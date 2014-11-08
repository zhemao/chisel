/*
 Copyright (c) 2011", "2012", "2013", "2014 The Regents of the University of
 California (Regents). All Rights Reserved.  Redistribution and use in
 source and binary forms", "with or without modification", "are permitted
 provided that the following conditions are met:

    * Redistributions of source code must retain the above
      copyright notice", "this list of conditions and the following
      two paragraphs of disclaimer.
    * Redistributions in binary form must reproduce the above
      copyright notice", "this list of conditions and the following
      two paragraphs of disclaimer in the documentation and/or other materials
      provided with the distribution.
    * Neither the name of the Regents nor the names of its contributors
      may be used to endorse or promote products derived from this
      software without specific prior written permission.

 IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT", "INDIRECT",
 SPECIAL", "INCIDENTAL", "OR CONSEQUENTIAL DAMAGES", "INCLUDING LOST PROFITS",
 ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION", "EVEN IF
 REGENTS HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

 REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES", "INCLUDING", "BUT NOT
 LIMITED TO", "THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 A PARTICULAR PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION", "IF
 ANY", "PROVIDED HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION
 TO PROVIDE MAINTENANCE", "SUPPORT", "UPDATES", "ENHANCEMENTS", "OR
 MODIFICATIONS.
*/

package Chisel
import Node._
import java.io.File;
import java.io.InputStream
import java.io.OutputStream
import java.io.PrintStream
import scala.sys.process._
import Reg._
import ChiselError._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.mutable.StringBuilder

class NuSMVBackend extends Backend {
  val keywords = HashSet("MODULE", "DEFINE", "MDEFINE", "CONSTANTS", "VAR",
    "IVAR", "FROZENVAR", "INIT", "TRANS", "INVAR", "SPEC", "CTLSPEC",
    "LTLSPEC", "PSLSPEC", "COMPUTE", "NAME", "INVARSPEC", "FAIRNESS",
    "JUSTICE", "COMPASSION", "ISA", "ASSIGN", "CONSTRAINT", "SIMPWFF",
    "CTLWFF", "LTLWFF", "PSLWFF", "COMPWFF", "IN", "MIN", "MAX", "MIRROR",
    "PRED", "PREDICATES", "process", "array", "of", "boolean", "integer",
    "real", "word", "word1", "bool", "signed", "unsigned", "extend", "resize",
    "sizeof", "uwconst", "swconst", "EX", "AX", "EF", "AF", "EG", "AG", "E",
    "F", "O", "G", "H", "X", "Y", "Z", "A", "U", "S", "V", "T", "BU", "EBF",
    "ABF", "EBG", "ABG", "case", "esac", "mod", "next", "init", "union", "in",
    "xor", "xnor", "self", "TRUE", "FALSE", "count")

  override val needsLowering = Set("PriEnc", "OHToUInt", "Log2")
  override def isEmittingComponents: Boolean = true

  private def emitLit(x: BigInt, w: Int): String = {
    val unsigned = if (x < 0) (BigInt(1) << w) + x else x
    "0h" + w + "_" + unsigned.toString(16)
  }

  override def emitRef(node: Node): String = {
    node match {
      case lit: Literal => emitLit(lit.value, lit.needWidth())
      case _ => node.name
    }
  }

  private def emitVarDecls(sb: StringBuilder, regs: Iterable[Reg]) {
    sb.append("VAR\n")
    for (reg <- regs) {
      val typname = reg.next match {
        case sint: SInt => "signed word"
        case _ => "unsigned word"
      }
      val width = reg.next.needWidth
      sb.append("\t").append(reg.name).append(" : ")
        .append(typname).append("[")
        .append(reg.next.needWidth)
        .append("];\n")
    }
  }

  private def emitUpdates(sb: StringBuilder, regs: Iterable[Reg]) {
    sb.append("ASSIGN\n")

    for (reg <- regs) {
      sb.append("\tnext(").append(reg.name).append(") := ")
        .append(emitRef(reg.next)).append(";\n")
    }
  }

  private def emitOp(sb: StringBuilder, op: Op) {
    op.op match {
      case "+" | "*" | "&" | "|" =>
        sb.append(emitRef(op.inputs(0)))
          .append(" ").append(op.op).append(" ")
          .append(emitRef(op.inputs(1)))
      case "##" => {
        val sw = op.inputs(1).needWidth
        sb.append("(").append(emitRef(op.inputs(0))).append(" << ")
          .append(sw).append(") | ").append(emitRef(op.inputs(1)))
      }
      case "Mux" => {
        val ref1 = emitRef(op.inputs(1))
        val ref2 = emitRef(op.inputs(2))
        sb.append("case ").append(emitRef(op.inputs(0)))
          .append(" : ").append(emitRef(op.inputs(1)))
          .append("; TRUE : ").append(emitRef(op.inputs(2)))
          .append("; esac")
      }
      case s => println(s"Unmatched op: ${op.name} ${s}")
    }
  }

  private def emitExtract(sb: StringBuilder, extract: Extract) {
    val gotWidth = extract.inputs(0).needWidth()
    if (gotWidth > 1) {
      if (extract.inputs.length < 3) {
        sb.append("(").append(emitRef(extract.inputs(0)))
          .append(" >> ").append(emitRef(extract.inputs(1)))
          .append(") & 1")
      } else {
        val hi = emitRef(extract.inputs(1))
        val lo = emitRef(extract.inputs(2))
        sb.append("(").append(emitRef(extract.inputs(0)))
          .append(" >> ").append(lo)
          .append(") & ((1 << (").append(hi).append(" - ").append(lo)
          .append(" + 1)) - 1)")
      }
    } else {
      sb.append(emitRef(extract.inputs(0)))
    }
  }

  private def emitDefs(sb: StringBuilder, defs: Iterable[Node]) {
    sb.append("DEFINE\n")
    for (node <- defs) {
      sb.append("\t").append(node.name).append(" := ")
      node match {
        case op: Op => {
          emitOp(sb, op)
        }
        case extract: Extract => {
          emitExtract(sb, extract)
        }
        case _ => {
          println(s"${node.name} ${node.getClass.getName}")
          if (node.inputs.length == 1) {
            sb.append(emitRef(node.inputs(0)))
          }
        }
      }
      sb.append(";\n")
    }
  }

  private def emitModule(top: Module): StringBuilder = {
    val outputs = new ArrayBuffer[(String,Bits)]
    val inputs  = new ArrayBuffer[(String,Bits)]
    val sb = new StringBuilder()

    for ((n, w) <- top.wires) {
      if (w.dir == INPUT) {
        inputs += Tuple2(n, w)
      } else if (w.dir == OUTPUT) {
        outputs += Tuple2(n, w)
      }
    }

    val ports = (outputs.unzip._1 ++ inputs.unzip._1 :+ "reset").toSet

    val moduleName = top.getClass.getSimpleName

    sb.append("MODULE ").append(moduleName).append("(reset, ")
      .append(inputs.unzip._1.mkString(", ")).append(")\n")

    val regs = new ArrayBuffer[Reg]
    val mwrites = new ArrayBuffer[MemWrite]
    val defs = new ArrayBuffer[Node]

    for (node <- top.nodes) {
      node match {
        case reg: Reg =>
          regs += reg
        case m: MemWrite =>
          mwrites += m
        case lit: Literal => ()
        case _ => if (!ports.contains(node.name)) {
          defs += node
        }
      }
    }

    emitVarDecls(sb, regs)
    emitUpdates(sb, regs)
    emitDefs(sb, defs)

    sb
  }

  override def elaborate(c: Module) {
    super.elaborate(c)

    val out = createOutputFile(c.name + ".smv")
    val sb = emitModule(c)
    out.write(sb.toString)
    out.flush()
    out.close()
  }
}
