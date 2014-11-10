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
import scala.collection.mutable.LinkedHashMap
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.Stack
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
  val flushedTexts = HashSet[String]()
  val componentStack = new Stack[Module]
  def curComponent = componentStack.top

  private def emitLit(x: BigInt, w: Int): String = {
    val unsigned = if (x < 0) (BigInt(1) << w) + x else x
    "0h" + w + "_" + unsigned.toString(16)
  }

  private def emitName(node: Node): String = {
    val tempPrefix = node match {
      case _: Reg => "R"
      case _ => "T"
    }
    if (node.name != "") node.name else tempPrefix + node.emitIndex
  }

  override def emitRef(node: Node): String = {
    node match {
      case lit: Literal => emitLit(lit.value, lit.needWidth())
      case _ =>
        if (node.component == this.curComponent)
          emitName(node)
        else
          node.component.name + "." + emitName(node)
    }
  }

  private def emitType(typ: Node): String = {
    /*val sType = "signed word [" + typ.needWidth + "]"
    val uType = "unsigned word [" + typ.needWidth + "]"
    val bType = "{TRUE, FALSE}"

    typ match {
      case _: SInt => sType
      case _: Bool => bType
      case _: Bits => uType
      case _: LogicalOp => bType
      case _: BinaryOp => emitType(typ.inputs(0))
      case _: UnaryOp => emitType(typ.inputs(0))
      case _: Mux => emitType(typ.inputs(1))
      case memread: MemRead => emitType(memread.mem.data)
      case lit: Literal => if (lit.signed) sType else uType
    }*/
    "unsigned word [" + typ.needWidth + "]"
  }

  private def emitComponent(sb: StringBuilder, mod: Module) {
    sb.append(mod.moduleName).append("(reset")
    for ((n, w) <- mod.wires) {
      if (n != "reset") {
        w match {
          case io: Bits =>
            if (io.dir == INPUT) {
              if (io.inputs.length == 0) {
                sb.append(", 0")
              } else if (io.inputs.length > 1) {
                ChiselError.warning("Too many connections to " + emitRef(io))
              } else {
                sb.append(", ").append(emitRef(io.inputs(0)))
              }
            }
        }
      }
    }
    sb.append(")")
  }

  private def emitVarDecls(
      sb: StringBuilder,
      regs: Iterable[Reg],
      mems: Iterable[Mem[_]],
      children: Iterable[Module]) {
    if (regs.size + mems.size + children.size > 0) {
      sb.append("VAR\n")
      for (reg <- regs) {
        sb.append("\t").append(emitName(reg))
          .append(" : ")
          .append(emitType(reg.next))
          .append(";\n")
      }
      for (mem <- mems) {
        sb.append("\t").append(emitName(mem))
          .append(" : array 0..").append(mem.n - 1)
          .append(" of ")
          .append(emitType(mem.data))
          .append(";\n")
      }

      for (mod <- children) {
        sb.append("\t").append(mod.name).append(" : ")
        emitComponent(sb, mod)
        sb.append(";\n")
      }
    }
  }

  private def emitUpdates(sb: StringBuilder, regs: Iterable[Reg]) {
    if (regs.size > 0) {
      sb.append("ASSIGN\n")

      for (reg <- regs) {
        sb.append("    next(").append(emitName(reg)).append(") := ")
          .append(emitRef(reg.next)).append(";\n")
      }
    }
  }

  private def emitBinaryOp(op: String, a: Node, b: Node) = {
    val (asigned, bsigned, realop) = op match {
      case "+" | "-" | "*" | "/" | "%" | "&" | "|" |
           "<" | ">" | "<=" | ">=" | "!=" => (false, false, op)
      case "==" => (false, false, "=")
      case "^" => (false, false, "xor")
      case "s<" => (true, true, "<")
      case "s<=" => (true, true, "<=")
      case "s>>" => (true, false, ">>")
      case "s*s" => (true, true, "*")
      case "s/s" => (true, true, "/")
      case "s%s" => (true, true, "%")
      case "s*u" => (true, false, "*")
      case "##" => (false, false, "::")
      case _ => {
        ChiselError.warning(s"Unmatched operator ${op}")
        (false, false, op)
      }
    }
    val aref = if (asigned) "signed(" + emitRef(a) + ")" else emitRef(a)
    val bref = if (bsigned) "signed(" + emitRef(b) + ")" else emitRef(b)

    aref + " " + realop + " " + bref
  }

  private def emitUnaryOp(op: String, x: Node):String = {
    val realop = op match {
      case "~" => op
    }
    realop + emitRef(x)
  }

  private def emitExtract(sb: StringBuilder, extract: Extract) {
    sb.append(emitRef(extract.inputs(0)))
      .append("[").append(emitRef(extract.inputs(1)))
      .append(":").append(emitRef(extract.inputs(2)))
      .append("]")
  }

  private def emitMux(sb: StringBuilder, sel: Node, a: Node, b: Node) {
    sb.append("case ").append(emitRef(sel))
      .append(" : ").append(emitRef(a))
      .append("; TRUE : ").append(emitRef(b))
      .append("; esac")
  }

  private def emitMemRead(sb: StringBuilder, memread: MemRead) {
    sb.append(emitName(memread.mem))
      .append("[")
      .append(emitRef(memread.inputs(0)))
      .append("]")
  }

  private def emitDefs(sb: StringBuilder, defs: Iterable[Node]) {
    if (defs.size > 0) {
      sb.append("DEFINE\n")
      for (node <- defs) {
        sb.append("\t").append(emitName(node)).append(" := ")
        node match {
          case op: BinaryOp =>
            sb.append(emitBinaryOp(op.op, op.inputs(0), op.inputs(1)))
          case op: LogicalOp =>
            sb.append(emitBinaryOp(op.op, op.inputs(0), op.inputs(1)))
          case op: UnaryOp =>
            sb.append(emitUnaryOp(op.op, op.inputs(0)))
          case mux: Mux =>
            emitMux(sb, mux.inputs(0), mux.inputs(1), mux.inputs(2))
          case extract: Extract =>
            emitExtract(sb, extract)
          case memread: MemRead =>
            emitMemRead(sb, memread)
          case bits: Bits =>
            sb.append(emitRef(bits.inputs(0)))
          case _ => {
            println(s"${node.name} ${node.getClass.getName}")
          }
        }
        sb.append(";\n")
      }
    }
  }

  private def emitModuleText(top: Module): String = {
    val sb = new StringBuilder()

    componentStack.push(top)

    val outputs = new ArrayBuffer[(String,Bits)]
    val inputs  = new ArrayBuffer[(String,Bits)]

    for ((n, w) <- top.wires) {
      if (w.dir == INPUT) {
        inputs += Tuple2(n, w)
      } else if (w.dir == OUTPUT) {
        outputs += Tuple2(n, w)
      }
    }

    val ports = (inputs.unzip._1 :+ "reset").toSet

    sb.append("(reset, ")
      .append(inputs.unzip._1.mkString(", "))
      .append(")\n")

    val regs = new ArrayBuffer[Reg]
    val mems = new ArrayBuffer[Mem[_]]
    val defs = new ArrayBuffer[Node]

    for (node <- top.nodes) {
      node match {
        case reg: Reg =>
          regs += reg
        case mem: Mem[_] =>
          mems += mem
        case lit: Literal => ()
        case _ => if (!ports.contains(node.name)) {
          defs += node
        }
      }
    }

    emitVarDecls(sb, regs, mems, top.children)
    emitUpdates(sb, regs)
    emitDefs(sb, defs)

    componentStack.pop()

    sb.toString
  }

  def flushModules( out: java.io.FileWriter,
    defs: LinkedHashMap[String, LinkedHashMap[String, ArrayBuffer[Module] ]],
    level: Int ) {
    for( (className, modules) <- defs ) {
      var index = 0
      for ( (text, comps) <- modules) {
        val moduleName = if( modules.size > 1 ) {
          className + "_" + index.toString;
        } else {
          className;
        }
        index = index + 1
        var textLevel = 0;
        for( flushComp <- comps ) {
          textLevel = flushComp.level;
          if( flushComp.level == level && flushComp.moduleName == "") {
            flushComp.moduleName = moduleName
          }
        }
        if( textLevel == level ) {
          /* XXX We write the module source text in *emitChildren* instead
                 of here so as to generate a minimal "diff -u" with the previous
                 implementation. */
        }
      }
    }
  }


  def emitChildren(top: Module,
    defs: LinkedHashMap[String, LinkedHashMap[String, ArrayBuffer[Module] ]],
    out: java.io.FileWriter, depth: Int) {
    if (top.isInstanceOf[BlackBox])
      return

    for (child <- top.children) {
      emitChildren(child, defs, out, depth + 1);
    }
    val className = extractClassName(top);
    for( (text, comps) <- defs(className)) {
      if( comps contains top ) {
        if( !(flushedTexts contains text) ) {
          out.append("MODULE ")
          out.append(top.moduleName)
          out.append(text)
          out.append("\n")
          flushedTexts += text
        }
        return;
      }
    }
  }

  def emitMainModule(top: Module): String = {
    val sb = new StringBuilder()
    sb.append("MODULE main\nVAR\n\treset : {0, 1};\n")

    for ((n, w) <- top.wires) {
      if (w.dir == INPUT) {
        sb.append("\t").append(w.name).append(" : ")
          .append(emitType(w)).append(";\n")
      }
    }

    sb.toString()
  }

  def doCompile(top: Module, out: java.io.FileWriter, depth: Int): Unit = {
    /* *defs* maps Mod classes to Mod instances through
       the generated text of their module.
       We use a LinkedHashMap such that later iteration is predictable. */
    val defs = LinkedHashMap[String, LinkedHashMap[String, ArrayBuffer[Module]]]()
    var level = 0;
    for (c <- Driver.sortedComps) {
      ChiselError.info(depthString(depth) + "COMPILING " + c
        + " " + c.children.length + " CHILDREN"
        + " (" + c.level + "," + c.traversal + ")");
      ChiselError.checkpoint()

      if( c.level > level ) {
        /* When a component instance instantiates different sets
         of sub-components based on its constructor parameters, the same
         Module class might appear with different level in the tree.
         We thus wait until the very end to generate module names.
         If that were not the case, we could flush modules as soon as
         the source text for all components at a certain level in the tree
         has been generated. */
        flushModules(out, defs, level);
        level = c.level
      }
      val res = emitModuleText(c);
      val className = extractClassName(c);
      if( !(defs contains className) ) {
        defs += (className -> LinkedHashMap[String, ArrayBuffer[Module] ]());
      }
      if( defs(className) contains res ) {
        /* We have already outputed the exact same source text */
        defs(className)(res) += c;
        ChiselError.info("\t" + defs(className)(res).length + " components");
      } else {
        defs(className) += (res -> ArrayBuffer[Module](c));
      }
    }
    flushModules(out, defs, level);
    emitChildren(top, defs, out, depth);
    out.append(emitMainModule(top))
  }

  override def elaborate(c: Module) {
    super.elaborate(c)

    val out = createOutputFile(c.name + ".smv")
    doCompile(c, out, 0)
    out.close()
  }
}
