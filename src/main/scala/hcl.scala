/*
 Copyright (c) 2011, 2012, 2013, 2014 The Regents of the University of
 California (Regents). All Rights Reserved.  Redistribution and use in
 source and binary forms, with or without modification, are permitted
 provided that the following conditions are met:

    * Redistributions of source code must retain the above
      copyright notice, this list of conditions and the following
      two paragraphs of disclaimer.
    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      two paragraphs of disclaimer in the documentation and/or other materials
      provided with the distribution.
    * Neither the name of the Regents nor the names of its contributors
      may be used to endorse or promote products derived from this
      software without specific prior written permission.

 IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT,
 SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS,
 ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF
 REGENTS HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

 REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT
 LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 A PARTICULAR PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF
 ANY, PROVIDED HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION
 TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
 MODIFICATIONS.
*/

package Chisel
import ChiselError._

class TestIO(val format: String, val args: Seq[Data] = null)

object Scanner {
  def apply (format: String, args: Data*): TestIO =
    new TestIO(format, args.toList);
}
object Printer {
  def apply (format: String, args: Data*): TestIO =
    new TestIO(format, args.toList);
}

/**
  _chiselMain_ behaves as if it constructs an execution tree from
  the constructor of a sub class of Module which is passed as a parameter.
  That execution tree is simplified by aggregating all calls which are not
  constructors of a Module instance into the parent which is.
  The simplified tree (encoded through _Driver.children_) forms the basis
  of the generated verilog. Each node in the simplified execution tree is
  a _Module_ instance from which a verilog module is textually derived.
  As an optimization, _Backend_ classes output modules which are
  textually equivalent only once and update a _Module_ instance's
  _moduleName_ accordingly.
*/
object chiselMain {
  def apply[T <: Module](args: Array[String], gen: () => T): T =
    Driver(args, gen)

  def apply[T <: Module](args: Array[String], gen: () => T, ftester: T => Tester[T]): T =
    Driver(args, gen, ftester)

  // Assumes gen needs to be wrapped in Module()
  def run[T <: Module] (args: Array[String], gen: () => T): T =
    Driver(args, gen, false)

  def run[T <: Module] (args: Array[String], gen: () => T, ftester: T => Tester[T]): T =
    Driver(args, gen, ftester, false)

  def modelCheck[T <: Module](args: Array[String], gen: () => T, mchecker: T => ModelChecker[T]): T =
    Driver.modelCheck(args, gen, mchecker)
}

//Is this antiquated?
object chiselMainTest {
  def apply[T <: Module](args: Array[String], gen: () => T)(tester: T => Tester[T]): T =
    chiselMain(args, gen, tester)
}

class ChiselException(message: String, cause: Throwable) extends Exception(message, cause)

object throwException {
  def apply(s: String, t: Throwable = null) = {
    val xcpt = new ChiselException(s, t)
    findFirstUserLine(xcpt.getStackTrace) foreach { u => xcpt.setStackTrace(Array(u)) }
    throw xcpt
  }
}


trait proc extends Node {
  protected var procAssigned = false

  protected[Chisel] def verifyMuxes: Unit = {
    if (!defaultRequired && (inputs.length == 0 || inputs(0) == null))
      ChiselError.error({"NO UPDATES ON " + this}, this.line)
    if (defaultRequired && defaultMissing)
      ChiselError.error({"NO DEFAULT SPECIFIED FOR WIRE: " + this + " in component " + this.component.getClass}, this.line)
  }

  protected[Chisel] def doProcAssign(src: Node, cond: Bool): Unit = {
    if (cond.canBeUsedAsDefault && defaultMissing) {
      setDefault(src)
    } else if (procAssigned) {
      inputs(0) = Multiplex(cond, src, inputs(0))
    } else if (cond.litValue() != 0) {
      procAssigned = true
      val mux = Multiplex(cond, src, default)
      if (inputs.isEmpty) inputs += mux
      else { require(inputs(0) == default); inputs(0) = mux }
    }
  }

  protected[Chisel] def procAssign(src: Node): Unit =
    doProcAssign(src, Module.current.whenCond)

  protected[Chisel] def muxes: Seq[Mux] = {
    def traverse(x: Node): List[Mux] = x match {
      case m: Mux => m :: (if (m.inputs(2) eq default) Nil else traverse(m.inputs(2)))
      case _ => Nil
    }
    traverse(inputs(0))
  }

  protected[Chisel] def next: Node = {
    val node = getNode
    if (node.inputs.isEmpty) null else node.inputs(0)
  }
  protected def default = if (defaultRequired) null else this
  protected def defaultRequired: Boolean = false
  protected def defaultMissing: Boolean =
    procAssigned && inputs(0).isInstanceOf[Mux] && (muxes.last.inputs(2) eq default)
  protected def setDefault(src: Node): Unit = muxes.last.inputs(2) = src
}

trait nameable {
  var name: String = ""
  /** _named_ is used to indicates name was set explicitely
   and should not be overriden by a _nameIt_ generator. */
  var named = false
}

abstract class BlackBox extends Module {
  Driver.blackboxes += this

  def setVerilogParameters(string: String) {
    this.asInstanceOf[Module].verilog_parameters = string;
  }

  def setName(name: String) {
    moduleName = name;
  }
}


class Delay extends Node {
  override def isReg: Boolean = true
  def assignReset(rst: => Bool): Boolean = false
  def assignClock(clk: Clock): Unit = { clock = clk }
}

