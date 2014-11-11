package Chisel

import scala.collection.mutable.HashMap
import scala.collection.mutable.StringBuilder
import scala.collection.mutable.ArrayBuffer

class ModelChecker[T <: Module](val c: T) extends FileSystemUtilities {
  private var curCycle = 0
  private val pokeMap = new HashMap[String, HashMap[Int, BigInt]]
  private val widthMap = new HashMap[String, Int]
  private val ctlSpecs = new ArrayBuffer[String]

  private def emitLit(x: BigInt, w: Int): String = {
    val unsigned = if (x < 0) (BigInt(1) << w) + x else x
    "0h" + w + "_" + unsigned.toString(16)
  }

  def step(cycles: Int = 1) {
    curCycle += cycles
  }

  def poke(bits: Bits, num: BigInt) {
    if (!pokeMap.contains(bits.name)) {
      pokeMap(bits.name) = HashMap((curCycle, num))
      widthMap(bits.name) = bits.width
    } else {
      pokeMap(bits.name)(curCycle) = num
    }
  }

  def spec(ctl: String) {
    ctlSpecs += ctl
  }

  def emit() {
    val sb = new StringBuilder
    val lastCycle = curCycle + 1

    sb.append("    cycle : 0..").append(lastCycle).append(";\n")
      .append("ASSIGN\n")
      .append("    init(cycle) := 0;\n")
      .append("    next(cycle) := case\n")
      .append("        cycle < ").append(lastCycle).append(" : cycle + 1;\n")
      .append("        TRUE : cycle;\n")
      .append("    esac;\n")

    for ((signalName, pokes) <- pokeMap) {
      val width = widthMap(signalName)

      sb.append("    next(").append(signalName).append(") := ")
        .append("case\n")

      for ((cycle, num) <- pokes) {
        sb.append("        cycle = ")
          .append(cycle).append(" : ")
          .append(emitLit(num, width))
          .append(";\n")
      }
      sb.append("        TRUE : ").append(signalName)
        .append(";\n    esac;\n")
    }

    for (ctl <- ctlSpecs) {
      sb.append("SPEC ").append(ctl).append(";\n")
    }

    val owriter = appendOutputFile(c.name + ".smv")
    owriter.append(sb)
    owriter.close()
  }
}
