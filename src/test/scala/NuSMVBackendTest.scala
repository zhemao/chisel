import Chisel._
import org.junit.Test

class NuSMVBackendSuite extends TestSuite {
  @Test def testSimple() {
    class SimpleExample extends Module {
      val io = new Bundle {
        val a = UInt(INPUT, width = 5)
        val b = SInt(OUTPUT, width = 6)
      }

      val x = Reg(next = io.a)
      val y = Reg(init = SInt(0, 5))
      val z = Reg(SInt(width = 6))

      y := y + UInt(1)
      z := x | y
      io.b := z
    }

    chiselMain(Array(
      "--backend", "nusmv",
      "--targetDir", dir.getPath.toString()),
    () => Module(new SimpleExample))
    assertFile("NuSMVBackendSuite_SimpleExample_1.smv")
  }
}
