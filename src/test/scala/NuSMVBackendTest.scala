import Chisel._
import org.junit.Test

class NuSMVBackendSuite extends TestSuite {
  @Test def testSimple() {
    class SimpleExample extends Module {
      val io = new Bundle {
        val a = UInt(INPUT, width = 5)
        val b = SInt(OUTPUT, width = 6)
        val c = Bool(OUTPUT)
        val d = Bool(OUTPUT)
      }

      val x = Reg(next = io.a)
      val y = Reg(init = SInt(0, 5))
      val z = Reg(SInt(width = 6))

      y := y + UInt(1)
      z := x | y
      io.b := z

      val w = Reg(init = Bool(false))
      w := !w
      io.c := w

      io.d := y > x
    }

    chiselMain(Array(
      "--backend", "nusmv",
      "--targetDir", dir.getPath.toString()),
    () => Module(new SimpleExample))
    assertFile("NuSMVBackendSuite_SimpleExample_1.smv")
  }

  @Test def testMemory() {
    class MemoryExample extends Module {
      val io = new Bundle {
        val readAddr = UInt(INPUT, 2)
        val readData = UInt(OUTPUT, 8)
      }

      val readAddrReg = Reg(next = io.readAddr)
      val mem = Mem(UInt(width = 8), 4)

      io.readData := mem(readAddrReg)
    }

    chiselMain(Array(
      "--backend", "nusmv",
      "--targetDir", dir.getPath.toString()),
    () => Module(new MemoryExample))
    assertFile("NuSMVBackendSuite_MemoryExample_1.smv")
  }
}
