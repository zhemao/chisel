import Chisel._
import org.junit.Test

class NuSMVBackendSuite extends TestSuite {
  val nusmvArgs = Array(
      "--backend", "nusmv",
      "--targetDir", dir.getPath.toString())

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

    chiselMain(nusmvArgs, () => Module(new SimpleExample))
    assertFile("NuSMVBackendSuite_SimpleExample_1.smv")
  }

  @Test def testMemory() {
    class MemoryExample extends Module {
      val io = new Bundle {
        val readAddr = UInt(INPUT, 2)
        val readData = UInt(OUTPUT, 8)

        val writeAddr = UInt(INPUT, 2)
        val writeData = UInt(INPUT, 8)
        val writeEn = Bool(INPUT)
      }

      val readAddrReg = Reg(next = io.readAddr)
      val mem = Mem(UInt(width = 8), 4)

      io.readData := mem(readAddrReg)

      when (io.writeEn) {
        mem(io.writeAddr) := io.writeData
      }
    }

    class MemoryChecker(c: MemoryExample) extends ModelChecker(c) {
      poke(c.io.writeAddr, 1)
      poke(c.io.writeData, 2)
      poke(c.io.writeEn, 1)
      step(1)
      poke(c.io.writeEn, 0)
      step(1)
      poke(c.io.readAddr, 1)

      spec("AF (toint(io_readAddr) = 1 & toint(top.io_readData) = 2)")
    }

    chiselMain.modelCheck(nusmvArgs,
      () => Module(new MemoryExample),
      (c: MemoryExample) => new MemoryChecker(c))
    assertFile("NuSMVBackendSuite_MemoryExample_1.smv")
  }

  @Test def testSubmodule() {
    class Child extends Module {
      val io = new Bundle {
        val cin = Bool(INPUT)
        val cout = Bool(OUTPUT)
      }

      io.cout := !io.cin
    }
    class Parent extends Module {
      val NumChildren = 2

      val io = new Bundle {
        val pin = Bits(INPUT, NumChildren)
        val pout = Bits(OUTPUT, NumChildren)
      }

      val couts = Vec.fill(NumChildren) { Bool() }

      for (i <- 0 until NumChildren) {
        val child = Module(new Child)
        child.io.cin := io.pin(i)
        couts(i) := child.io.cout
      }

      io.pout := couts.toBits
    }

    chiselMain(nusmvArgs, () => Module(new Parent))
    assertFile("NuSMVBackendSuite_Parent_1.smv")
  }

  @Test def testGCD() {
    class GCD(w: Int) extends Module {
      val io = new Bundle {
        val a = UInt(INPUT, w)
        val b = UInt(INPUT, w)
        val c = UInt(OUTPUT, w)
        val start = Bool(INPUT)
        val done = Bool(OUTPUT)
      }

      val x = Reg(UInt(width = w))
      val y = Reg(UInt(width = w))

      when (io.start) {
        x := io.a
        y := io.b
      } .elsewhen (x > y) {
        x := x - y
      } .elsewhen (y > x) {
        y := y - x
      }

      io.done := (x === y)
      io.c := x
    }

    class GCDChecker(c: GCD) extends ModelChecker(c) {
      poke(c.io.start, 1)
      poke(c.io.a, 6)
      poke(c.io.b, 4)
      step(1)
      poke(c.io.start, 0)

      spec("AF (top.io_c = 0ud16_2)")
    }

    chiselMain.modelCheck(nusmvArgs,
      () => Module(new GCD(16)),
      (c: GCD) => new GCDChecker(c))
    assertFile("NuSMVBackendSuite_GCD_1.smv")
  }

  @Test def testROM {
    class ROMExample extends Module {
      val io = new Bundle {
        val readAddr = UInt(INPUT, 3)
        val readData = UInt(OUTPUT, 8)
      }

      val rom = Vec.tabulate(8)(i => UInt(i << 2, 8))
      io.readData := rom(io.readAddr)
    }

    class ROMChecker(c: ROMExample) extends ModelChecker(c) {
      for (i <- 0 until 8) {
        poke(c.io.readAddr, i)
        step(1)
      }

      spec("AG ((toint(io_readAddr) = 1) -> (toint(top.io_readData) = 4))")
    }

    chiselMain.modelCheck(nusmvArgs,
      () => Module(new ROMExample),
      (c: ROMExample) => new ROMChecker(c))
    assertFile("NuSMVBackendSuite_ROMExample_1.smv")
  }
}
