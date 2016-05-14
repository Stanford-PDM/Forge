import dhdl.compiler._
import dhdl.library._
import dhdl.shared._

object TestCompiler extends DHDLApplicationCompiler with Test
object TestInterpreter extends DHDLApplicationInterpreter with Test
trait Test extends DHDLApplication {

  def main() {
    type Q16 = FixPt[Signed, B16, B16]

    val v1    = OffChipMem[Q16]("v1", 10)
    val v2    = OffChipMem[Q16]("v2", 10)
    val outer = ArgOut[Q16]

    val vec1 = Array.fill(10)(random[Q16](10))
    val vec2 = Array.fill(10)(random[Q16](10))
    setMem(v1, vec1)
    setMem(v2, vec2)

    Accel {
      val b1 = BRAM[Q16]("b1", 5)
      val b2 = BRAM[Q16]("b2", 5)

      Pipe.fold(10 by 5)(outer){i =>
        b1 := v1(i::i+5)
        b2 := v2(i::i+5)
        val inner = Reg[Q16]
        Pipe.reduce(0 until 5)(inner){ii => b1(ii) * b2(ii) }{_+_}
      }{_+_}

      ()
    }

    val gold = vec1.map{_**2}.reduce{_+_}
    println("outer: " + getArg(outer).mkString + " (should be " + gold.mkString + ")")
  }
}
