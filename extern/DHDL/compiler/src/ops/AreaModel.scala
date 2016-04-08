package dhdl.compiler.ops

import scala.reflect.{Manifest,SourceContext}

import dhdl.shared._
import dhdl.shared.ops._
import dhdl.compiler._
import dhdl.compiler.ops._

// Struct for passing around completed FPGA area analysis results
case class FPGAResourceSummary(
  alms: Int = 0,
  regs: Int = 0,
  dsps: Int = 0,
  bram: Int = 0
)

// Class for operating on intermediate FPGA resource counts
case class FPGAResources(
  lut7: Int = 0,
  lut6: Int = 0,
  lut5: Int = 0,
  lut4: Int = 0,
  lut3: Int = 0,
  mem64: Int = 0,
  mem32: Int = 0,
  mem16: Int = 0,
  regs: Int = 0,
  dsps: Int = 0,
  bram: Int = 0
) {
  def +(that: FPGAResources) = FPGAResources(
    lut7 = this.lut7 + that.lut7,
    lut6 = this.lut6 + that.lut6,
    lut5 = this.lut5 + that.lut5,
    lut4 = this.lut4 + that.lut4,
    lut3 = this.lut3 + that.lut3,
    mem64 = this.mem64 + that.mem64,
    mem32 = this.mem32 + that.mem32,
    mem16 = this.mem16 + that.mem16,
    regs = this.regs + that.regs,
    dsps = this.dsps + that.dsps,
    bram = this.bram + that.bram
  )
  def *(a: Int) = FPGAResources(a*lut7,a*lut6,a*lut5,a*lut4,a*lut3,a*mem64,a*mem32,a*mem16,
                                a*regs,a*dsps,a*bram)

  def isNonzero: Boolean = lut7 > 0 || lut6 > 0 || lut5 > 0 || lut4 > 0 || lut3 > 0 ||
                           mem64 > 0 || mem32 > 0 || mem16 > 0 || regs > 0 || dsps > 0 || bram > 0

  override def toString() = s"luts=$lut3,$lut4,$lut5,$lut6,$lut7,mems=$mem16,$mem32,$mem64,regs=$regs,dsps=$dsps,bram=$bram"
}

object NoArea extends FPGAResources()


// TODO: Should get some of this from loading a file rather than hardcoding
// All numbers here are from Stratix V profiling
trait AreaModel {
  this: DHDLExp with CounterToolsExp =>

  private var silentModel = false
  private def warn(x: String) { if (!silentModel) stageWarn(x) }
  def silenceAreaModel() { silentModel = true }

  /**
   * Returns the area resources for a delay line with the given width (in bits) and length (in cycles)
   * Models delays as registers for short delays, BRAM for long ones
   **/
  def areaOfDelayLine(width: Int, length: Int): FPGAResources = {
    // TODO: Not sure what the cutoff is here
    if (length < 32) FPGAResources(regs = width*length)
    else             areaOfBRAM(width, length, 1, false)
  }
  def areaOfDelayLine(width: Int, length: Long): FPGAResources = {
    if(length > Int.MaxValue) throw new Exception(s"Casting delay line length to Int would result in overflow")
    areaOfDelayLine(width, length.toInt)
  }

  private def areaOfMemWord(nbits: Int) = {
    val m64 = nbits/64
    val m32 = (nbits - m64*64)/32
    val m16 = (nbits - m64*64 - m32*32)/16
    FPGAResources(mem64=m64, mem32=m32, mem16=m16)
  }

  private def areaOfArg(nbits: Int) = FPGAResources(regs=3*nbits/2)

  /**
   * Area resources required for a BRAM with word size nbits, and with given depth,
   * number of banks, and double buffering
   **/
  private def areaOfBRAM(nbits: Int, depth: Int, banks: Int, dblBuf: Boolean) = {
    // Physical depth for given word size for horizontally concatenated RAMs
    val wordDepth = if      (nbits == 1)  16384
                    else if (nbits == 2)  8192
                    else if (nbits <= 5)  4096
                    else if (nbits <= 10) 2048
                    else if (nbits <= 20) 1024
                    else                  512

    // Number of horizontally concatenated RAMs required to implement given word
    val width = if (nbits > 40) Math.ceil( nbits / 40.0 ).toInt else 1
    val rams = width * Math.ceil(depth.toDouble/(wordDepth*banks)).toInt * banks

    if (dblBuf) FPGAResources(lut3=2*nbits, regs=2*nbits, bram = rams*2)
    else        FPGAResources(bram = rams)
  }

  def areaOfMetapipe(n: Int) = FPGAResources(
    lut4 = (11*n*n + 45*n)/2 + 105,  // 0.5(11n^2 + 45n) + 105
    regs = (n*n + 3*n)/2 + 35        // 0.5(n^2 + 3n) + 35
  )
  def areaOfSequential(n: Int) = FPGAResources(lut4=7*n+40, regs=2*n+35)


  def areaOf(e: Exp[Any], inReduce: Boolean, inHwScope: Boolean) = e match {
    case Def(d) if !inHwScope => areaOfNodeOutOfScope(e, d)
    case Def(d) if inReduce  => areaOfNodeInReduce(e, d)
    case Def(d) if !inReduce => areaOfNode(e, d)
    case _ => NoArea  // Bound args and constants accounted for elsewhere
  }


  private def areaOfNodeOutOfScope(s: Exp[Any], d: Def[Any]): FPGAResources = d match {
    case _:Reg_new[_] if regType(s) != Regular => areaOfNode(s, d)
    case _ => NoArea
  }

  /**
   * Returns the area resources for the given node when specialized for tight update cycles
   * Accumulator calculation+update is often generated as a special case to minimize latencies in tight cycles
   **/
  private def areaOfNodeInReduce(s: Exp[Any], d: Def[Any]): FPGAResources = d match {
    case _ => areaOfNode(s, d)
  }


  /**
   * Returns the area resources for the given node
   **/
  private def areaOfNode(s: Exp[Any], d: Def[Any]): FPGAResources = d match {
    case ConstBit(_) => FPGAResources(lut3=1,regs=1)
    case ConstFix(_) => areaOfMemWord(nbits(s))
    case ConstFlt(_) => areaOfMemWord(nbits(s))

    case Reg_new(_) if regType(s) == ArgumentIn  => areaOfArg(nbits(s))
    case Reg_new(_) if regType(s) == ArgumentOut => areaOfArg(nbits(s))

    case Reg_new(_) if regType(s) == Regular =>
      if (isDblBuf(s)) FPGAResources(lut3 = nbits(s), regs = 4*nbits(s)) // TODO: Why 4?
      else             FPGAResources(regs = nbits(s))

    case e@Bram_new(depth, _) => areaOfBRAM(nbits(e._mT), depth, banks(s), isDblBuf(s))

    // TODO: These are close but still need some refining
    case e@Bram_load(ram, _) =>
      val decode = if (isPow2(banks(ram))) 0 else Math.ceil(Math.log(banks(ram))).toInt
      val bits = nbits(e._mT)
      FPGAResources(lut3=decode+bits, regs=decode+bits)

    case e@Bram_store(ram, _, _) =>
      val decode = if (isPow2(banks(ram))) 0 else Math.ceil(Math.log(banks(ram))).toInt
      val bits = nbits(e._mT)
      FPGAResources(lut3=decode+bits, regs=decode+bits)

    // TODO: Seems high, confirm
    case _:Counter_new => FPGAResources(lut3=106,regs=67)
    case _:Counterchain_new => NoArea

    // TODO: Have to get numbers for non-32 bit multiplies and divides
    case DHDLPrim_Neg_fix(_)   => FPGAResources(lut3 = nbits(s), regs = nbits(s))
    case DHDLPrim_Add_fix(_,_) => FPGAResources(lut3 = nbits(s), regs = nbits(s))
    case DHDLPrim_Sub_fix(_,_) => FPGAResources(lut3 = nbits(s), regs = nbits(s))
    case DHDLPrim_Mul_fix(_,_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(dsps = 2)

    case DHDLPrim_Div_fix(_,_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      if (sign(s)) FPGAResources(lut3=1192,lut5=2,regs=2700)
      else         FPGAResources(lut3=1317,lut5=6,regs=2900)

    case DHDLPrim_Mod_fix(_,_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      if (sign(s)) FPGAResources(lut3=1192,lut5=2,regs=2700)
      else         FPGAResources(lut3=1317,lut5=6,regs=2900)

    case DHDLPrim_Lt_fix(_,_)  => FPGAResources(lut4=nbits(s), regs=nbits(s))
    case DHDLPrim_Leq_fix(_,_) => FPGAResources(lut4=nbits(s), regs=nbits(s))
    case DHDLPrim_Neq_fix(_,_) => FPGAResources(lut4=nbits(s)/2, lut5=nbits(s)/8, regs=nbits(s))
    case DHDLPrim_Eql_fix(_,_) => FPGAResources(lut4=nbits(s)/2, lut5=nbits(s)/8, regs=nbits(s))
    case DHDLPrim_And_fix(_,_) => FPGAResources(lut3=nbits(s), regs=nbits(s))
    case DHDLPrim_Or_fix(_,_)  => FPGAResources(lut3=nbits(s), regs=nbits(s))

    //case DHDLPrim_Lsh_fix(_,_) => // ??? nbits(s)*nbits(s) ?
    //case DHDLPrim_Rsh_fix(_,_) => // ???

    // TODO: Floating point for things besides single precision
    case DHDLPrim_Neg_flt(_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut3=397,lut4=29,lut5=125,lut6=34,lut7=5,regs=606,mem16=50)

    case DHDLPrim_Add_flt(_,_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut3=397,lut4=29,lut5=125,lut6=34,lut7=5,regs=606,mem16=50)

    case DHDLPrim_Sub_flt(_,_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut3=397,lut4=29,lut5=125,lut6=34,lut7=5,regs=606,mem16=50)

    case DHDLPrim_Mul_flt(_,_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut3=152,lut4=10,lut5=21,lut6=2,dsps=1,regs=335,mem16=43)

    case DHDLPrim_Div_flt(_,_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut3=2384,lut4=448,lut5=149,lut6=385,lut7=1,regs=3048,mem32=25,mem16=9)

    case DHDLPrim_Lt_flt(_,_)  =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut4=42,lut6=26,regs=33)

    case DHDLPrim_Leq_flt(_,_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut4=42,lut6=26,regs=33)

    case DHDLPrim_Neq_flt(_,_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut4=42,lut6=26,regs=33)

    case DHDLPrim_Eql_flt(_,_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut4=42,lut6=26,regs=33)


    case DHDLPrim_Not_bit(_)   => FPGAResources(lut3=1,regs=1)
    case DHDLPrim_And_bit(_,_) => FPGAResources(lut3=1,regs=1)
    case DHDLPrim_Or_bit(_,_)  => FPGAResources(lut3=1,regs=1)
    case DHDLPrim_Xor_bit(_,_)  => FPGAResources(lut3=1,regs=1)
    case DHDLPrim_Xnor_bit(_,_)  => FPGAResources(lut3=1,regs=1)

    case DHDLPrim_Abs_fix(_) => FPGAResources(lut3=nbits(s),regs=nbits(s))
    case DHDLPrim_Abs_flt(_) => FPGAResources(regs=nbits(s)-1)
    case DHDLPrim_Log_flt(_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut3=472,lut4=47,lut5=74,lut6=26,lut7=3,mem16=42,regs=950,dsps=7,bram=3)

    case DHDLPrim_Exp_flt(_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut3=368,lut4=102,lut5=137,lut6=38,mem16=24,regs=670,dsps=5,bram=2)

    case DHDLPrim_Sqrt_flt(_) =>
      if (nbits(s) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut3=476,lut4=6,lut5=6,mem32=11,regs=900)

    case BasicCtrl1_Mux(_,_,_) => FPGAResources(regs = nbits(s))

    case Convert_fixpt(_) => FPGAResources(regs=nbits(s))
    //case Convert_fltpt(_) => // ???
    case Fixpt_to_fltpt(x) =>
      if (nbits(s) != 32 && nbits(x) != 32) warn(s"Don't know area for $d - using default")
      FPGAResources(lut4=50,lut6=132,regs=238)

    case Fltpt_to_fixpt(_) =>
      FPGAResources(lut4=160,lut6=96,regs=223+nbits(s))


    // TODO: These need new numbers after Raghu's changes
    case tt: TileTransfer[_] if tt.store =>
      FPGAResources(lut3=1900,lut4=167,lut5=207,lut6=516,lut7=11,regs=5636,dsps=3,bram=46) // 2014.1 was dsp=3

    case tt: TileTransfer[_] if !tt.store =>
      FPGAResources(lut3=453, lut4=60, lut5=131,lut6=522,regs=1377,dsps=4,bram=46) // 2014.1 was dsp=4

    case _:Pipe_parallel => FPGAResources(lut4=9*nStages(s)/2, regs = nStages(s) + 3)

    case _:Pipe_foreach if styleOf(s) == Coarse => areaOfMetapipe(nStages(s))
    case _:Pipe_reduce[_,_] if styleOf(s) == Coarse => areaOfMetapipe(nStages(s))
    case _:Block_reduce[_] if styleOf(s) == Coarse => areaOfMetapipe(nStages(s))

    case _:Pipe_foreach if styleOf(s) == Disabled => areaOfSequential(nStages(s))
    case _:Pipe_reduce[_,_] if styleOf(s) == Disabled => areaOfSequential(nStages(s))
    case _:Block_reduce[_] if styleOf(s) == Disabled => areaOfSequential(nStages(s))
    case _:Unit_pipe if styleOf(s) == Disabled => areaOfSequential(nStages(s))

    // Nodes with known zero area cost
    case Reg_read(_)    => NoArea
    case Reg_write(_,_) => NoArea
    case Reg_reset(_)   => NoArea
    case Offchip_new(_) => NoArea
    case _:Pipe_foreach if styleOf(s) == Fine => NoArea
    case _:Pipe_reduce[_,_] if styleOf(s) == Fine => NoArea
    case _:Unit_pipe if styleOf(s) == Fine => NoArea

    // Effects
    case Reflect(d,_,_) => areaOfNode(s,d)
    case Reify(_,_,_) => NoArea
    case _ =>
      warn(s"Don't know area for $d")
      NoArea
  }
}
