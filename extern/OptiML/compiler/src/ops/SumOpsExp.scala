package optiml.compiler.ops

import scala.tools.nsc.io._
import scala.reflect.{Manifest,SourceContext}
import scala.virtualization.lms.common.{Base,BaseExp,EffectExp,BaseFatExp}
import scala.virtualization.lms.common.{ScalaGenBase,ScalaGenEffect,ScalaGenFat}
import scala.virtualization.lms.util._
import scala.virtualization.lms.internal._
import ppl.delite.framework.ops.DeliteCollection
import ppl.delite.framework.datastructures._
import ppl.delite.framework.ops.{DeliteOpsExp, DeliteCollectionOpsExp}
import ppl.delite.framework.Util._
import optiml.shared._
import optiml.shared.ops._
import optiml.shared.typeclass._
import optiml.compiler._
import optiml.compiler.ops._

trait SumOpsExp extends SumOps with BaseFatExp with EffectExp {
  this: OptiMLExp =>

   case class Sum[A:Manifest:Arith](start: Exp[Int], end: Exp[Int], map: Exp[Int] => Exp[A], init: Exp[A])(implicit canSum: CanSum[A,A], ctx: SourceContext)
     extends DeliteOpMapReduceZero[Int,A] {

     override val mutable = true // can we do this automatically?

     val in = copyTransformedOrElse(_.in)(IndexVector(start,end))
     val size = copyTransformedOrElse(_.size)(end - start)
     def zero = a.zero(init)
     override lazy val accInit = reifyEffects(canSum.mutableA(a.zero(init)))
     def reduce = (a,b) => canSum.accA(a,b)

     def m = manifest[A]
     def a = implicitly[Arith[A]]
     def cs = implicitly[CanSum[A,A]]
     def sc = implicitly[SourceContext]
   }

   // TODO: Damien fix this
  case class SumIf[R:Manifest:Arith,A:Manifest](start: Exp[Int], end: Exp[Int], co: Exp[Int] => Exp[Boolean], fu: Exp[Int] => Exp[A])(implicit canSum: CanSum[R,A], ctx: SourceContext) // TODO aks: CS into Arith
    extends DeliteOpFoldLike[A, R] {
      type OpType <: SumIf[R, A]

    val accInit: Block[R] = copyTransformedBlockOrElse(_.accInit)(reifyEffects(canSum.mutableR(a.empty)))
    override val mutable = true

    val in: Exp[DeliteCollection[Int]] = copyTransformedOrElse(_.in)(IndexVector(start,end))
    def fin = dc_apply(in, this.v)

    val size: Exp[Int] = copyTransformedOrElse(_.size)(end - start)

    def flatMapLikeFunc(): Exp[DeliteCollection[A]] = {
      IfThenElse(co(fin), reifyEffects(DeliteArray.singletonInLoop(fu(fin), v)), reifyEffects(DeliteArray.emptyInLoop[A](v)))
    }
    
    def foldPar(acc: Exp[R], add: Exp[A]): Exp[R] = canSum.accA(acc, add) 
    def redSeq(x1: Exp[R], x2: Exp[R]): Exp[R] = canSum.accR(x1, x2)

    def mR = manifest[R]
    def a = implicitly[Arith[R]]
    def mA = manifest[A]
    def cs = implicitly[CanSum[R,A]]
    def sc = implicitly[SourceContext]
  }

  def optiml_sum[A:Manifest:Arith](start: Exp[Int], end: Exp[Int], block: Exp[Int] => Exp[A])(implicit cs: CanSum[A,A], ctx: SourceContext) = {
    // don't add it back in, just re-compute it to avoid the peeled iteration problems
    val zero = block(start)
    reflectPure(Sum(start,end,block,zero))
  }

  def optiml_sumif[R:Manifest:Arith,A:Manifest](start: Exp[Int], end: Exp[Int], cond: Exp[Int] => Exp[Boolean], block: Exp[Int] => Exp[A])(implicit cs: CanSum[R,A], ctx: SourceContext) = {
    reflectPure(SumIf[R,A](start, end, cond, block))
  }


  /**
   * Mirroring
   */
  override def mirror[A:Manifest](e: Def[A], f: Transformer)(implicit ctx: SourceContext): Exp[A] = {
    e match {
      case e@Sum(st,en,b,init) => reflectPure(new { override val original = Some(f,e) } with Sum(f(st),f(en),f(b),f(init))(mtype(e.m),atype(e.a),cstype(e.cs),e.sc))(mtype(manifest[A]), implicitly[SourceContext])
      case e@SumIf(st,en,c,b) => reflectPure(new { override val original = Some(f,e) } with SumIf(f(st),f(en),f(c),f(b))(mtype(e.mR),atype(e.a),mtype(e.mA),cstype(e.cs),e.sc))(mtype(manifest[A]), implicitly[SourceContext])
      case Reflect(e@Sum(st,en,b,init), u, es) => reflectMirrored(Reflect(new { override val original = Some(f,e) } with Sum(f(st),f(en),f(b),f(init))(mtype(e.m), atype(e.a), cstype(e.cs), e.sc), mapOver(f,u), f(es)))(mtype(manifest[A]), ctx)
      case Reflect(e@SumIf(st,en,c,b), u, es) => reflectMirrored(Reflect(new { override val original = Some(f,e) } with SumIf(f(st),f(en),f(c),f(b))(mtype(e.mR),atype(e.a),mtype(e.mA),cstype(e.cs),e.sc), mapOver(f,u), f(es)))(mtype(manifest[A]), ctx)
      case _ => super.mirror(e, f)
  }}.asInstanceOf[Exp[A]] // why??
}

// these need to exist for externs, even though we don't need them for sum
trait ScalaGenSumOps
trait CudaGenSumOps
trait OpenCLGenSumOps
trait CGenSumOps

