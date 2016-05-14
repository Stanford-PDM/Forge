package dhdl.compiler.ops

import scala.reflect.{Manifest,SourceContext}

import dhdl.shared._
import dhdl.shared.ops._
import dhdl.compiler._
import dhdl.compiler.ops._
import dhdl.compiler.transform._

import scala.collection.mutable.HashMap

trait ContentionModel {
  val IR: DHDLExp
  import IR._

  val isolatedContention = HashMap[Exp[Any],List[Int]]()

  def outerContention(x: Exp[Any], P: => Int): Int = {
    if (styleOf(x) != Fine) {
      val ics = childrenOf(x).map{c => calcContention(c) * P}

      if (ics.isEmpty) stageError(s"Controller $x has no children!")

      isolatedContention(x) = ics
      if (styleOf(x) == Coarse) ics.sum else ics.max
    }
    else 0
  }

  def calcContention(x: Exp[Any]): Int = x match {
    case Def(EatReflect(Hwblock(_)))        => outerContention(x, 1)
    case Def(EatReflect(_:Pipe_parallel))   => childrenOf(x).map(calcContention).sum
    case Def(EatReflect(_:Unit_pipe))       => outerContention(x, 1)
    case Def(EatReflect(e:Pipe_foreach))    => outerContention(x, parsOf(e.cchain).reduce{_*_})
    case Def(EatReflect(e:Pipe_fold[_,_]))  => outerContention(x, parsOf(e.cchain).reduce{_*_})
    case Def(EatReflect(e:Accum_fold[_,_])) => outerContention(x, parsOf(e.ccOuter).reduce{_*_})
    case Def(EatReflect(_:Offchip_load_vector[_]))  => 1
    case Def(EatReflect(_:Offchip_store_vector[_])) => 1
    case _ => 0
  }

  def markPipe(x: Exp[Any], parent: Int) {
    if (styleOf(x) == Coarse) childrenOf(x).foreach{child => markContention(child,parent) }
    else if (styleOf(x) == Disabled) {
      val ics = isolatedContention(x)
      val mx = ics.max
      // Can just skip case where mx = 0 - no offchip memory accesses in this sequential anyway
      if (mx > 0) childrenOf(x).zip(ics).foreach{case (child,c) => markContention(child, (parent/mx)*c) }
    }
  }

  def markContention(x: Exp[Any], parent: Int): Unit = x match {
    case Def(EatReflect(Hwblock(_)))        => markPipe(x, parent)
    case Def(EatReflect(_:Pipe_parallel))   => childrenOf(x).foreach{child => markContention(child,parent)}
    case Def(EatReflect(_:Unit_pipe))       => markPipe(x, parent)
    case Def(EatReflect(_:Pipe_foreach))    => markPipe(x, parent)
    case Def(EatReflect(_:Pipe_fold[_,_]))  => markPipe(x, parent)
    case Def(EatReflect(_:Accum_fold[_,_])) => markPipe(x, parent)
    case Def(EatReflect(_:Offchip_load_vector[_])) => contentionOf(x) = parent
    case Def(EatReflect(_:Offchip_store_vector[_])) => contentionOf(x) = parent
    case _ => // do nothing
  }

  def run(top: Exp[Any]) = {
    val c = calcContention(top)
    markContention(top, c)
  }
}
