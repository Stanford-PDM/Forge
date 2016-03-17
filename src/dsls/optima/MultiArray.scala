package ppl.dsl.forge
package dsls
package optima

import core.{ForgeApplication,ForgeApplicationRunner}

trait MultiArrays { this: OptiMADSL =>

  // TODO: Expand and move to a different file
  def importIndices() {
    val Indices = lookupTpe("Indices")
    internal (Indices) ("indices_new", Nil, SList(MInt) :: Indices) implements record(Indices, ("i", SList(MInt), quotedArg(0)))
    internal.static (Indices) ("apply", Nil, varArgs(MInt) :: Indices) implements composite ${ indices_new($0.toList) }
    internal.infix (Indices) ("apply", Nil, (Indices, SInt) :: MInt) implements composite ${ field[Int]($0, "i_" + $1) }
    internal.infix (Indices) ("toList", Nil, (Indices, SInt) :: SList(MInt)) implements composite ${ List.tabulate($1){i => $0(i)} }
  }

  def importMultiArrays() {
    val T = tpePar("T")
    val R = tpePar("R")
    val S = List(TStringable(T))

    val ArrayND = lookupTpe("ArrayND")
    val Array1D = lookupTpe("Array1D")
    val Array2D = lookupTpe("Array2D")
    val Array3D = lookupTpe("Array3D")
    val Indices = lookupTpe("Indices")
    val Range   = lookupTpe("Range")

    // --- Nodes
    // These don't really both need to be nodes...
    internal (ArrayND) ("ma_new", T, SList(MInt) :: ArrayND(T), effect = mutable) implements figment ${
      maflat_new($0, MLayout($0.length,Flat,Plain))
    }
    internal (ArrayND) ("ma_new_immutable", T, SList(MInt) :: ArrayND(T)) implements figment ${
      maflat_new_immutable($0, MLayout($0.length,Flat,Plain))
    }
    internal (ArrayND) ("ma_view", T, (ArrayND(T), SList(Range), SList(SInt)) :: ArrayND(T)) implements figment ${
      maflat_view($0, $1, $2, MLayout($1.length - $2.length,Flat,View))
    }

    val ArrayND_Internals = withTpe(ArrayND)
    ArrayND_Internals {
      // --- Compiler shortcuts
      internal.infix ("as3D") (Nil :: Array3D(T)) implements redirect ${ $self.asInstanceOf[Rep[Array3D[T]]] }
      internal.infix ("as2D") (Nil :: Array2D(T)) implements redirect ${ $self.asInstanceOf[Rep[Array2D[T]]] }
      internal.infix ("as1D") (Nil :: Array1D(T)) implements redirect ${ $self.asInstanceOf[Rep[Array1D[T]]] }

      // --- Single element operators
      internal ("ma_apply") (Indices :: T) implements figment ${ maflat_apply($0, $1) }
      internal ("ma_update") ((Indices, T) :: MUnit, effect = write(0)) implements figment ${ maflat_update($0, $1, $2) }

      // --- Misc.
      internal ("ma_mkstring") ((SList(MString), T ==> MString) :: MString) implements figment ${ maimpl_mkstring($0, $1, $2) }
    }


    //--- API
    static (ArrayND) ("apply", T, varArgs(MInt) :: ArrayND(T)) implements composite ${ ma_new[T]($0.toList) }
    static (Array3D) ("apply", T, (MInt, MInt, MInt) :: Array3D(T)) implements composite ${ ma_new[T](List($0, $1, $2)).as3D }
    static (Array2D) ("apply", T, (MInt, MInt) :: Array2D(T)) implements composite ${ ma_new[T](List($0, $1)).as2D }
    static (Array1D) ("apply", T, MInt :: Array1D(T)) implements composite ${ ma_new[T](List($0)).as1D }

    val ArrayND_API = withTpe(ArrayND)
    ArrayND_API {
      // --- Properties
      infix ("size") (Nil :: MInt) implements figment ${ maimpl_size($self) }
      infix ("dim") (SInt :: MInt) implements figment ${ maimpl_dim($self, $1) }

      // --- Single elements
      // Note: Scala doesn't support varArgs in updates right now (without extra macro stuff anyway)
      infix ("apply") (varArgs(MInt) :: T) implements composite ${ ma_apply($self, indices_new($1.toList)) }
      infix ("update") ((SList(MInt), T) :: MUnit, effect = write(0)) implements composite ${ ma_update($self, indices_new($1), $2) }

      // --- Misc.
      infix ("makeString") (varArgs(MString) :: MString, S) implements composite ${ ma_mkstring($self, $1.toList, {e: Rep[T] => padspace(e.mkStr)}) }
    }

    val Array1D_API = withTpe(Array1D)
    Array1D_API {
      infix ("length") (Nil :: MInt) implements composite ${ $self.size }
      infix ("apply") (MInt :: T) implements composite ${ ma_apply($self, Indices($1)) }
      infix ("update") ((MInt, T) :: MUnit, effect = write(0)) implements composite ${ ma_update($self, Indices($1), $2) }

      // --- Misc.
      infix ("makeString") (Nil :: MString, S) implements composite ${ ma_mkstring($self, List(""), {e: Rep[T] => padspace(e.mkStr)} )}
      infix ("toString") (Nil :: MString) implements composite ${ ma_mkstring($self, List(""), {e: Rep[T] => padspace(format_numeric(e))} )}
      infix ("pprint") (Nil :: MUnit, S, effect = simple) implements composite ${ println($self.makeString) }
    }

    val Array2D_API = withTpe(Array2D)
    Array2D_API {
      infix ("nRows") (Nil :: MInt) implements composite ${ $self.dim(0) }
      infix ("nCols") (Nil :: MInt) implements composite ${ $self.dim(1) }

      infix ("apply") ((MInt,MInt) :: T) implements composite ${ ma_apply($self, Indices($1, $2)) }
      infix ("update") ((MInt,MInt,T) :: MUnit, effect = write(0)) implements composite ${ ma_update($self, Indices($1, $2), $3) }

      // --- Misc.
      infix ("makeString") (Nil :: MString, S) implements composite ${ ma_mkstring($self, List("\\n",""), {e: Rep[T] => padspace(e.mkStr)} )}
      infix ("toString") (Nil :: MString) implements composite ${ ma_mkstring($self, List("\\n",""), {e: Rep[T] => padspace(format_numeric(e))} )}
      infix ("pprint") (Nil :: MUnit, S, effect = simple) implements composite ${ println($self.makeString) }
    }


  }
}