package ppl.dsl.forge
package dsls
package optima

import core.{ForgeApplication,ForgeApplicationRunner}

trait MultiArrayMetadata { this: OptiMADSL =>

  def importMultiArrayMetadata() {
    val ArrayND = lookupTpe("ArrayND")
    val Array1D = lookupTpe("Array1D")
    val Array2D = lookupTpe("Array2D")
    val Array3D = lookupTpe("Array3D")

    //--------------------------
    //--- Metadata definitions
    //--------------------------

    // --- Implementation form (used for views and buffers)
    // TODO: Ternary is more general, could be useful to move elsewhere (may want to change naming scheme)
    val Ternary = tpe("Ternary", stage=compile)
    identifier (Ternary) ("False_3")
    identifier (Ternary) ("Partial_3")
    identifier (Ternary) ("True_3")

    val Form = metadata("Form", ("v", Ternary))
    onMeet (Form) ${ if (this != that) Form(Partial_3) else that }


    // --- MultiArray isBuffer
    val MBuffer = metadata("MBuffer", ("form", Form))
    onMeet (MBuffer) ${ MBuffer(meet(this.form, that.form)) }

    internal.infix (MBuffer) ("isTrue", Nil, MBuffer :: SBoolean) implements composite ${ $0.form.v == True_3 }
    internal.infix (MBuffer) ("isPhys", Nil, MBuffer :: SBoolean) implements composite ${ $0.form.v == Partial_3 }
    internal (MBuffer) ("enableBuffer", Nil, MAny :: MUnit, effect = simple) implements composite ${
      setMetadata($0, MBuffer(Form(True_3)))
      setUpdated($0)
    }

    // --- MultiArray isView
    val MView = metadata("MView", ("form", Form))
    onMeet (MView) ${ MView(meet(this.form, that.form)) }

    internal.infix (MView) ("isTrue", Nil, MView :: SBoolean) implements composite ${ $0.form.v == True_3 }
    internal.infix (MView) ("isPhys", Nil, MView :: SBoolean) implements composite ${ $0.form.v == Partial_3 }
    internal (MView) ("enableView", Nil, MAny :: MUnit, effect = simple) implements composite ${ setMetadata($0, MView(Form(True_3))) }

    // --- MultiArray rank
    val MRank = metadata("MRank", ("rank", SInt))
    val rank = grp("rank")
    onMeet (MRank) ${ MRank(this.rank) }
    canMeet (MRank) ${ this.rank == that.rank }

    // --- MultiArray may be updated
    val MayUpdate = metadata("MayUpdate", ("mayUpdate", SBoolean))
    onMeet (MayUpdate) ${ MayUpdate(this.mayUpdate || that.mayUpdate) }

    internal (MayUpdate) ("setUpdated", Nil, MAny :: MUnit, effect = simple) implements composite ${ setMetadata($0, MayUpdate(true)) }

    // TODO: Bit annoying to specify both versions - better way to generate both from one?
    for (T <- List(SymProps, MAny)) {
      internal (MView) ("getView", Nil, T :: SOption(MView)) implements composite ${ meta[MView]($0) }
      internal (MView) ("isPhysView", Nil, T :: SBoolean) implements composite ${ getView($0).map{_.isPhys}.getOrElse(false) }
      internal (MView) ("isTrueView", Nil, T :: SBoolean) implements composite ${ getView($0).map{_.isTrue}.getOrElse(false) }

      internal (MBuffer) ("getBuffer", Nil, T :: SOption(MBuffer)) implements composite ${ meta[MBuffer]($0) }
      internal (MBuffer) ("isPhysBuffer", Nil, T :: SBoolean) implements composite ${ getBuffer($0).map{_.isPhys}.getOrElse(false) }
      internal (MBuffer) ("isTrueBuffer", Nil, T :: SBoolean) implements composite ${ getBuffer($0).map{_.isTrue}.getOrElse(false) }

      internal (MRank) ("getRank", Nil, T :: SOption(MRank)) implements composite ${ meta[MRank]($0) }
      // Note rank() will throw an exception if used before all ranks have been assigned!
      internal.static (rank) ("apply", Nil, T :: SInt) implements composite ${
        getLayout($0).map(_.rank).getOrElse(getRank($0).get.rank)
      }

      internal (MayUpdate) ("getMayUpdate", Nil, T :: SOption(MayUpdate)) implements composite ${ meta[MayUpdate]($0) }
      internal (MayUpdate) ("mayUpdate", Nil, T :: SBoolean) implements composite ${ getMayUpdate($0).map{_.mayUpdate}.getOrElse(false) }
    }

    internal.static (rank) ("update", Nil, (MAny, SInt) :: MUnit, effect = simple) implements composite ${ setMetadata($0, MRank($1)) }
    internal.static (rank) ("update", Nil, (MAny, SOption(MRank)) :: MUnit, effect = simple) implements composite ${ setMetadata($0, $1) }

    defaultMetadata(MArray) ${ MRank(1) }
    defaultMetadata(Array1D) ${ MRank(1) }
    defaultMetadata(Array2D) ${ MRank(2) }
    defaultMetadata(Array3D) ${ MRank(3) }

    // --- MultiArray layout
    val LayoutType = tpe("LayoutType", stage=compile)
    identifier (LayoutType) ("Flat")

    val LayoutSubtype = tpe("LayoutSubtype", stage=compile)
    identifier (LayoutSubtype) ("Plain")
    identifier (LayoutSubtype) ("View")
    identifier (LayoutSubtype) ("Buffer")
    identifier (LayoutSubtype) ("BuffView")

    val MLayout = metadata("MLayout", ("rank", SInt), ("tpe", LayoutType), ("subtpe", LayoutSubtype))
    onMeet (MLayout) ${ that }
    canMeet (MLayout) ${ this == that }

    internal.infix (MLayout) ("isView", Nil, MLayout :: SBoolean) implements composite ${ $0.subtpe == View || $0.subtpe == BuffView }

    val layout = grp("layout")

    for (T <- List(SymProps, MAny)) {
      internal (MLayout) ("getLayout", Nil, T :: SOption(MLayout)) implements composite ${ meta[MLayout]($0) }
      internal.static (layout) ("apply", Nil, T :: MLayout) implements composite ${ getLayout($0).get }
    }

    internal.static (layout) ("update", Nil, (MAny, MLayout) :: MUnit, effect = simple) implements composite ${ setMetadata($0, $1) }
    internal.static (layout) ("update", Nil, (MAny, SOption(MLayout)) :: MUnit, effect = simple) implements composite ${ setMetadata($0, $1) }
  }
}