package ppl.dsl.forge
package examples
package optila

import core.{ForgeApplication,ForgeApplicationRunner}

trait DenseVectorOps {
  this: OptiLADSL => 

  def importDenseVectorOps() {
    val T = tpePar("T") 
    val R = tpePar("R")
    val B = tpePar("B")
    
    val DenseVector = lookupTpe("DenseVector") // tpe("DenseVector", T) 
    val IndexVector = lookupTpe("IndexVector")
    val DenseVectorView = lookupTpe("DenseVectorView")
    val DenseMatrix = lookupTpe("DenseMatrix")
  
    // data fields     
    data(DenseVector, ("_length", MInt), ("_isRow", MBoolean), ("_data", MArray(T)))      
  
    // static methods
    static (DenseVector) ("apply", T, (MInt, MBoolean) :: DenseVector(T), effect = mutable) implements allocates(DenseVector, ${$0}, ${$1}, ${array_empty[T]($0)})
    static (DenseVector) ("apply", T, varArgs(T) :: DenseVector(T)) implements allocates(DenseVector, ${unit($0.length)}, ${unit(true)}, ${array_fromseq($0)})
    
    // helper
    compiler (DenseVector) ("densevector_fromfunc", T, (MInt, MInt ==> T) :: DenseVector(T)) implements single ${
      val out = DenseVector[T]($0, true)
      for (i <- 0 until out.length) {
        out(i) = $1(i)
      }      
      out.unsafeImmutable
    }    
    static (DenseVector) ("zeros", Nil, MInt :: DenseVector(MDouble)) implements single ${ densevector_fromfunc($0, i => 0.0 )}
    static (DenseVector) ("zerosf", Nil, MInt :: DenseVector(MFloat)) implements single ${ densevector_fromfunc($0, i => 0f )}
    static (DenseVector) ("ones", Nil, MInt :: DenseVector(MDouble)) implements single ${ densevector_fromfunc($0, i => 1.0) }
    static (DenseVector) ("onesf", Nil, MInt :: DenseVector(MFloat)) implements single ${ densevector_fromfunc($0, i => 1f) }
    static (DenseVector) ("rand", Nil, MInt :: DenseVector(MDouble)) implements single ${ densevector_fromfunc($0, i => random[Double]) }
    static (DenseVector) ("randf", Nil, MInt :: DenseVector(MFloat)) implements single ${ densevector_fromfunc($0, i => random[Float]) }
    static (DenseVector) ("uniform", Nil, MethodSignature(List(("start", MInt), ("step_size", MDouble), ("end", MInt), ("isRow", MBoolean, "true")), DenseVector(MDouble))) implements single ${ 
      val length = ceil(($end-$start)/$step_size)
      densevector_fromfunc(length, i => $step_size*i + $start)
    }
    
    static (DenseVector) ("flatten", T, ("pieces",DenseVector(DenseVector(T))) :: DenseVector(T)) implements single ${
      if ($pieces.length == 0){
        DenseVector[T](0, $pieces.isRow).unsafeImmutable
      }
      else {
        val sizes = $pieces map { e => e.length }
        val (total,begins) = t2(densevector_precumulate[Int](sizes, 0, (_: Rep[Int]) + (_: Rep[Int])))
        val result = DenseVector[T](total, $pieces.isRow)
        for (i <- 0 until $pieces.length) {
          result.copyFrom(begins(i), $pieces(i))
        }
        result.unsafeImmutable
      }
    }              
    
    // only composite ops can return non-lifted tuples (or anything else). using CTuple2 should work, but there is a problem with iFThenElse that I don't fully understand yet.
    // val CTuple2 = lookupTpe("Tuple2",now)
    val Tuple2 = lookupTpe("Tup2")
    compiler (DenseVector) ("densevector_precumulate", T, ((("v",DenseVector(T)), ("identity",T), ("func",(T,T) ==> T)) :: Tuple2(T,DenseVector(T)))) implements composite ${
      if ($v.length == 0) {
        (($identity,DenseVector[T](0,$v.isRow).unsafeImmutable))
      } 
      else {
        val result = DenseVector[T](0, $v.isRow)
        var accum = $identity
        for (i <- 0 until $v.length) {
          result <<= accum
          accum = $func(accum, $v(i))
        }
        (accum,result.unsafeImmutable)      
      }
    } 

    // a non-type-safe way of passing the metadata required to allocate a DenseVector in a parallel op
    // ideally we would encode this is as a type class, but it's not clear we would get an instance of this type class in dc_alloc
    val CR = tpePar("CR")
    compiler (DenseVector) ("densevector_raw_alloc", (R,CR), (CR,MInt) :: DenseVector(R)) implements composite ${
      val ms = manifest[CR].toString
      val simpleName = ms.drop(ms.lastIndexOf("\$\$")+1)         
      val isRow = simpleName match {
        case s if s.startsWith("IndexVector") => indexvector_isrow($0.asInstanceOf[Rep[IndexVector]])
        case s if s.startsWith("DenseVectorView") => densevectorview_isrow($0.asInstanceOf[Rep[DenseVectorView[Any]]])
        case s if s.startsWith("DenseVector") => densevector_isrow($0.asInstanceOf[Rep[DenseVector[Any]]])
      }
      DenseVector[R]($1, isRow) 
    }        
          
    val DenseVectorOps = withTpe (DenseVector)          
    DenseVectorOps {                                        
      /**
       * Accessors
       */
      infix ("length") (Nil :: MInt) implements getter(0, "_length")
      infix ("isRow") (Nil :: MBoolean) implements getter(0, "_isRow")
      infix ("apply") (MInt :: T) implements composite ${ array_apply(densevector_raw_data($self), $1) }                        
      
      
      /**
       * Miscellaneous
       */
      infix ("t") (Nil :: DenseVector(T)) implements allocates(DenseVector, ${densevector_length($0)}, ${!(densevector_isrow($0))}, ${array_clone(densevector_raw_data($0))})
      infix ("mt") (Nil :: MUnit, effect = write(0)) implements composite ${
        densevector_set_isrow($0, !$0.isRow)
      }
      infix ("Clone") (Nil :: DenseVector(T), aliasHint = copies(0)) implements map((T,T), 0, "e => e")
      infix ("mutable") (Nil :: DenseVector(T), effect = mutable, aliasHint = copies(0)) implements single ${
        val out = DenseVector[T]($self.length, $self.isRow)        
        for (i <- 0 until out.length) {
          out(i) = $self(i)
        }
        out
      }   
      infix ("replicate") ((MInt,MInt) :: DenseMatrix(T)) implements single ${
        if ($self.isRow) {
          val out = DenseMatrix[T]($1, $2*$self.length)
          for (col <- 0 until $2*$self.length){
            val colToJ = col % $self.length
            for (rI <- 0 until $1) {
              out(rI, col) = $self(colToJ)
            }
          }
          out.unsafeImmutable
        }
        else {
          val out = DenseMatrix[T]($1*$self.length, $2)
          for (row <- 0 until $1*$self.length){
            val rowToI = row % $self.length
            for (cI <- 0 until $2) {
              out(row, cI) = $self(rowToI)
            }
          }
          out.unsafeImmutable
        }
      }
        
      
      /**
       * Data operations
       */
      compiler ("densevector_raw_data") (Nil :: MArray(T)) implements getter(0, "_data")
      compiler ("densevector_set_raw_data") (MArray(T) :: MUnit, effect = write(0)) implements setter(0, "_data", ${$1})
      compiler ("densevector_set_length") (MInt :: MUnit, effect = write(0)) implements setter(0, "_length", ${$1})                  
      compiler ("densevector_set_isrow") (MBoolean :: MUnit, effect = write(0)) implements setter(0, "_isRow", ${$1})
      
      infix ("update") ((("i",MInt),("e",T)) :: MUnit, effect = write(0)) implements composite ${
        array_update(densevector_raw_data($self), $i, $e)
      }      
      infix ("<<") (T :: DenseVector(T)) implements single ${
        val out = DenseVector[T](0,$self.isRow)
        out <<= $self
        out <<= $1
        out.unsafeImmutable
      }      
      infix("<<") (DenseVector(T) :: DenseVector(T)) implements single ${
        val out = DenseVector[T]($self.length+$1.length, $self.isRow)
        for (i <- 0 until $self.length){
          out(i) = $self(i)
        }
        for (i <- 0 until $1.length){
          out(i+$self.length) = $1(i)
        }
        out.unsafeImmutable        
      }
      infix ("<<=") (T :: MUnit, effect = write(0)) implements composite ${ $self.insert($self.length,$1) }          
      infix ("<<=") (DenseVector(T) :: MUnit, effect = write(0)) implements composite ${ $self.insertAll($self.length,$1) }
            
      infix ("insert") ((MInt,T) :: MUnit, effect = write(0)) implements single ${
        densevector_insertspace($self,$1,1)
        $self($1) = $2
      }      
      infix ("insertAll") ((MInt,DenseVector(T)) :: MUnit, effect = write(0)) implements single ${
        densevector_insertspace($self, $1, $2.length)
        $self.copyFrom($1, $2)     
      }
      infix ("remove") (MInt :: MUnit, effect = write(0)) implements composite ${ $self.removeAll($1, unit(1)) }
      infix ("removeAll") ((("pos",MInt),("len",MInt)) :: MUnit, effect = write(0)) implements single ${
        val data = densevector_raw_data($self)
        array_copy(data, $pos + $len, data, $pos, $self.length - ($pos + $len))
        densevector_set_length($self, $self.length - $len)        
      }
            
      infix ("copyFrom") ((MInt,DenseVector(T)) :: MUnit, effect = write(0)) implements single ${        
        val d = densevector_raw_data($self)
        for (i <- 0 until $2.length) {
          array_update(d,$1+i,$2(i))
        }        
      }
      infix ("trim") (Nil :: MUnit, effect = write(0)) implements single ${
        val data = densevector_raw_data($self)
        if ($self.length < array_length(data)) {
          val d = array_empty[T]($self.length)
          array_copy(data, 0, d, 0, $self.length)
          densevector_set_raw_data($self, d.unsafeImmutable)
        }        
      }
      infix ("clear") (Nil :: MUnit, effect = write(0)) implements single ${
        densevector_set_length($self, 0)
        densevector_set_raw_data($self, (array_empty[T](0)).unsafeImmutable)        
      }      
      
      compiler ("densevector_insertspace") ((("pos",MInt),("len",MInt)) :: MUnit, effect = write(0)) implements single ${
        densevector_ensureextra($self,$len)
        val data = densevector_raw_data($self)
        array_copy(data,$pos,data,$pos+$len,$self.length-$pos)
        densevector_set_length($self,$self.length+$len)
      }      
      compiler ("densevector_ensureextra") (("extra",MInt) :: MUnit, effect = write(0)) implements single ${
        val data = densevector_raw_data($self)
        if (array_length(data) - $self.length < $extra) {
          densevector_realloc($self, $self.length+$extra)
        }
      }      
      compiler ("densevector_realloc") (("minLen",MInt) :: MUnit, effect = write(0)) implements single ${
        val data = densevector_raw_data($self)
        var n = Math.max(4, array_length(data)*2)
        while (n < $minLen) n = n*2
        val d = array_empty[T](n)
        array_copy(data, 0, d, 0, $self.length)
        densevector_set_raw_data($self, d.unsafeImmutable)  
      }        
      
      
      /**
       * Math
       */   
       
      infix ("+=") (DenseVector(T) :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) + $1(i) }
      }
      infix ("+=") (T :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) + $1 }
      }
      // so that we can add without converting to Dense
      infix ("+=") (DenseVectorView(T) :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) + $1(i) }
      }
            
      infix ("*=") (DenseVector(T) :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) * $1(i) }
      }
      infix ("*=") (T :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) * $1 }
      }
      infix ("*=") (DenseVectorView(T) :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) * $1(i) }
      }   
      
      infix ("-=") (DenseVector(T) :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) - $1(i) }
      }
      infix ("-=") (T :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) - $1 }
      }      
      infix ("-=") (DenseVectorView(T) :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) - $1(i) }
      }      
      
      infix ("/=") (DenseVector(T) :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) / $1(i) }
      }
      infix ("/=") (T :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) / $1 }
      }      
      infix ("/=") (DenseVectorView(T) :: MUnit, TArith(T), effect = write(0)) implements composite ${
        $self.indices.foreach { i => $self(i) = $self(i) / $1(i) }
      }      
      
      
      /**
       * Ordering
       */      
      infix ("sort") (Nil :: DenseVector(T), TOrdering(T)) implements allocates(DenseVector, ${densevector_length($0)}, ${!(densevector_isrow($0))}, ${array_sort(densevector_raw_data($0))})

      // TODO: HasMinMax, TupleReduce?
      // infix ("min" (Nil :: T, TOrdering(T))) implements reduce(T, 0, ${implicitly[HasMinMax[T]].min}, ${ if (a < b) a else b }) 
      // infix ("minIndex" (Nil :: T, TOrdering(T))) implements reduce(T, 0, ${implicitly[HasMinMax[T]].min}, ${ }) 
      // infix ("max" (Nil :: T, TOrdering(T))) implements reduce(T, 0, ${implicitly[HasMinMax[T]].max}, ${ if (a > b) a else b }) 
      // infix ("maxIndex" (Nil :: T, TOrdering(T))) implements reduce(T, 0, ${implicitly[HasMinMax[T]].max}, ${ }) 
      
      infix ("median") (Nil :: T, (TNumeric(T),TOrdering(T))) implements single ${ 
        val x = $self.sort
        val mid = x.length / 2
        if (x.length % 2 == 0) {
          ((x(mid).AsInstanceOf[Double] + x(mid-1).AsInstanceOf[Double]) / 2).AsInstanceOf[T]
        }
        else x(mid)
      }
      infix (":>") (DenseVector(T) :: DenseVector(MBoolean), TOrdering(T)) implements zip((T,T,MBoolean), (0,1), ${ (a,b) => a > b })
      infix (":<") (DenseVector(T) :: DenseVector(MBoolean), TOrdering(T)) implements zip((T,T,MBoolean), (0,1), ${ (a,b) => a < b })
                                    
                        
      /**
       * Required for parallel collection       
       */                  
      compiler ("densevector_appendable") ((MInt,T) :: MBoolean) implements single("true")
      compiler ("densevector_append") ((MInt,T) :: MUnit, effect = write(0)) implements single ${
        $self.insert($self.length, $2)
      }                                  
      compiler ("densevector_copy") ((MInt,DenseVector(T),MInt,MInt) :: MUnit, effect = write(2)) implements single ${
        val src = densevector_raw_data($self)
        val dest = densevector_raw_data($2)
        array_copy(src, $1, dest, $3, $4)
      }

      parallelize as ParallelCollectionBuffer(T, lookupOp("densevector_raw_alloc"), lookupOp("length"), lookupOverloaded("apply",2), lookupOp("update"), lookupOp("densevector_set_length"), lookupOp("densevector_appendable"), lookupOp("densevector_append"), lookupOp("densevector_copy"))            
    } 
        
    // Add DenseVector to Arith
    val Arith = lookupGrp("Arith").asInstanceOf[Rep[DSLTypeClass]]
    val DenseVectorArith = tpeClassInst("ArithDenseVector", T withBound TArith, Arith(DenseVector(T)))
    infix (DenseVectorArith) ("zero", T withBound TArith, DenseVector(T) :: DenseVector(T)) implements composite ${ DenseVector[T]($0.length,$0.isRow).unsafeImmutable }
    infix (DenseVectorArith) ("empty", T withBound TArith, Nil :: DenseVector(T)) implements composite ${ DenseVector[T](unit(0),unit(true)).unsafeImmutable }
    infix (DenseVectorArith) ("+", T withBound TArith, (DenseVector(T),DenseVector(T)) :: DenseVector(T)) implements composite ${ densevector_pl($0,$1) }
    infix (DenseVectorArith) ("-", T withBound TArith, (DenseVector(T),DenseVector(T)) :: DenseVector(T)) implements composite ${ densevector_sub($0,$1) }
    infix (DenseVectorArith) ("*", T withBound TArith, (DenseVector(T),DenseVector(T)) :: DenseVector(T)) implements composite ${ densevector_mul($0,$1) } 
    infix (DenseVectorArith) ("/", T withBound TArith, (DenseVector(T),DenseVector(T)) :: DenseVector(T)) implements composite ${ densevector_div($0,$1) }          
    infix (DenseVectorArith) ("abs", T withBound TArith, DenseVector(T) :: DenseVector(T)) implements composite ${ densevector_abs($0) }
    infix (DenseVectorArith) ("exp", T withBound TArith, DenseVector(T) :: DenseVector(T)) implements composite ${ densevector_exp($0) }         
        
    importDenseVectorPrimitiveOps()    
    addVectorCommonOps(DenseVector,T)
  }  
  
  
  
  /**
   * Special cases for DenseVector primitive arithmetic. This is annoying, so let's hide it at the bottom.
   */
  def importDenseVectorPrimitiveOps() {
    val DenseVector = lookupTpe("DenseVector")
    
    // the conversions here will be costly unless things fuse. alternatively, we could convert element by element.
    // TODO: unfortunately, these have priority over operators defined in VectorCommonOps, so they can sometimes force conversions.
    infix (DenseVector) ("+", Nil, (MInt,DenseVector(MInt)) :: DenseVector(MInt)) implements composite ${ densevector_pl[Int]($1,$0) }
    infix (DenseVector) ("+", Nil, (MInt,DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_pl[Float]($1,$0.toFloat) }
    infix (DenseVector) ("+", Nil, (MInt,DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($1,$0.toDouble) }
    infix (DenseVector) ("+", Nil, (MFloat,DenseVector(MInt)) :: DenseVector(MFloat)) implements composite ${ densevector_pl[Float]($1.toFloat,$0) }
    infix (DenseVector) ("+", Nil, (MFloat,DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_pl[Float]($1,$0) }
    infix (DenseVector) ("+", Nil, (MFloat,DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($1,$0.toDouble) }
    infix (DenseVector) ("+", Nil, (MDouble,DenseVector(MInt)) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($1.toDouble,$0) }
    infix (DenseVector) ("+", Nil, (MDouble,DenseVector(MFloat)) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($1.toDouble,$0) }
    infix (DenseVector) ("+", Nil, (MDouble,DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($1,$0) }
    infix (DenseVector) ("+", Nil, (DenseVector(MInt),MInt) :: DenseVector(MInt)) implements composite ${ densevector_pl[Int]($0,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MInt),MFloat) :: DenseVector(MFloat)) implements composite ${ densevector_pl[Float]($0.toFloat,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MInt),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($0.toDouble,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MFloat),MInt) :: DenseVector(MFloat)) implements composite ${ densevector_pl[Float]($0,$1.toFloat) }
    infix (DenseVector) ("+", Nil, (DenseVector(MFloat),MFloat) :: DenseVector(MFloat)) implements composite ${ densevector_pl[Float]($0,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MFloat),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($0.toDouble,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MDouble),MInt) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($0,$1.toDouble) }
    infix (DenseVector) ("+", Nil, (DenseVector(MDouble),MFloat) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($0.toDouble,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MDouble),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($0,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MInt),DenseVector(MInt)) :: DenseVector(MInt)) implements composite ${ densevector_pl[Int]($0,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MInt),DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_pl[Float]($0.toFloat,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MInt),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($0.toDouble,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MFloat),DenseVector(MInt)) :: DenseVector(MFloat)) implements composite ${ densevector_pl[Float]($0,$1.toFloat) }
    infix (DenseVector) ("+", Nil, (DenseVector(MFloat),DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_pl[Float]($0,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MFloat),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($0.toDouble,$1) }
    infix (DenseVector) ("+", Nil, (DenseVector(MDouble),DenseVector(MInt)) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($0,$1.toDouble) }
    infix (DenseVector) ("+", Nil, (DenseVector(MDouble),DenseVector(MFloat)) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($0,$1.toDouble) }
    infix (DenseVector) ("+", Nil, (DenseVector(MDouble),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_pl[Double]($0,$1) }    
    
    infix (DenseVector) ("-", Nil, (DenseVector(MInt),MInt) :: DenseVector(MInt)) implements composite ${ densevector_sub[Int]($0,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MInt),MFloat) :: DenseVector(MFloat)) implements composite ${ densevector_sub[Float]($0.toFloat,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MInt),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_sub[Double]($0.toDouble,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MFloat),MInt) :: DenseVector(MFloat)) implements composite ${ densevector_sub[Float]($0,$1.toFloat) }
    infix (DenseVector) ("-", Nil, (DenseVector(MFloat),MFloat) :: DenseVector(MFloat)) implements composite ${ densevector_sub[Float]($0,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MFloat),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_sub[Double]($0.toDouble,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MDouble),MInt) :: DenseVector(MDouble)) implements composite ${ densevector_sub[Double]($0,$1.toDouble) }
    infix (DenseVector) ("-", Nil, (DenseVector(MDouble),MFloat) :: DenseVector(MDouble)) implements composite ${ densevector_sub[Double]($0.toDouble,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MDouble),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_sub[Double]($0,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MInt),DenseVector(MInt)) :: DenseVector(MInt)) implements composite ${ densevector_sub[Int]($0,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MInt),DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_sub[Float]($0.toFloat,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MInt),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_sub[Double]($0.toDouble,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MFloat),DenseVector(MInt)) :: DenseVector(MFloat)) implements composite ${ densevector_sub[Float]($0,$1.toFloat) }
    infix (DenseVector) ("-", Nil, (DenseVector(MFloat),DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_sub[Float]($0,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MFloat),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_sub[Double]($0.toDouble,$1) }
    infix (DenseVector) ("-", Nil, (DenseVector(MDouble),DenseVector(MInt)) :: DenseVector(MDouble)) implements composite ${ densevector_sub[Double]($0,$1.toDouble) }
    infix (DenseVector) ("-", Nil, (DenseVector(MDouble),DenseVector(MFloat)) :: DenseVector(MDouble)) implements composite ${ densevector_sub[Double]($0,$1.toDouble) }
    infix (DenseVector) ("-", Nil, (DenseVector(MDouble),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_sub[Double]($0,$1) }    
    
    infix (DenseVector) ("unary_-", Nil, (DenseVector(MInt)) :: DenseVector(MInt)) implements composite ${ densevector_mul[Int]($0,unit(-1)) }
    infix (DenseVector) ("unary_-", Nil, (DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_mul[Float]($0,unit(-1f)) }
    infix (DenseVector) ("unary_-", Nil, (DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0,unit(-1.0)) }
    infix (DenseVector) ("*", Nil, (MInt,DenseVector(MInt)) :: DenseVector(MInt)) implements composite ${ densevector_mul[Int]($1,$0) }
    infix (DenseVector) ("*", Nil, (MInt,DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_mul[Float]($1,$0.toFloat) }
    infix (DenseVector) ("*", Nil, (MInt,DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($1,$0.toDouble) }
    infix (DenseVector) ("*", Nil, (MFloat,DenseVector(MInt)) :: DenseVector(MFloat)) implements composite ${ densevector_mul[Float]($1.toFloat,$0) }
    infix (DenseVector) ("*", Nil, (MFloat,DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_mul[Float]($1,$0) }
    infix (DenseVector) ("*", Nil, (MFloat,DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($1,$0.toDouble) }
    infix (DenseVector) ("*", Nil, (MDouble,DenseVector(MInt)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($1.toDouble,$0) }
    infix (DenseVector) ("*", Nil, (MDouble,DenseVector(MFloat)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($1.toDouble,$0) }
    infix (DenseVector) ("*", Nil, (MDouble,DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($1,$0) }
    infix (DenseVector) ("*", Nil, (DenseVector(MInt),MInt) :: DenseVector(MInt)) implements composite ${ densevector_mul[Int]($0,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MInt),MFloat) :: DenseVector(MFloat)) implements composite ${ densevector_mul[Float]($0.toFloat,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MInt),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0.toDouble,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MFloat),MInt) :: DenseVector(MFloat)) implements composite ${ densevector_mul[Float]($0,$1.toFloat) }
    infix (DenseVector) ("*", Nil, (DenseVector(MFloat),MFloat) :: DenseVector(MFloat)) implements composite ${ densevector_mul[Float]($0,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MFloat),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0.toDouble,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MDouble),MInt) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0,$1.toDouble) }
    infix (DenseVector) ("*", Nil, (DenseVector(MDouble),MFloat) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0.toDouble,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MDouble),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MInt),DenseVector(MInt)) :: DenseVector(MInt)) implements composite ${ densevector_mul[Int]($0,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MInt),DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_mul[Float]($0.toFloat,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MInt),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0.toDouble,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MFloat),DenseVector(MInt)) :: DenseVector(MFloat)) implements composite ${ densevector_mul[Float]($0,$1.toFloat) }
    infix (DenseVector) ("*", Nil, (DenseVector(MFloat),DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_mul[Float]($0,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MFloat),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0.toDouble,$1) }
    infix (DenseVector) ("*", Nil, (DenseVector(MDouble),DenseVector(MInt)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0,$1.toDouble) }
    infix (DenseVector) ("*", Nil, (DenseVector(MDouble),DenseVector(MFloat)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0,$1.toDouble) }
    infix (DenseVector) ("*", Nil, (DenseVector(MDouble),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_mul[Double]($0,$1) }    

    infix (DenseVector) ("/", Nil, (DenseVector(MInt),MInt) :: DenseVector(MInt)) implements composite ${ densevector_div[Int]($0,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MInt),MFloat) :: DenseVector(MFloat)) implements composite ${ densevector_div[Float]($0.toFloat,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MInt),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_div[Double]($0.toDouble,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MFloat),MInt) :: DenseVector(MFloat)) implements composite ${ densevector_div[Float]($0,$1.toFloat) }
    infix (DenseVector) ("/", Nil, (DenseVector(MFloat),MFloat) :: DenseVector(MFloat)) implements composite ${ densevector_div[Float]($0,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MFloat),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_div[Double]($0.toDouble,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MDouble),MInt) :: DenseVector(MDouble)) implements composite ${ densevector_div[Double]($0,$1.toDouble) }
    infix (DenseVector) ("/", Nil, (DenseVector(MDouble),MFloat) :: DenseVector(MDouble)) implements composite ${ densevector_div[Double]($0.toDouble,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MDouble),MDouble) :: DenseVector(MDouble)) implements composite ${ densevector_div[Double]($0,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MInt),DenseVector(MInt)) :: DenseVector(MInt)) implements composite ${ densevector_div[Int]($0,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MInt),DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_div[Float]($0.toFloat,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MInt),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_div[Double]($0.toDouble,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MFloat),DenseVector(MInt)) :: DenseVector(MFloat)) implements composite ${ densevector_div[Float]($0,$1.toFloat) }
    infix (DenseVector) ("/", Nil, (DenseVector(MFloat),DenseVector(MFloat)) :: DenseVector(MFloat)) implements composite ${ densevector_div[Float]($0,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MFloat),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_div[Double]($0.toDouble,$1) }
    infix (DenseVector) ("/", Nil, (DenseVector(MDouble),DenseVector(MInt)) :: DenseVector(MDouble)) implements composite ${ densevector_div[Double]($0,$1.toDouble) }
    infix (DenseVector) ("/", Nil, (DenseVector(MDouble),DenseVector(MFloat)) :: DenseVector(MDouble)) implements composite ${ densevector_div[Double]($0,$1.toDouble) }
    infix (DenseVector) ("/", Nil, (DenseVector(MDouble),DenseVector(MDouble)) :: DenseVector(MDouble)) implements composite ${ densevector_div[Double]($0,$1) }    
  }
}