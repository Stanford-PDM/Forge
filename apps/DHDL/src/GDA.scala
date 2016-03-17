import dhdl.compiler._
import dhdl.library._
import dhdl.shared._
import scala.util.Random

// TODO: How to optimize automatically when cTileSize == cols?
object GDACompiler extends DHDLApplicationCompiler with GDA
object GDAInterpreter extends DHDLApplicationInterpreter with GDA
trait GDA extends DHDLApplication {

  type Elem = Fix

  override def stageArgNames = List("rTileSize", "cTileSize")
  lazy val rTileSize = stageArgOrElse[Int](0, 2)
  lazy val cTileSize = stageArgOrElse[Int](1, 4)
  lazy val rows = ArgIn[Fix]("rows")
  lazy val cols = ArgIn[Fix]("cols")

  def gda(
    x: Rep[OffChipMem[Elem]],
    y: Rep[OffChipMem[Bit]],
    mu0: Rep[OffChipMem[Elem]],
    mu1: Rep[OffChipMem[Elem]],
    sigma: Rep[OffChipMem[Elem]]
  ) {
    val sub = OffChipMem[Elem]("sub", cols)

    MetaPipe(rows by rTileSize){ r =>
      val yTile = BRAM[Bit]("yTile", rTileSize)
      y.ld(yTile, r, rTileSize)

      Sequential(rTileSize by 1){ rr =>
        MetaPipe(cols by cTileSize){ c =>
          val xTile = BRAM[Elem]("xTile", rTileSize, cTileSize)
          val mu0Tile = BRAM[Elem]("mu0Tile", cTileSize)
          val mu1Tile = BRAM[Elem]("mu1Tile", cTileSize)
          Parallel {
            x.ld(xTile, r, c, rTileSize, cTileSize) // Load a tile of x
            mu0.ld(mu0Tile, c, cTileSize)           // Load a tile of mu0
            mu1.ld(mu1Tile, c, cTileSize)           // Load a tile of mu1
          }
          val subTile = BRAM[Elem]("subTemp", cTileSize)
          Pipe(cTileSize by 1){ cc =>
            subTile(cc) = xTile(rr,cc) - mux(yTile(rr), mu1Tile(cc), mu0Tile(cc))
          }
          sub.st(subTile, c, cTileSize)
        }
        MetaPipe(cols by cTileSize, cols by cTileSize){ (i,j) =>
          val subTile1 = BRAM[Elem]("subTile1", cTileSize)
          val subTile2 = BRAM[Elem]("subTile2", cTileSize)
          val sigmaTile = BRAM[Elem]("sigmaTile", cTileSize, cTileSize)
          Parallel {
            sub.ld(subTile1, i, cTileSize)
            sub.ld(subTile2, j, cTileSize)
            sigma.ld(sigmaTile, i, j, cTileSize, cTileSize)
          }
          Pipe(cTileSize by 1, cTileSize by 1){ (ii,jj) =>
            sigmaTile(ii,jj) = sigmaTile(ii,jj) + subTile1(ii) * subTile2(jj)
          }
          sigma.st(sigmaTile, i, j, cTileSize, cTileSize)
        }
      }
    }
  }

  def main() {
    val R = 6
    val C = 8

    val x = OffChipMem[Elem]("x", R, C)
    val y = OffChipMem[Bit]("y", R)
    val mu0 = OffChipMem[Elem]("mu0", C)
    val mu1 = OffChipMem[Elem]("mu1", C)
    val sigma = OffChipMem[Elem]("sigma", C, C)

    val sX = Array.fill(R){ Array.fill(C){ randomFix(10) }} //Array.tabulate(C){j => random[Flt] * 100.0f }}
    val sY = Array.fill(R){ random[Bit] }
    val sMu0 = Array.fill(C){ randomFix(10) }
    val sMu1 = Array.fill(C){ randomFix(10) }

    println("x: " + sX.map(_.mkString(", ")).mkString("\n") )
    println("y: " + sY.mkString("\n"))
    println("mu0: " + sMu0.mkString(", "))
    println("mu1: " + sMu1.mkString(", "))

    // Transfer data and start accelerator
    setArg(rows, R)
    setArg(cols, C)
    setMem(x, sX.flatten)
    setMem(y, sY)
    setMem(mu0, sMu0)
    setMem(mu1, sMu1)
    Accel{ gda(x, y, mu0, mu1, sigma) }

    val gold = sX.zip(sY){ (row, y) =>
      val sub = if (y) row.zip(sMu1){_-_} else row.zip(sMu0){_-_}
      Array.tabulate(C){i => Array.tabulate(C){j => sub(i) * sub(j) }}.flatten
    }.reduce{(a,b) => a.zip(b){_+_}}

    val result = getMem(sigma)

    val xFlattened = getMem(x)
    println("x: ")
    println(xFlattened.mkString(", "))

    println("expected: " + gold.mkString(", "))
    println("result:   " + result.mkString(", "))
    println("diff:     " + gold.zip(result){_-_}.mkString(", "))
    assert( result == gold )
  }
}