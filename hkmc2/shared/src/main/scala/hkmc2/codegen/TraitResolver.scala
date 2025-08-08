package hkmc2
package codegen

import scala.collection.mutable
import mlscript.utils.*, shorthands.*
import utils.*
import semantics.Elaborator.State
import semantics.*

import hkmc2.Message.MessageContext

import java.io.StringWriter
import java.io.PrintWriter
import hkmc2.syntax.Imp
import hkmc2.syntax.Tree
import hkmc2.semantics.ClassDef.Plain

def appendMaps[K, V](m1: Map[K, V], m2: Map[K, V]): Map[K, V] =
  m2.foldLeft(m1) {
    case (acc, (k, v)) =>
      acc.updatedWith(k) {
        case Some(existing) =>
          assert(v.equals(existing))
          Some(existing)
        case None => Some(v)
      }
  }

class TraitResolver(using Raise):

  def getAbstracts(cls: ClassLikeDef, childSym: Symbol): Map[TraitSymbol, Map[Symbol, Ls[TermDefinition]]] =
    println("------------")
    
    val requires = cls.body.blk.stats.collect {
      case r: Require => r
    }.foldLeft(Map.empty[TraitSymbol, Map[Symbol, Ls[TermDefinition]]])((acc, r) => r.inheritedAbstract.foldLeft(acc) {
      case (acc, (trt, map)) =>  acc.updatedWith(trt) {
        case Some(existing) => Some(appendMaps(existing, map))
        case None => Some(map)
      }
    })
    println(s"requires: $requires")

    val abstracts = cls.body.blk.stats.collect {
      case td: TermDefinition if td.body is N => td
    }
    println(s"abstracts: $abstracts")

    val impls: Ls[(TraitSymbol, Symbol, Ls[TermDefinition], Plain)] = cls.body.blk.stats.collect {
      case p: Plain if p.trt.nonEmpty => 
        // TODO: handle N properly
        val path = p.trt.get
        val trtSym = (path match
          case t: Term.Ref => t.sym
          case t: Term.Sel => t.sym.get
          case t: Term.SynthSel => t.sym.get
          case _ => ???).asTrt.get
        def nthChild(path: Term, n: Int): Symbol = 
          if n == 0 then path match
            case t: Term.Ref => t.sym
            case t: Term.Sel => t.sym.get
            case t: Term.SynthSel => t.sym.get
            case _ => ???
          else path match
            case Term.Ref(_) => cls.sym
            case Term.Sel(pre, _) => nthChild(pre, n - 1)
            case Term.SynthSel(pre, _) => nthChild(pre, n - 1)
            case _ => ???
        val tds = p.body.blk.stats.collect {
          case td: TermDefinition if td.body.nonEmpty => td
        }
        val childSym = nthChild(path, 1).asClsOrModOrTrt.get
        (trtSym, childSym, tds, p)
    }
    println(s"impls: $impls")

    def checkImplsSat(abs: TermDefinition)(imp: TermDefinition) = abs.sym.nme == imp.sym.nme
    val updatedRequires = impls.foldLeft(requires):
      case (acc, (trtSym, childSym, tds, p)) =>
        acc.updatedWith(trtSym):
          case S(childToAbs) => S(childToAbs.updatedWith(childSym):
            case S(abs) => S(abs.filterNot(a => tds.exists(checkImplsSat(a))))
            case N => (raise:
              ErrorReport:
                msg"Implemented trait is not required" -> p.toLoc :: Nil); N
          ) 
          case N => (raise:
            ErrorReport:
              msg"Implemented trait is not required" -> p.toLoc :: Nil); N

    cls match
      case t: TraitDef => updatedRequires.updated(cls.sym.asTrt.get, Map(childSym -> abstracts))
      case _ => updatedRequires


  def resolveRequires(cls: ClassLikeDef) =
    cls match
      case p: Plain if p.trt.nonEmpty =>
      case _ =>
        println("=============")
        println(cls.sym)
        cls.body.blk.stats.foreach {
          case r: Require =>
            // TODO: handle N properly
            val traitDefn = r.mod.defn.get
            val map = getAbstracts(traitDefn, cls.sym)
            r.inheritedAbstract = map
          case _ =>
        }
        val ownAbstracts = getAbstracts(cls, cls.sym)
        println("Own abstracts:")
        println(ownAbstracts)
        cls match
          case t: TraitDef =>
          case _ =>
            ownAbstracts.foreach((ts, map) => map.foreach((chld, abs) => 
              if abs.nonEmpty then
                raise:
                  ErrorReport:
                    msg"Concrete ${cls.sym.nme} does not implement all abstract members of trait ${ts.nme}: ${abs.map(_.sym.nme).mkString(", ")}" -> cls.toLoc :: Nil
            ))

  def resolve(stmts: Ls[Statement]): Unit =
    for stmt <- stmts do
      stmt match 
      case c: ClassLikeDef => 
        resolveRequires(c)
        resolve(c.body.blk.stats)
      case _ => // ignore other statements
