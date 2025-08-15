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

class TraitResolver(using Raise):

  def getAbstracts(cls: ClassLikeDef): Map[Ls[FieldSymbol], Ls[TermDefinition]] =    
    val requires = cls.body.blk.stats.collect:
      case r: Require => r
    .foldLeft(Map.empty[Ls[FieldSymbol], Ls[TermDefinition]]): (acc, r) =>
      r.inheritedAbstract.foldLeft(acc):
        case (acc, (path, tds)) =>
          acc.updatedWith(cls.sym :: path):
            case Some(tds) => Some(tds)
            case None => Some(tds)

    val abstracts = cls.body.blk.stats.collect {
      case td: TermDefinition if td.body is N => td
    }

    val impls: Map[Ls[FieldSymbol], (Ls[TermDefinition], Plain)] = cls.body.blk.stats.collect {
      case p: Plain if p.trt.nonEmpty =>
        // TODO: handle N properly
        val sel = p.trt.get
        def trmToPath (trm: Term): Ls[FieldSymbol] = trm match
          case r: Term.Ref => r.sym.asClsOrModOrTrt.get :: Nil
          case s @ Term.Sel(pre, _) => trmToPath(pre) :+ s.sym.get.asClsOrModOrTrt.get
          case s @ Term.SynthSel(pre, _) => trmToPath(pre) :+ s.sym.get.asClsOrModOrTrt.get
          case _ => ???
        val tds = p.body.blk.stats.collect:
          case td: TermDefinition if td.body.nonEmpty => td
        trmToPath(sel) -> (tds, p)
    }.toMap

    def findMostSpecificImpl(path: Ls[FieldSymbol]): Option[(Ls[TermDefinition], Plain)] =
      if impls.contains(path)
        then Some(impls(path))
        else if path.tail.nonEmpty then findMostSpecificImpl(path.tail)
        else None
    def checkImplsSat(abs: TermDefinition)(imp: TermDefinition) = abs.sym.nme == imp.sym.nme
    val updatedRequires: Map[Ls[FieldSymbol], Ls[TermDefinition]] =
      requires.foldLeft(Map.empty):
        case (acc, (reqPath, tds)) =>
          val implOpt = findMostSpecificImpl(reqPath)          
          val implTds = if implOpt.nonEmpty
          then
            val (tds, p) = implOpt.get
            p.implementingTraits = reqPath :: p.implementingTraits
            tds
          else Nil
          val filteredTds = tds.filterNot(td => implTds.exists(checkImplsSat(td)))
          acc.updated(reqPath, filteredTds)

    cls match
      case t: TraitDef => updatedRequires.updated(cls.sym.asTrt.get :: Nil, abstracts)
      case _ => updatedRequires

  def resolveRequires(cls: ClassLikeDef) =
    println(s"================================")
    println(s"Class = ${cls.sym.nme}")
    cls match
      case p: Plain if p.trt.nonEmpty =>
      case _ =>
        cls.body.blk.stats.foreach:
          case r: Require =>
            // TODO: handle N properly
            val traitDefn = r.mod.defn.get
            val map = traitDefn.abs // getAbstracts(traitDefn)
            r.inheritedAbstract = map.getOrElse(Map.empty)
          case _ =>
        val ownAbstracts = getAbstracts(cls)
        println(ownAbstracts)
        cls.abs = S(ownAbstracts)
        cls match
          case t: TraitDef =>
          case _ =>
            ownAbstracts.foreach((ts, abs) =>
              if abs.nonEmpty then
                raise:
                  ErrorReport:
                    msg"Concrete ${cls.sym.nme} does not implement all abstract members of trait ${ts.last.nme}: ${abs.map(_.sym.nme).mkString(", ")}" -> cls.toLoc :: Nil
            )

  def resolve(stmts: Ls[Statement]): Unit =
    for stmt <- stmts do
      stmt match 
      case c: ClassLikeDef => 
        resolveRequires(c)
        resolve(c.body.blk.stats)
      case _ => // ignore other statements
