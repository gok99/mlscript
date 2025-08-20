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

object TraitLifter

class TraitResolver(using Raise):

  def getAbstracts(cls: ClassLikeDef): Map[Ls[FieldSymbol], (Ls[TraitSymbol], Opt[Require], Ls[TermDefinition])] =
    val requires = cls.body.blk.stats.collect:
      case r: Require => r
    .foldLeft(Map.empty[Ls[FieldSymbol], (Ls[TraitSymbol], Opt[Require], Ls[TermDefinition])]): (acc, r) =>
      val inherited = r.mod.defn.flatMap(_.abs).getOrElse(Map.empty)
      inherited.foldLeft(acc):
        case (acc, (path, (implPath, or, abs))) =>
          val req: Opt[Require] = or match
            case Some(r) => Some(r)
            case None => Some(r)
          acc.updatedWith(cls.sym :: path):
            case Some(implPath, N, abs) => Some(implPath, req, abs)
            case Some(stuff) => Some(stuff) // is case be necessary?
            case None => Some(implPath, req, abs)

    println(s"requires: ${requires.keys.mkString(", ")}")

    val abstracts = cls.body.blk.stats.collect:
      case td: TermDefinition if td.body is N => td

    val impls: Map[Ls[FieldSymbol], (Ls[TermDefinition], TraitDef)] = cls.body.blk.stats.collect:
      case p: TraitDef =>
        val sel = p.trt
        def trmToPath(trm: Term): Ls[FieldSymbol] = trm match
          case r: Term.Ref => r.sym.asClsOrModOrTrt.get :: Nil
          case s @ Term.Sel(pre, _) => trmToPath(pre) :+ s.sym.get.asClsOrModOrTrt.get
          case s @ Term.SynthSel(pre, _) => trmToPath(pre) :+ s.sym.get.asClsOrModOrTrt.get
          case _ => ???
        val tds = p.body.blk.stats.collect:
          case td: TermDefinition if td.body.nonEmpty => td
        trmToPath(sel) -> (tds, p)
    .toMap

    def findMostSpecificImpl(path: Ls[FieldSymbol]): Option[(Ls[TermDefinition], TraitDef)] =
      println(s"Finding most specific impl for path: ${path}")
      if impls.contains(path)
        then Some(impls(path))
        else if path.tail.nonEmpty then findMostSpecificImpl(path.tail)
        else None
    def checkImplsSat(abs: TermDefinition)(imp: TermDefinition) = abs.sym.nme == imp.sym.nme
    val updatedRequires: Map[Ls[FieldSymbol], (Ls[TraitSymbol], Opt[Require], Ls[TermDefinition])] = requires.foldLeft(Map.empty):
      case (acc, (reqPath, (implPath, or, abs))) =>
        if abs.nonEmpty then
          val implOpt = findMostSpecificImpl(reqPath)
          val res = if implOpt.nonEmpty
          then
            println(s"Found impl for ${reqPath.mkString(".")}: ${implOpt.get._2.sym.nme}")
            val (tds, implTrait) = implOpt.get
            val filtered = abs.filterNot(td => tds.exists(checkImplsSat(td)))
            (or, filtered) match
              case (S(r), Nil) => 
                println(s"Trait ${implTrait.sym.nme} completes all abstract members of ${r.path}")
                r.implPath = (implTrait.sym :: implPath).reverse
              case _ => 
            (implTrait.sym :: implPath, or, filtered)
          else (implPath, or, abs)
          acc.updated(reqPath, res)
        else acc.updated(reqPath, (implPath, or, abs))

    cls match
      case t: TraitDef =>
        val value = (Nil, N, abstracts)
        updatedRequires.updated(cls.sym.asTrt.get :: Nil, value)
      case _ => updatedRequires

  def resolveRequires(cls: ClassLikeDef) =
    println(s"================================")
    println(s"Class = ${cls.sym.nme}")
    val ownAbstracts = getAbstracts(cls)
    cls.abs = S(ownAbstracts)
    cls match
      case t: TraitDef =>
      case _ =>
        ownAbstracts.foreach:
          case (ts, (td, _, abs)) =>
            if abs.nonEmpty then
              raise:
                ErrorReport:
                  msg"Concrete ${cls.sym.nme} does not implement all abstract members of trait ${ts.last.nme}: ${abs.map(_.sym.nme).mkString(", ")}" -> cls.toLoc :: Nil

  def resolve(stmts: Ls[Statement]): Unit =
    for stmt <- stmts do
      stmt match 
      case c: ClassLikeDef => 
        resolveRequires(c)
        resolve(c.body.blk.stats.filter(s => 
          !s.isInstanceOf[TraitDef] || s.asInstanceOf[TraitDef].kind != Imp)
        )
      case _ => // ignore other statements
