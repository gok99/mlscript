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

class TraitResolver(using Raise, TraceLogger, State):
  
  val tl = summon[TraceLogger]

  def sortClss(clss: Ls[ClassLikeDef]): Ls[ClassLikeDef] =
    val requires = clss.flatMap: cls =>
      cls.body.blk.stats.collect:
        case r: Require => (cls.sym, r.mod)
    val sortedClss = clss.sortWith: (ca, cb) =>
      ca.sym match
        case ts: TraitSymbol => requires.contains((cb.sym, ts))
        case _ => false
    return sortedClss

  def getFreeReqsTerm(s: Term)(using FieldSymbol): Set[FieldSymbol] = s match
    case r: Term.Ref => r.sym.asClsOrModOrTrt.toSet.filter(s => s.isInstanceOf[TraitSymbol] || s == summon[FieldSymbol])
    case e => e.subTerms.toSet.flatMap(getFreeReqsTerm)

  def getFreeReqsStatement(s: Statement)(using FieldSymbol): Set[FieldSymbol] =
    s.subTerms.flatMap(getFreeReqsTerm).toSet

  def getAbstracts(cls: ClassLikeDef): Map[Ls[FieldSymbol], (Ls[TraitSymbol], Opt[Require], Ls[TermDefinition], Ls[TermDefinition])] =
    var deps = Set.empty[TraitSymbol]
    val rs = cls.body.blk.stats.collect:
      case r: Require =>
        // update trait's deps
        r.mod.defn.foreach(tdep => deps = deps ++ tdep.deps + r.mod)
        if r.mod.defn.flatMap(trt => cls.sym.asTrt.map(thisTrt => trt.deps.contains(thisTrt))).getOrElse(false)
        then raise:
          ErrorReport:
            msg"Trait ${cls.sym.nme} cannot require trait ${r.mod.nme} that (transitively) depends on ${cls.sym.nme}" -> r.toLoc :: Nil
        r
    val requires = rs
    .foldLeft(Map.empty[Ls[FieldSymbol], (Ls[TraitSymbol], Opt[Require], Ls[TermDefinition], Ls[TermDefinition])]): (acc, r) =>
      val inherited = r.mod.defn.flatMap(_.abs).getOrElse(Map.empty)
      inherited.foldLeft(acc):
        case (acc, (path, (implPath, or, abs, con))) =>
          val req: Opt[Require] = or match
            case Some(r) => Some(r)
            case None => Some(r)
          acc.updatedWith(cls.sym :: path):
            case Some(implPath, N, abs, con) => Some(implPath, req, abs, con)
            case Some(stuff) => Some(stuff) // is case be necessary?
            case None => Some(implPath, req, abs, con)
    cls match
      case t: TraitDef => t.deps = t.deps ++ deps
      case _ =>

    tl.log(s"requires: ${requires.keys.mkString(", ")}")

    val (abstracts, concrete) = cls.body.blk.stats.collect:
      case td: TermDefinition => td
    .partition(_.body.isEmpty)

    val impls: Map[Ls[FieldSymbol], (Ls[TermDefinition], TraitDef)] = cls.body.blk.stats.collect:
      case p: TraitDef if p.kind == Imp =>
        // check that free vars are ok
        val freeReqs = getFreeReqsStatement(p)(using cls.sym) - p.sym

        val sel = p.trt
        def trmToPath(trm: Term): Ls[FieldSymbol] = trm match
          case r: Term.Ref => r.sym.asClsOrModOrTrt.get :: Nil
          case s @ Term.Sel(pre, _) => trmToPath(pre) :+ s.sym.get.asClsOrModOrTrt.get
          case s @ Term.SynthSel(pre, _) => trmToPath(pre) :+ s.sym.get.asClsOrModOrTrt.get
          case _ => ???
        val tds = p.body.blk.stats.collect:
          case td: TermDefinition if td.body.nonEmpty => td
        val path = trmToPath(sel)
        
        // check impl free vars
        val trt = path.last
        freeReqs.foreach: r =>
          val (cdeps, name) = r match
            case t: TraitSymbol => (t.defn.get.deps + t, t.nme)
            case c: ClassLikeSymbol if c == cls.sym => (deps, c.nme)
            case _ => ???
          
          if cdeps.contains(trt.asTrt.get)
          then raise:
            ErrorReport:
              msg"Implementation has an implicit requirement on ${name}, but ${name} (transitively) depends on trait ${trt.nme}" -> p.toLoc :: Nil
          else rs.find(_.mod == r) match
            case Some(req) =>
              val t: FieldSymbol -> Require = (cls.sym, req)
              p.impReqs = p.impReqs + t
            case None => raise:
                ErrorReport:
                  msg"Implementation ${p.sym.nme} requires trait ${r.nme}, but ${cls.sym.nme} does not" -> p.toLoc :: Nil
        
        trmToPath(sel) -> (tds, p)
    .toMap

    var unusedTraits = impls.values.map(_._2).toSet

    def findMostSpecificImpl(path: Ls[FieldSymbol]): Option[(Ls[TermDefinition], TraitDef)] =
      tl.log(s"Finding most specific impl for path: ${path}")
      if impls.contains(path)
        then Some(impls(path))
        else if path.tail.nonEmpty then findMostSpecificImpl(path.tail)
        else None
    def checkImplsSat(abs: TermDefinition)(imp: TermDefinition) = abs.sym.nme == imp.sym.nme
    val updatedRequires: Map[Ls[FieldSymbol], (Ls[TraitSymbol], Opt[Require], Ls[TermDefinition], Ls[TermDefinition])] = requires.foldLeft(Map.empty):
      case (acc, (reqPath, (implPath, or, abs, con))) =>
        if abs.nonEmpty then
          val implOpt = findMostSpecificImpl(reqPath)
          val res = if implOpt.nonEmpty
          then
            tl.log(s"Found impl for ${reqPath.mkString(".")}: ${implOpt.get._2.sym.nme}")
            val (tds, implTrait) = implOpt.get
            if tds.exists(imp => con.exists(crt => imp.sym.nme == crt.sym.nme))
            then // does not implement homogenously, skip
              (implPath, or, abs, con)
            else
              val filtered = abs.filterNot(td => tds.exists(checkImplsSat(td)))
              unusedTraits = unusedTraits - implTrait
              (or, filtered) match
                case (S(r), Nil) => 
                  tl.log(s"Trait ${implTrait.sym.nme} completes all abstract members of ${r.path}")
                  r.implPath = r.implPath.updated(reqPath, (implTrait.sym :: implPath).reverse)
                case _ => 
              (implTrait.sym :: implPath, or, filtered, con ++ tds)
          else (implPath, or, abs, con)
          acc.updated(reqPath, res)
        else acc.updated(reqPath, (implPath, or, abs, con))

    unusedTraits.foreach: t =>
      raise:
        ErrorReport:
          msg"Trait ${t.sym.nme} is unused" -> t.toLoc :: Nil

    cls match
      case t: TraitDef =>
        val value = (Nil, N, abstracts, concrete)
        updatedRequires.updated(cls.sym.asTrt.get :: Nil, value)
      case _ => updatedRequires

  def resolveRequires(cls: ClassLikeDef) =
    tl.log(s"================================")
    tl.log(s"Class = ${cls.sym.nme}")
    val ownAbstracts = getAbstracts(cls)
    cls.abs = S(ownAbstracts)
    cls match
      case t: TraitDef =>
      case _ =>
        ownAbstracts.foreach:
          case (ts, (td, _, abs, con)) =>
            if abs.nonEmpty then
              raise:
                ErrorReport:
                  msg"Concrete ${cls.sym.nme} does not implement all abstract members of trait ${ts.last.nme}: ${abs.map(_.sym.nme).mkString(", ")}" -> cls.toLoc :: Nil

  def resolve(stmts: Ls[Statement]): Unit =
    val clss = stmts.collect:
      case c: ClassLikeDef => c

    sortClss(clss).foreach: c =>
      resolveRequires(c)
      resolve(c.body.blk.stats.filter(s => 
        !s.isInstanceOf[TraitDef] || s.asInstanceOf[TraitDef].kind != Imp)
      )
