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
    case a: Term.App => getFreeReqsTerm(a.lhs) ++ getFreeReqsTerm(a.rhs)
    case ta: Term.TyApp => getFreeReqsTerm(ta.lhs) ++ ta.targs.flatMap(getFreeReqsTerm)
    case s: Term.Sel => getFreeReqsTerm(s.prefix)
    case s: Term.SynthSel => getFreeReqsTerm(s.prefix)
    case s: Term.DynSel => getFreeReqsTerm(s.prefix)
    case t: Term.Tup => t.fields.flatMap(f => f.subTerms.flatMap(getFreeReqsTerm)).toSet
    case t: Term.CtxTup => t.fields.flatMap(f => f.subTerms.flatMap(getFreeReqsTerm)).toSet
    case i: Term.IfLike => i.desugared.subTerms.flatMap(getFreeReqsTerm).toSet
    case l: Term.Lam => l.body.subTerms.flatMap(getFreeReqsTerm).toSet
    case f: Term.FunTy => f.lhs.subTerms.flatMap(getFreeReqsTerm).toSet ++ f.rhs.subTerms.flatMap(getFreeReqsTerm).toSet
    case f: Term.Forall => f.body.subTerms.flatMap(getFreeReqsTerm).toSet
    case w: Term.WildcardTy => w.in.toList.flatMap(getFreeReqsTerm).toSet ++ w.out.toList.flatMap(getFreeReqsTerm).toSet
    case b: Term.Blk => b.stats.flatMap(getFreeReqsStatement).toSet ++ getFreeReqsTerm(b.res)
    case r: Term.Rcd => r.stats.flatMap(getFreeReqsStatement).toSet
    case q: Term.Quoted => getFreeReqsTerm(q.body)
    case u: Term.Unquoted => getFreeReqsTerm(u.body)
    case n: Term.New => getFreeReqsTerm(n.cls) ++ n.argss.flatten.flatMap(getFreeReqsTerm).toSet
    case sp: Term.SelProj => getFreeReqsTerm(sp.prefix) ++ getFreeReqsTerm(sp.cls)
    case a: Term.Asc => getFreeReqsTerm(a.term) ++ getFreeReqsTerm(a.ty)
    case c: Term.CompType => getFreeReqsTerm(c.lhs) ++ getFreeReqsTerm(c.rhs)
    case n: Term.Neg => getFreeReqsTerm(n.rhs)
    case r: Term.Region => getFreeReqsTerm(r.body)
    case r: Term.RegRef => getFreeReqsTerm(r.reg) ++ getFreeReqsTerm(r.value)
    case a: Term.Assgn => getFreeReqsTerm(a.lhs) ++ getFreeReqsTerm(a.rhs)
    case d: Term.Deref => getFreeReqsTerm(d.ref)
    case s: Term.SetRef => getFreeReqsTerm(s.ref) ++ getFreeReqsTerm(s.value)
    case r: Term.Ret => getFreeReqsTerm(r.result)
    case t: Term.Throw => getFreeReqsTerm(t.result)
    case t: Term.Try => getFreeReqsTerm(t.body) ++ getFreeReqsTerm(t.finallyDo)
    case a: Term.Annotated => getFreeReqsTerm(a.target)
    case h: Term.Handle => h.rhs.subTerms.flatMap(getFreeReqsTerm).toSet ++ h.args.flatMap(getFreeReqsTerm).toSet ++ getFreeReqsTerm(h.body)
    case Term.Error | Term.UnitVal() | Term.Missing | Term.Lit(_) => Set.empty

  def getFreeReqsStatement(s: Statement)(using FieldSymbol): Set[FieldSymbol] =
    s.subTerms.flatMap(getFreeReqsTerm).toSet

  def getAbstracts(cls: ClassLikeDef): Map[Ls[FieldSymbol], (Ls[TraitSymbol], Opt[Require], Ls[TermDefinition])] =
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
    cls match
      case t: TraitDef => t.deps = t.deps ++ deps
      case _ =>

    tl.log(s"requires: ${requires.keys.mkString(", ")}")

    val abstracts = cls.body.blk.stats.collect:
      case td: TermDefinition if td.body is N => td

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
              p.impReqs = p.impReqs + req
            case None => raise:
                ErrorReport:
                  msg"Implementation ${p.sym.nme} requires trait ${r.nme}, but ${cls.sym.nme} does not" -> p.toLoc :: Nil
        
        trmToPath(sel) -> (tds, p)
    .toMap

    def findMostSpecificImpl(path: Ls[FieldSymbol]): Option[(Ls[TermDefinition], TraitDef)] =
      tl.log(s"Finding most specific impl for path: ${path}")
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
            tl.log(s"Found impl for ${reqPath.mkString(".")}: ${implOpt.get._2.sym.nme}")
            val (tds, implTrait) = implOpt.get
            val filtered = abs.filterNot(td => tds.exists(checkImplsSat(td)))
            (or, filtered) match
              case (S(r), Nil) => 
                tl.log(s"Trait ${implTrait.sym.nme} completes all abstract members of ${r.path}")
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
    tl.log(s"================================")
    tl.log(s"Class = ${cls.sym.nme}")
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
    val clss = stmts.collect:
      case c: ClassLikeDef => c

    sortClss(clss).foreach: c =>
      resolveRequires(c)
      resolve(c.body.blk.stats.filter(s => 
        !s.isInstanceOf[TraitDef] || s.asInstanceOf[TraitDef].kind != Imp)
      )
