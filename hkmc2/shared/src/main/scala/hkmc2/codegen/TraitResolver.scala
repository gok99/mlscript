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

/**
 * Draft of trait constraint resolution
 */

object TraitResolver:

  case class TCtx(roots: Set[Symbol], nodeOfSymbol: Map[Symbol, Node]):
    def addRoot(sym: Symbol): TCtx =
      this.copy(roots = this.roots + sym)
    def removeRoot(sym: Symbol): TCtx =
      this.copy(roots = this.roots - sym)
    def updateMap(sym: Symbol, node: Node): TCtx =
      this.copy(nodeOfSymbol = this.nodeOfSymbol.updated(sym, node))

  object TCtx:
    val empty = TCtx(Set.empty, Map.empty)

  def tctx(using TCtx) = summon[TCtx]

  case class Node(symbol: Symbol, parents: Ls[Node], children: Ls[Node], 
    virtuals: Ls[TermDefinition], propVirtuals: Ls[TermDefinition], implementations: Ls[TermDefinition]):

    def addChild(child: Node): Node =
      copy(children = child :: children)

    def setVirtuals(virtuals: Ls[TermDefinition]): Node =
      copy(virtuals = virtuals)

    def setPropVirtuals(propVirtuals: Ls[TermDefinition]): Node =
      copy(propVirtuals = propVirtuals)

    def setImplementations(implementations: Ls[TermDefinition]): Node =
      copy(implementations = implementations)

    def addParent(parent: Node): Node =
      copy(parents = parent :: parents)

    def unimplementedVirtuals: Ls[TermDefinition] =
      // should check types
      (virtuals ++ propVirtuals).filter(v => implementations.forall(i => i.sym.nme != v.sym.nme))

    def isRoot: Bool = parents.isEmpty
  
  // Graph management

  def addNode(sym: Symbol)(using ctx: TCtx): TCtx =
    var tctx = ctx
    val node = Node(sym, Nil, Nil, Nil, Nil, Nil)
    tctx = tctx.addRoot(sym)
    tctx.updateMap(sym, node)

  def addParentDetail(sym: Symbol, parent: Symbol)(using ctx: TCtx): TCtx =
    var tctx = ctx
    val parentNode = tctx.nodeOfSymbol.getOrElse(parent, {
      tctx = addNode(parent)(using tctx)
      tctx.nodeOfSymbol.get(parent).get
    })
    val childNode = tctx.nodeOfSymbol.getOrElse(sym, {
      tctx = addNode(sym)(using tctx)
      tctx.nodeOfSymbol.get(sym).get
    })

    val newChildNode = childNode.addParent(parentNode)
    val newParentNode = parentNode.addChild(childNode)
    
    tctx = tctx.updateMap(sym, newChildNode)
    tctx = tctx.updateMap(parent, newParentNode)

    if !tctx.roots.contains(parent) && newParentNode.isRoot then
      tctx = tctx.addRoot(parent)

    if tctx.roots.contains(sym) then
      tctx = tctx.removeRoot(sym)

    tctx

  def setVirtuals(sym: Symbol, virtuals: Ls[TermDefinition])(using ctx: TCtx): TCtx =
    var tctx = ctx
    val node = tctx.nodeOfSymbol.getOrElse(sym, {
      tctx = addNode(sym)(using tctx)
      tctx.nodeOfSymbol.get(sym).get
    })
    val newNode = node.setVirtuals(virtuals)
    tctx.updateMap(sym, newNode)

  def setImplementations(sym: Symbol, implementations: Ls[TermDefinition])(using ctx: TCtx): TCtx =
    var tctx = ctx
    val node = tctx.nodeOfSymbol.getOrElse(sym, {
      tctx = addNode(sym)(using tctx)
      tctx.nodeOfSymbol.get(sym).get
    })
    println(s"Setting implementations for $sym: ${implementations.map(_.sym.nme).mkString(", ")}")
    val newNode = node.setImplementations(implementations)
    tctx.updateMap(sym, newNode)

  // Queries (TODO)
  // Types of queries we need to support:
  // 1. What is the symbol for the trait that is required by this ClsLike?
  // 2. What is the path for the implementation?
  
  

  // Graph check
  // Things we need to check:
  // 1. Concrete classes implement all abstract fields
  // 2. If equality constraint are specified, paths must be parents (TODO)
  // 3. Constraint is placed on 2 upstream traits that already both have implementations (TODO)
  
  def propagateVirtuals()(using ctx: TCtx): TCtx =
    var ctxt = ctx
    val roots = ctxt.roots
    val visited = mutable.Set[Symbol]()
    def visit(node: Node): Unit =
      println(s"Visiting node: ${ppNode(node)}")
      visited += node.symbol
      val unimplementedVirtuals = node.unimplementedVirtuals
      for childp <- node.children do
        val child = ctxt.nodeOfSymbol.get(childp.symbol).get
        if unimplementedVirtuals.nonEmpty then
          val newChildNode = child.setPropVirtuals(child.propVirtuals ++ unimplementedVirtuals)
          ctxt = ctxt.updateMap(child.symbol, newChildNode)
        println(s"Child: ${child.symbol.nme} has unimplemented virtuals: ${unimplementedVirtuals.map(_.sym.nme).mkString(", ")}")
        if child.parents.forall(p => 
          println(s"Checking parent: ${p.symbol.nme} for child: ${child.symbol.nme} -> visited: ${visited.contains(p.symbol)}")
          visited.contains(p.symbol)) then
          visit(child)

    roots.foreach(sym => visit(ctxt.nodeOfSymbol.get(sym).get))
    ctxt

  def checkVirtuals()(using ctx: TCtx, raise: Raise) : Unit = 
    ctx.nodeOfSymbol.values.foreach { node =>
      if !node.symbol.isInstanceOf[TraitSymbol] && node.unimplementedVirtuals.nonEmpty then
        var loc = node.symbol.toLoc
        raise:
          ErrorReport:
                msg"Concrete class contains virtual fields: ${node.unimplementedVirtuals.map(_.sym.nme).distinct.mkString(", ")}" -> loc :: Nil
    }

  def ppCtx()(using ctx: TCtx): Str =
    val sb = new StringBuilder
    sb.append(s"TCtx:\n")
    sb.append(s"  Roots: ${ctx.roots.map(_.nme).mkString(", ")}\n")
    sb.append(s"  Nodes:\n")
    ctx.nodeOfSymbol.foreach { case (sym, node) =>
      sb.append(ppNode(node))
    }
    sb.toString()
  
  def ppNode(node: Node): Str =
    val sb = new StringBuilder
    sb.append(s"Node(${node.symbol}):\n")
    sb.append(s"  Parents: ${node.parents.map(_.symbol).mkString(", ")}\n")
    sb.append(s"  Children: ${node.children.map(_.symbol).mkString(", ")}\n")
    sb.append(s"  Virtuals: ${node.virtuals.map(_.sym.nme).mkString(", ")}\n")
    sb.append(s"  PropVirtuals: ${node.propVirtuals.map(_.sym.nme).mkString(", ")}\n")
    sb.append(s"  Implementations: ${node.implementations.map(_.sym.nme).mkString(", ")}\n")
    sb.toString()

class TraitResolver(using TL, Raise, State, TraitResolver.TCtx):
  import TraitResolver.*

  def traverseTrt(trt: TraitDef)(using ctx: TCtx): TCtx =
    var ctxt = ctx
    val stmts = trt.body.blk.stats
    val absFields = trt.body.blk.stats.collect {
      case f: TermDefinition if f.body is None => f
    }
    ctxt = setVirtuals(trt.sym, absFields)(using ctxt)
    traverseCls(trt)(using ctxt)

  def traverseCls(cls: ClassLikeDef)(using ctx: TCtx): TCtx =
    var ctxt = ctx
    val stmts = cls.body.blk.stats
    val (reqs, imps) = stmts.foldRight(Nil: Ls[Require], Nil: Ls[Statement]): (stmt, p) =>
      val (reqs, imps) = p
      stmt match
        case r: Require => (r :: reqs, imps)
        case i: ClassDef.Plain if i.kind == Imp => (reqs, i.body.blk.stats ::: imps)
        case _ => (reqs, imps)
    reqs.foreach(r => ctxt = addParentDetail(cls.sym, r.mod)(using ctxt))
    imps.foreach(i => ctxt = setImplementations(cls.sym, imps.collect {
      case t: TermDefinition => t
    })(using ctxt))
    resolve(stmts)(using ctxt)

  def resolve(stmts: Ls[Statement])(using ctx: TCtx): TCtx = 
    var ctxt = ctx
    // collect Require stmts and Imp Plain stmts, 
    // from ClsLikeKinds
    for stmt <- stmts do
      stmt match 
      case t: TraitDef => ctxt = traverseTrt(t)(using ctxt)
      case c: ClassLikeDef => ctxt = traverseCls(c)(using ctxt)
      case _ => // ignore other statements
    ctxt

  def resolveAndCheck(stmts: Ls[Statement])(using ctx: TCtx): TCtx =
    println("==========Checking Traits==========")
    var ctxt = resolve(stmts)(using ctx)
    println(ppCtx()(using ctxt))
    println("=====")
    
    // run check!
    ctxt = propagateVirtuals()(using ctxt)
    println(ppCtx()(using ctxt))
    checkVirtuals()(using ctxt)
    // stmts
    ctxt
