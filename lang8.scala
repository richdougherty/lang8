package com.richdougherty.lang8

package graph {

object Graph {
	type NodeId = Int
	type EdgeId = Int

	case class EdgeData[+E](value: E, from: NodeId, to: NodeId)
	case class NodeData[+N](value: N)
	
	def empty: Graph[Nothing,Nothing] = new Graph(0, Map.empty, Map.empty)
	
	class NodeFocus[+N,+E](val gd: Graph[N,E], val nid: NodeId, val nd: NodeData[N]) {
		def id: NodeId = nid
		def value: N = nd.value
		def unfocus: Graph[N,E] = gd
		def from: Iterable[EdgeFocus[N,E]] = {
			for (e <- unfocus.edges; if (e.from.id == id)) yield e
		}
		def to: Iterable[EdgeFocus[N,E]] = {
			for (e <- unfocus.edges; if (e.to.id == id)) yield e
		}
		def value_=[N1 >: N](newValue: N1): NodeFocus[N1,E] = {
			val nd1 = NodeData(newValue)
			val gd1 = new Graph(gd.nextId, gd.nmap.updated(nid, nd1), gd.emap)
			new NodeFocus(gd1, nid, nd1)
		}
		def add[N1 >: N, E1 >: E](edgeValue: E1, toValue: N1): EdgeFocus[N1,E1] = {
			val eid1 = gd.nextId
			val nid1 = gd.nextId+1
			val ed1 = EdgeData(edgeValue, nid, nid1)
			val nd1 = NodeData(toValue)
			val gd1 = new Graph(gd.nextId+2, gd.nmap.updated(nid1,nd1), gd.emap.updated(eid1,ed1))
			new EdgeFocus(gd1, eid1, ed1)
		}
		def link[E1 >: E](edgeValue: E1, toId: NodeId): EdgeFocus[N,E1] = {
			assert(gd.nmap.contains(toId))
			val eid1 = gd.nextId
			val ed1 = EdgeData(edgeValue, nid, toId)
			val gd1 = new Graph(gd.nextId+1, gd.nmap, gd.emap.updated(eid1,ed1))
			new EdgeFocus(gd1, eid1, ed1)
		}
		def delete: Graph[N,E] = {
			val emap1 = gd.emap.filter { case (eid, ed) => ed.from != nid && ed.to != nid }
			new Graph(gd.nextId, gd.nmap-nid, emap1)
		}
		override def toString = "NodeFocus(" + gd + ", " + nid + ", " + nd + ")"
	}
	class EdgeFocus[+N,+E](val gd: Graph[N,E], val eid: EdgeId, val ed: EdgeData[E]) {
		def id: EdgeId = eid
		def value: E = ed.value
		def unfocus: Graph[N,E] = gd
		def to: NodeFocus[N,E] = unfocus.node(ed.to)
		def from: NodeFocus[N,E] = unfocus.node(ed.from)
		def value_=[E1 >: E](newValue: E1): EdgeFocus[N,E1] = {
			val ed1 = EdgeData(newValue, ed.from, ed.to)
			val gd1 = new Graph(gd.nextId, gd.nmap, gd.emap.updated(eid, ed1))
			new EdgeFocus(gd1, eid, ed1)
		}
		def delete: NodeFocus[N,E] = {
			val gd1 = new Graph(gd.nextId, gd.nmap, gd.emap-eid)
			val nid = ed.from
			new NodeFocus(gd1, nid, gd.nmap(nid))
		}
		override def toString = "EdgeFocus(" + gd + ", " + eid + ", " + ed + ")"
	}

}

import Graph._
class Graph[+N,+E](val nextId: Int, val nmap: Map[NodeId,NodeData[N]], val emap: Map[NodeId,EdgeData[E]]) {

	def node(id: NodeId): NodeFocus[N,E] =
		new NodeFocus(this, id, nmap(id))
	def edge(id: EdgeId): EdgeFocus[N,E] =
		new EdgeFocus(this, id, emap(id))
	def nodes: Iterable[NodeFocus[N,E]] = {
		for ((nid, nd) <- nmap) yield {
			new NodeFocus(this, nid, nd)
		}
	}
	def edges: Iterable[EdgeFocus[N,E]] = {
		for ((eid, ed) <- emap) yield {
			new EdgeFocus(this, eid, ed)
		}
	}
	def addNode[N1 >: N](nodeValue: N1): NodeFocus[N1,E] = {
		val nid = nextId
		val nd = NodeData(nodeValue)
		val gd1 = new Graph(nextId+1, nmap.updated(nid, nd), emap)
		new NodeFocus(gd1, nid, nd)
	}
}

} // package graph


object GraphUtils {
	import graph._
	import Graph._

	case class Tree[+N,+E](nv: N, edges: List[(E, TreeTarget[N,E])])
	trait TreeTarget[+N,+E]
	case class ChildTarget[+N,+E](tree: Tree[N,E]) extends TreeTarget[N,E]
	case class ParentTarget[+N,+E](count: Int) extends TreeTarget[N,E]
	case class ExternalTarget[+N,+E](nid: NodeId) extends TreeTarget[N,E]
	
		def addTree[N,E](g: Graph[N,E], tree: Tree[N,E]): NodeFocus[N,E] = {
		
			def getOrAddTarget(g: Graph[N,E], path: List[NodeId], target: TreeTarget[N,E]): NodeFocus[N,E] = target match {
				case ChildTarget(tree) =>
					addTree0(g, path, tree)
				case ParentTarget(count) =>
					g.node(path(count))
				case ExternalTarget(nid) =>
					g.node(nid)
			}
			def addTree0(g: Graph[N,E], path: List[NodeId], tree: Tree[N,E]): NodeFocus[N,E] = {
				val nf1 = g.addNode(tree.nv)
				addEdges(nf1, nf1.id::path, tree.edges)
			}
			def addEdge(fromFocus: NodeFocus[N,E], path: List[NodeId], ev: E, target: TreeTarget[N,E]): EdgeFocus[N,E] = {
				val toFocus = getOrAddTarget(fromFocus.unfocus, path, target)
				toFocus.unfocus.node(fromFocus.id).link(ev, toFocus.id)
			}
			// returns focus to parent
			def addEdges(fromFocus: NodeFocus[N,E], path: List[NodeId], edges: List[(E, TreeTarget[N,E])]): NodeFocus[N,E] = edges match {
				case Nil => fromFocus
				case (ev, target)::tail => addEdges(addEdge(fromFocus, path, ev, target).from, path, tail)
			}
			
			addTree0(g, Nil, tree)
		}

	def newScope[N,E](g: Graph[N,E]): Scope[N,E] = new Scope(g, Map.empty)
	
	class Scope[+N,+E](val g: Graph[N,E], val names: Map[String,NodeId]) {
		def graph = g
		def addNodeRef[N1>:N](name: String, nid: NodeId): Scope[N1,E] = {
			assert(!names.contains(name))
			val nf = g.node(nid)
			new Scope(nf.unfocus, names.updated(name, nf.id))
		}
		def addNode[N1>:N](name: String, value: N1): Scope[N1,E] = {
			assert(!names.contains(name))
			val nf = g.addNode(value)
			new Scope(nf.unfocus, names.updated(name, nf.id))
		}
		def addEdge[E1>:E](value: E1, from: String, to: String): Scope[N,E1] = {
			val fromId = names(from)
			val toId = names(to)
			new Scope(g.node(fromId).link(value, toId).unfocus, names)
		}
		def node(name: String): NodeFocus[N,E] = {
			g.node(names(name))
		}
	}

}


object Lang8 {

	import graph._
	import Graph._
	import GraphUtils._

	trait NodeLabel
	case object Variable extends NodeLabel
	case object Lambda extends NodeLabel
	case object Box extends NodeLabel
	case object Unbox extends NodeLabel
	case object Pair extends NodeLabel
	case object Symbol extends NodeLabel
	case object Intersection extends NodeLabel
	case object Union extends NodeLabel
	case object Impossible extends NodeLabel
	case object Choose extends NodeLabel
	case object Instantiation extends NodeLabel
	
	trait EdgeLabel
	// For lambda
	case object Domain extends EdgeLabel
	case object Codomain extends EdgeLabel
	case object Binding extends EdgeLabel
	// For instantiation
	case object Template extends EdgeLabel
	case object Target extends EdgeLabel
	// For box/unbox
	case object Content extends EdgeLabel
	// For pair
	case object Left extends EdgeLabel
	case object Right extends EdgeLabel
	// For intersection/union
	case object Member extends EdgeLabel
	// For choose
	case object Argument extends EdgeLabel
	case object Equal extends EdgeLabel
	case object NotEqual extends EdgeLabel
	
	// Id
	def createId(g: Graph[NodeLabel,EdgeLabel]): NodeFocus[NodeLabel,EdgeLabel] = {
		newScope[NodeLabel,EdgeLabel](g)
		.addNode("top", Lambda)
		.addNode("a", Variable)
		.addEdge(Domain, "top", "a")
		.addEdge(Codomain, "top", "a")
		.addEdge(Binding, "top", "a")
		.node("top")
	}
	
	// Swap
	def createSwap(g: Graph[NodeLabel,EdgeLabel]): NodeFocus[NodeLabel,EdgeLabel] = {
		newScope[NodeLabel,EdgeLabel](g)
		.addNode("top", Lambda)
		.addNode("inpair1", Pair)
		.addNode("inpair2", Pair)
		.addNode("outpair1", Pair)
		.addNode("outpair2", Pair)
		.addNode("a", Variable)
		.addNode("b", Variable)
		.addNode("rest", Variable)
		.addEdge(Domain, "top", "inpair1")
		.addEdge(Left, "inpair1", "b")
		.addEdge(Right, "inpair1", "inpair2")
		.addEdge(Left, "inpair2", "a")
		.addEdge(Right, "inpair2", "rest")
		.addEdge(Codomain, "top", "outpair1")
		.addEdge(Left, "outpair1", "a")
		.addEdge(Right, "outpair1", "outpair2")
		.addEdge(Left, "outpair2", "b")
		.addEdge(Right, "outpair2", "rest")
		.addEdge(Binding, "top", "inpair1")
		.addEdge(Binding, "top", "inpair2")
		.addEdge(Binding, "top", "outpair1")
		.addEdge(Binding, "top", "outpair2")
		.addEdge(Binding, "top", "a")
		.addEdge(Binding, "top", "b")
		.addEdge(Binding, "top", "rest")
		.node("top")
	}
	
	// Integer
	def createIntegerLib(g: Graph[NodeLabel,EdgeLabel]): Graph[NodeLabel,EdgeLabel] = {
		newScope[NodeLabel,EdgeLabel](g)
		.addNode("zero", Symbol)
		.addNode("succ", Symbol)
		
		.addNode("inc", Lambda)
		.addNode("inpair1", Pair)
		.addNode("outpair1", Pair)
		.addNode("a", Variable)
		.addNode("aSucc", Pair)
		.addNode("rest", Variable)
		.addEdge(Domain, "inc", "inpair1")
		.addEdge(Left, "inpair1", "a")
		.addEdge(Right, "inpair1", "rest")
		.addEdge(Codomain, "inc", "outpair1")
		.addEdge(Left, "outpair1", "aSucc")
		.addEdge(Right, "outpair1", "rest")
		.addEdge(Left, "aSucc", "succ")
		.addEdge(Right, "aSucc", "a")
		.addEdge(Binding, "inc", "inpair1")
		.addEdge(Binding, "inc", "outpair1")
		.addEdge(Binding, "inc", "a")
		.addEdge(Binding, "inc", "aSucc")
		.addEdge(Binding, "inc", "rest")
		
		.graph
	}
	
	def createComposition(g: Graph[NodeLabel,EdgeLabel], lam1: NodeId, lam2: NodeId): NodeFocus[NodeLabel,EdgeLabel] = {
		newScope[NodeLabel,EdgeLabel](g)
		.addNodeRef("lam1", lam1)
		.addNodeRef("lam2", lam2)
		.addNode("top", Lambda)
		.addNode("in", Variable)
		.addNode("mid", Variable)
		.addNode("out", Variable)
		.addNode("lam1inst", Instantiation)
		.addNode("lam1target", Lambda)
		.addNode("lam2inst", Instantiation)
		.addNode("lam2target", Lambda)
		.addEdge(Codomain, "top", "in")
		.addEdge(Domain, "top", "out")
		.addEdge(Codomain, "lam1target", "in")
		.addEdge(Domain, "lam1target", "mid")
		.addEdge(Codomain, "lam2target", "mid")
		.addEdge(Domain, "lam2target", "out")
		.addEdge(Template, "lam1inst", "lam1")
		.addEdge(Target, "lam1inst", "lam1target")
		.addEdge(Template, "lam2inst", "lam2")
		.addEdge(Target, "lam2inst", "lam2target")
		.addEdge(Binding, "top", "in")
		.addEdge(Binding, "top", "mid")
		.addEdge(Binding, "top", "out")
		.addEdge(Binding, "top", "lam1inst")
		.addEdge(Binding, "top", "lam2inst")
		.addEdge(Binding, "top", "lam1target")
		.addEdge(Binding, "top", "lam2target")
		.node("top")
	}
	
	import java.io._
	
	def printDot[N,E](os: OutputStream, g: Graph[N,E]): Unit = {
		val oswriter = new OutputStreamWriter(os)
		val pwriter = new PrintWriter(oswriter)
		import pwriter.{println, print}
		println("digraph G {")
		for (n <- g.nodes) {
			println("n" + n.id + " [label=\"" + n.value + n.id + "\"];")
			for (e <- n.from) {
				println("n" + n.id + " -> " + "n" + e.to.id + " [")
				println(
					e.value match {
						case Binding => "style=dotted, arrowsize=0.7"
						case v => "label=\"" + v + "\""
					})
				println("];")
			}
		}
		println("}")
		pwriter.flush()
	}
	
	def lookup[A,B](pairs: List[(A,B)], key: A): Option[B] = {
		pairs match {
			case Nil => None
			case (a, b)::_ if (a == key) => Some(b)
			case _::tail => lookup(tail, key)
		}
	}
	
	// get exactly 1 element
	def single[A](iterable: Iterable[A]): A = {
		val iterator = iterable.iterator
		if (!iterator.hasNext) throw new IllegalArgumentException("Can't get single element from iterable with 0 elements.")
		val result = iterator.next
		if (iterator.hasNext) throw new IllegalArgumentException("Can't get single element from iterable with > 1 elements.")
		result
	}
	
	// get 0 or 1 elements
	def singleOption[A](iterable: Iterable[A]): Option[A] = {
		val iterator = iterable.iterator
		val result = if (iterator.hasNext) Some(iterator.next) else None
		if (iterator.hasNext) throw new IllegalArgumentException("Can't get single element from iterable with > 1 elements.")
		result
	}
	
	def outEdgeByLabel(nf: NodeFocus[NodeLabel,EdgeLabel], label: EdgeLabel): Option[EdgeFocus[NodeLabel,EdgeLabel]] = {
		val matches = for (e <- nf.from; if (e.value == label)) yield e
		singleOption(matches)
	}
	
	def inEdgeByLabel(nf: NodeFocus[NodeLabel,EdgeLabel], label: EdgeLabel): Option[EdgeFocus[NodeLabel,EdgeLabel]] = {
		val matches = for (e <- nf.to; if (e.value == label)) yield e
		singleOption(matches)
	}
	
	def relinkEdge(ef: EdgeFocus[NodeLabel,EdgeLabel], nid: NodeId): EdgeFocus[NodeLabel,EdgeLabel] = {
		ef.delete.link(ef.value, nid)
	}

	val nonBinding = (_ : EdgeFocus[NodeLabel,EdgeLabel]).value != Binding
	
	def relinkMatchingInEdges(existing: NodeFocus[NodeLabel,EdgeLabel], newNid: NodeId, filter: EdgeFocus[NodeLabel,EdgeLabel] => Boolean): Graph[NodeLabel,EdgeLabel] = {
		(for (ef <- existing.to) yield ef.id).foldLeft(existing.unfocus) {
			case (g, eid) => {
				val ef1 = g.edge(eid)
				if (filter(ef1)) relinkEdge(ef1, newNid).unfocus
				else g
			}
		}
	}
	
	def replaceWithIntersection(g: Graph[NodeLabel,EdgeLabel], nids: List[NodeId]): NodeFocus[NodeLabel,EdgeLabel] = {
		assert(!nids.isEmpty)
		val inter = g.addNode(Intersection)
		val g1 = inter.unfocus
		
		// Calculate binding for intersection by looking at bindings for member nodes.
		// XXX: Not sure of exact algorithm yet.
		val g2 = inEdgeByLabel(g1.node(nids.head), Binding).get.from.link(Binding, inter.id).unfocus
		
		// Move existing member in-edges to intersection
		val g3 = nids.foldLeft(g2) { case (g, nid) => relinkMatchingInEdges(g.node(nid), inter.id, nonBinding) }
		// XXX: Handle outgoing edges! e.g. instantiation
		
		// Add member edges
		val g4 = nids.foldLeft(g3) { case (g, nid) => g.node(inter.id).link(Member, nid).unfocus }
		
		g4.node(inter.id)
	} 
	
	sealed trait StepResult
	case class NoStep(g: Graph[NodeLabel,EdgeLabel]) extends StepResult
	case class Step(g: Graph[NodeLabel,EdgeLabel], description: String) extends StepResult
	
	// input is focus on instantiation edge, output is focus on created intersection node
	def instantiate(nf: NodeFocus[NodeLabel,EdgeLabel]): NodeFocus[NodeLabel,EdgeLabel] = {
		// 1. Copy all nodes bound by target of instantiation (including target).
		// Keep a record of their counterparts.
		def copyNodes(g: Graph[NodeLabel,EdgeLabel], sourceNodes: List[NodeId], acc: List[(NodeId,NodeId)]): (Graph[NodeLabel,EdgeLabel], List[(NodeId,NodeId)]) = {
			sourceNodes match {
				case Nil => {
					(g, acc)
				}
				case head::tail => {
					val oldNode = g.node(head)
					val newNode = g.addNode(oldNode.value)
					//println("Copying node from " + oldNode + " to " + newNode + ".")
					copyNodes(newNode.unfocus, tail, (head, newNode.id)::acc)
				}
			}
		}
		val target = outEdgeByLabel(nf, Target).get.to
		val template = outEdgeByLabel(nf, Template).get.to
		
		val instantiationTargetId = target.id
		val instantiationTemplateId = template.id
		val children = (for (e <- template.from; if (e.value == Binding)) yield e.to.id).toList
		val (g1, copies) = copyNodes(nf.unfocus, instantiationTemplateId::children, Nil)
		val instantiation = lookup(copies, instantiationTemplateId).get
		
		// 2. Copy all edges, replacing one or both ends with the new node.
		// Binding nodes are rebound to parent of instantiation target.
		val bindingParentId = {
			val target = g1.node(instantiationTargetId)
			inEdgeByLabel(target, Binding).get.from.id
		}
		def copyEdge(ef: EdgeFocus[NodeLabel,EdgeLabel], copies: List[(NodeId,NodeId)]): EdgeFocus[NodeLabel,EdgeLabel] = {
			val value = ef.value
			val oldFrom = ef.from.id
			val newFrom = (value, oldFrom) match {
				case (Binding, instantiationTemplateId) => bindingParentId
				case _ => lookup(copies, oldFrom).get // must be defined
			}
			val oldTo = ef.to.id
			val newTo = lookup(copies, oldTo).getOrElse(oldTo) // may point outside bound nodes
			ef.unfocus.node(newFrom).link(value, newTo)
		}
		def copyEdges(g: Graph[NodeLabel,EdgeLabel], copies: List[(NodeId,NodeId)]): Graph[NodeLabel,EdgeLabel] = {
			val edges = for ((from, _) <- copies; e <- g.node(from).from) yield e.id
			edges.foldLeft(g) { case (g, e) => copyEdge(g.edge(e), copies).unfocus }
		}
		val g2 = copyEdges(g1, copies)
		val g3 = g2.node(bindingParentId).link(Binding, instantiation).unfocus		
		val nf4 = g3.addNode(Intersection)
		val g5 = nf4.unfocus.node(nf.id).delete
		val g6 = g5.node(bindingParentId).link(Binding, nf4.id).unfocus
		g6.node(nf4.id)
			.link(Member, instantiationTargetId)
			.from
			.link(Member, instantiation)
			.from
	}
	
	def solveIntersection(g: Graph[NodeLabel,EdgeLabel], e1: EdgeId, e2: EdgeId): StepResult = {
	
		val e1f = g.edge(e1)
		val e2f = g.edge(e2)
		assert(e1f.from.id == e2f.from.id)
		assert(e1f.from.value == Intersection)
		assert(e1f.value == Member)
		assert(e2f.value == Member)

		// Handle duplicate membership - can happen when copying edges
		if (e1f.to.id == e2f.to.id) return Step(e2f.delete.unfocus, "Removed duplicated member edge to " + e1f.to.id)

		(e1f.to.value, e2f.to.value) match {
			case (Variable, _) => {
				val g2 = relinkMatchingInEdges(g.node(e2f.to.id), e1f.to.id, nonBinding).node(e2f.to.id).delete
				Step(g2, "Removed variable " + e1f.to.id + " from intersection")
			}
			case (Intersection, _) => {
				val parent = e1f.from
				val child = e1f.to
				// Delete member link to child intersection
				val g1 = e1f.delete.unfocus
				// Copy all edges from child to parent intersection
				val g2 = relinkMatchingInEdges(g1.node(child.id), parent.id, nonBinding)
				// Delete child intersection
				val g3 = g2.node(child.id).delete
				Step(g3, "Merged child intersection " + child.id + " with parent " + parent.id)
			}
			case (Lambda, Lambda) => {
				val inter = e1f.from
				val interBinder = inEdgeByLabel(inter, Binding).get.from

				// XXX: Think about bindings!
				// XXX: Copy in-links???
				// XXX: Merge nodes?
				val lam1 = e1f.to
				val lam2 = e2f.to
				
				val lam1Dom = outEdgeByLabel(lam1, Domain).get.to
				val lam1Cod = outEdgeByLabel(lam1, Codomain).get.to
				val lam2Dom = outEdgeByLabel(lam2, Domain).get.to
				val lam2Cod = outEdgeByLabel(lam2, Codomain).get.to
				
				
				// Delete
				val g1 = g.node(lam2.id).delete // XXX: Need to check all out-edges were copied when intersection was made
				
				val lam1DomInter = replaceWithIntersection(g1, List(lam1Dom.id, lam2Dom.id))
				val g2 = lam1DomInter.unfocus
				val lam1CodInter = replaceWithIntersection(g2, List(lam1Cod.id, lam2Cod.id))
				val g3 = lam1CodInter.unfocus
				Step(g3, "Intersected lambdas " + lam1.id + " and " + lam2.id)
			}
			case (Pair, Pair) => {
				val inter = e1f.from
				val interBinder = inEdgeByLabel(inter, Binding).get.from

				// XXX: Think about bindings!
				// XXX: Copy in-links???
				// XXX: Merge nodes?
				val pair1 = e1f.to
				val pair2 = e2f.to
				
				val pair1Left = outEdgeByLabel(pair1, Left).get.to
				val pair1Right = outEdgeByLabel(pair1, Right).get.to
				val pair2Left = outEdgeByLabel(pair2, Left).get.to
				val pair2Right = outEdgeByLabel(pair2, Right).get.to
				
				
				// Delete
				val g1 = g.node(pair2.id).delete // XXX: Need to check all out-edges were copied when intersection was made
				
				val pair1LeftInter = replaceWithIntersection(g1, List(pair1Left.id, pair2Left.id))
				val g2 = pair1LeftInter.unfocus
				val pair1RightInter = replaceWithIntersection(g2, List(pair1Right.id, pair2Right.id))
				val g3 = pair1RightInter.unfocus
				Step(g3, "Intersected pairs " + pair1.id + " and " + pair2.id)
			}
			case (_, Variable | Intersection) => {
				// reverse edges to support easier pattern matching
				solveIntersection(g, e2, e1)
			}
			case (a, b) => {
				error("Cannot solve intersection between " + a + " and " + b + ".")
			}
			
			/*case (_, _) if (e1f.to.id == e2f.to.id) => 
			case (Variable, Variable) => // merge into single variable
			case (Lambda, Lambda) => // merge and intersect domain/codomain
			case (Pair, Pair) => // merge and intersect left/right
			case (Symbol, Symbol) => // never merge (only equal if actually same node)
			case (Box, _) || (_, Box) =>
			// cannot intersect box/unbox
			case _ => g*/
		}
	}
	
	def merge1(g: Graph[NodeLabel,EdgeLabel]): StepResult = {
		for (n1 <- g.nodes; n2 <- g.nodes; if (n1.id != n2.id)) {
			//println(n1.id + " eq " + n2.id)
			if (equalValue(g, n1.id, n2.id)) {
				// XXX: Choose binding edge?
				// XXX: Copy instantiation edges?
				//println("found match")
				return Step(relinkMatchingInEdges(g.node(n2.id), n1.id, nonBinding).node(n2.id).delete, "Merged " + n1.id + " and " + n2.id)
			}
		}	
		//println("no matches")
		NoStep(g)
	}

	def equalValue(g: Graph[NodeLabel,EdgeLabel], nid1: NodeId, nid2: NodeId): Boolean = {
		// XXX: Handle cycles.
		if (nid1 == nid2) true
		else {
			val nf1 = g.node(nid1)
			val nf2 = g.node(nid2)
			(nf1.value, nf2.value) match {
				case (Pair, Pair) => {
					val pair1Left = outEdgeByLabel(nf1, Left).get.to
					val pair1Right = outEdgeByLabel(nf1, Right).get.to
					val pair2Left = outEdgeByLabel(nf2, Left).get.to
					val pair2Right = outEdgeByLabel(nf2, Right).get.to
					equalValue(g, pair1Left.id, pair2Left.id) && equalValue(g, pair1Right.id, pair2Right.id)
				}
				case (Lambda, Lambda) => {
					val lam1Dom = outEdgeByLabel(nf1, Domain).get.to
					val lam1Cod = outEdgeByLabel(nf1, Codomain).get.to
					val lam2Dom = outEdgeByLabel(nf2, Domain).get.to
					val lam2Cod = outEdgeByLabel(nf2, Codomain).get.to
					equalValue(g, lam1Dom.id, lam2Dom.id) && equalValue(g, lam1Cod.id, lam2Cod.id)
				}
				case (_, _) => {
					false
				}
			}
		}
	}
	
	// steps:
	// - garbage collection
	// - instantiation
	// - unification (intersection)
	// - remove intersections/unions with single member
	// - combine parent/child intersections/unions
	// - unboxing
	
	def allPairs[A](list: List[A]): List[(A,A)] = {
		def allPairs0(list0: List[A], acc: List[(A,A)]): List[(A,A)] = {
			list0 match {
				case Nil => acc
				case head::tail => {
					val headPairings = for (a <- tail) yield (head, a)
					allPairs0(tail, acc ++ headPairings)
				}
			}
		}
		allPairs0(list, Nil)
	}
	
	def solveIntersection1(g: Graph[NodeLabel,EdgeLabel]): StepResult = {
		def solveIntersection10(intersections0: List[NodeFocus[NodeLabel,EdgeLabel]]): StepResult = {
			//println("solveIntersection10")
			intersections0 match {
				case Nil => NoStep(g)
				case intersection::tail => {
					val members = (for (e <- intersection.from; if (e.value == Member)) yield e).toList
					if (members.length == 1) removeTrivialIntersection(intersection)
					else {
						def solvePairs(pairs: List[(EdgeFocus[NodeLabel,EdgeLabel],EdgeFocus[NodeLabel,EdgeLabel])]): StepResult = {
							//println("solvePairs")
							pairs match {
								case Nil => NoStep(g)
								case (a, b)::tail => solveIntersection(g, a.id, b.id) match {
									case ns: NoStep => solvePairs(tail)
									case s: Step => s
								}
							}
						}
						solvePairs(allPairs(members)) match {
							case ns: NoStep => solveIntersection10(tail)
							case s: Step => s
						}
					}
				}
			}
		}
		val intersections = for (n <- g.nodes; if (n.value == Intersection)) yield n
		solveIntersection10(intersections.toList)
	}
	
	def removeTrivialIntersection(nf: NodeFocus[NodeLabel,EdgeLabel]): StepResult = {
		val outgoing = (for (ef <- nf.from) yield ef).toList
		assert(outgoing.size == 1)
		val memberEdge = outgoing(0)
		assert(memberEdge.value == Member)
		Step(relinkMatchingInEdges(nf, memberEdge.to.id, nonBinding).node(nf.id).delete, "Removed trivial intersection " + nf.id)
		// XXX: Should relink instantiation edge too!
	}

	
	def instantiate1(g: Graph[NodeLabel,EdgeLabel]): StepResult = {
		val instantiations = (for (n <- g.nodes; if (n.value == Instantiation)) yield n).toList
		if (instantiations.isEmpty) NoStep(g)
		else {
			val instantiation = instantiations(0)
			val instantiationResult = instantiate(instantiation)
			Step(instantiationResult.unfocus, "Instantiated " + instantiation.id)
		}
	}
	
	def main(args: Array[String]): Unit = {
		val idFocus = createId(Graph.empty)
		val swapFocus = createSwap(idFocus.unfocus)
		val swapSwapFocus = createComposition(swapFocus.unfocus, swapFocus.id, swapFocus.id)
		val idIdFocus = createComposition(swapSwapFocus.unfocus, idFocus.id, idFocus.id)
		//val integerLib = createIntegerLib(swapSwapFocus.unfocus)
		val start = idIdFocus.unfocus
		
		val stepFunctions: List[Graph[NodeLabel,EdgeLabel]=>StepResult] = List(
			//merge1 _,
			solveIntersection1 _,
			instantiate1 _
		)

		def step1(g: Graph[NodeLabel,EdgeLabel]): StepResult = {
			def step10(fs: List[Graph[NodeLabel,EdgeLabel]=>StepResult]): StepResult = {
				fs match {
					case Nil => NoStep(g)
					case f::tail => f(g) match {
						case NoStep(_) => step10(tail)
						case s: Step => s
					}
				}
			}
			step10(stepFunctions)
		}
		
		def run[A](g: Graph[NodeLabel,EdgeLabel]): Stream[Step] = {
			def run0(g1: Graph[NodeLabel,EdgeLabel]): Stream[Step] = {
				step1(g1) match {
					case NoStep(g2) => {
						Stream.empty
					}
					case s @ Step(g2, _) => {
						Stream.cons(s, run0(g2))
					}
				}
			}
			Stream.cons(Step(g, "Initial"), run0(g))
		}
		
		val gs = run(start)
		for ((Step(g, desc), i) <- gs.zipWithIndex) {
			println("Step " + i + ": " + desc)
			import java.io._
			val f = new File("step-"+i+".dot")
			val os = new FileOutputStream(f)
			try {
				printDot(os, g)
			} finally {
				os.close
			}
		}
	}
}
