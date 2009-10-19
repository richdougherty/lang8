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
	
	trait EdgeLabel
	// For lambda
	case object Domain extends EdgeLabel
	case object Codomain extends EdgeLabel
	case object Binding extends EdgeLabel
	case object Instantiate extends EdgeLabel
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
		.addEdge(Codomain, "top", "inpair1")
		.addEdge(Left, "inpair1", "b")
		.addEdge(Right, "inpair1", "inpair2")
		.addEdge(Left, "inpair2", "a")
		.addEdge(Right, "inpair2", "rest")
		.addEdge(Domain, "top", "outpair1")
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
	
	def createComposition(g: Graph[NodeLabel,EdgeLabel], lam1: NodeId, lam2: NodeId): NodeFocus[NodeLabel,EdgeLabel] = {
		newScope[NodeLabel,EdgeLabel](g)
		.addNodeRef("lam1", lam1)
		.addNodeRef("lam2", lam2)
		.addNode("top", Lambda)
		.addNode("in", Variable)
		.addNode("mid", Variable)
		.addNode("out", Variable)
		.addNode("lam1inst", Lambda)
		.addNode("lam2inst", Lambda)
		.addEdge(Codomain, "top", "in")
		.addEdge(Domain, "top", "out")
		.addEdge(Codomain, "lam1inst", "in")
		.addEdge(Domain, "lam1inst", "mid")
		.addEdge(Codomain, "lam2inst", "mid")
		.addEdge(Domain, "lam2inst", "out")
		.addEdge(Instantiate, "lam1inst", "lam1")
		.addEdge(Instantiate, "lam2inst", "lam2")
		.addEdge(Binding, "top", "in")
		.addEdge(Binding, "top", "mid")
		.addEdge(Binding, "top", "out")
		.addEdge(Binding, "top", "lam1inst")
		.addEdge(Binding, "top", "lam2inst")
		.node("top")
	}
	
	def printDot[N,E](g: Graph[N,E]): Unit = {
		println("digraph G {")
		for (n <- g.nodes) {
			println("n" + n.id + " [label=\"" + n.value + "\"];")
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
	
	// input is focus on instantiation edge, output is focus on created intersection node
	def instantiate(ef: EdgeFocus[NodeLabel,EdgeLabel]): NodeFocus[NodeLabel,EdgeLabel] = {
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
		val instantiationTargetId = ef.from.id
		val instantiationTemplateId = ef.to.id
		val children = (for (e <- ef.to.from; if (e.value == Binding)) yield e.to.id).toList
		val (g1, copies) = copyNodes(ef.unfocus, instantiationTemplateId::children, Nil)
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
		val g5 = nf4.unfocus.edge(ef.id).delete.unfocus
		val g6 = g5.node(bindingParentId).link(Binding, nf4.id).unfocus
		g6.node(nf4.id)
			.link(Member, instantiationTargetId)
			.from
			.link(Member, instantiation)
			.from
	}
	
	def intersect(g: Graph[NodeLabel,EdgeLabel], e1: EdgeId, e2: EdgeId): Graph[NodeLabel,EdgeLabel] = {
		val e1f = g.edge(e1)
		val e2f = g.edge(e2)
		assert(e1f.from.id == e2f.from.id)
		assert(e1f.from.value == Intersection)
		assert(e1f.value == Member)
		assert(e2f.value == Member)
		(e1f.to.value, e2f.to.value) match {
			case (Lambda, Lambda) => {
				// XXX: Think about bindings!
				// XXX: Copy in-links???
				val lam1 = e1f.to
				val lam2 = e2f.to
				val lam1Dom = outEdgeByLabel(lam1, Domain).get.to
				val lam1Cod = outEdgeByLabel(lam1, Codomain).get.to
				val lam2Dom = outEdgeByLabel(lam2, Domain).get.to
				val lam2Cod = outEdgeByLabel(lam2, Codomain).get.to
				val inter = e1f.from
				val interBinder = inEdgeByLabel(inter, Binding).get.from
				
				// Delete
				val g1 = g
					.edge(e2f.id).delete
					.unfocus
				val lam1DomInter = g1.addNode(Intersection)
				val g2 = lam1DomInter.unfocus
				val lam1CodInter = lam1DomInter
					.unfocus
					.addNode(Intersection)
				val g3 = lam1CodInter.unfocus
					
				// Move edges from old domain/codomain nodes
				// to new intersection nodes
				
				def relinkEdge(ef: EdgeFocus[NodeLabel,EdgeLabel], nid: NodeId): EdgeFocus[NodeLabel,EdgeLabel] = {
					ef.delete.link(ef.value, nid)
				}
				def relinkMatchingInEdges(existing: NodeFocus[NodeLabel,EdgeLabel], newNid: NodeId, filter: EdgeFocus[NodeLabel,EdgeLabel] => Boolean): Graph[NodeLabel,EdgeLabel] = {
					(for (ef <- existing.to) yield ef.id).foldLeft(existing.unfocus) {
						case (g, eid) => {
							val ef1 = g.edge(eid)
							if (filter(ef1)) relinkEdge(ef1, newNid).unfocus
							else g
						}
					}
				}
				
				val nonBinding = (_ : EdgeFocus[NodeLabel,EdgeLabel]).value != Binding
				
				val g5 = relinkMatchingInEdges(g3.node(lam1Dom.id), lam1DomInter.id, nonBinding)
				val g6 = relinkMatchingInEdges(g5.node(lam1Cod.id), lam1CodInter.id, nonBinding)
				val g7 = relinkMatchingInEdges(g6.node(lam2Dom.id), lam1DomInter.id, nonBinding)
				val g8 = relinkMatchingInEdges(g7.node(lam2Cod.id), lam1CodInter.id, nonBinding)

				val g10 = g8
					// Binding edges
					.node(interBinder.id)
					.link(Binding, lam1DomInter.id)
					.from
					.link(Binding, lam1CodInter.id)
					.unfocus
					// Member edges
					.node(lam1DomInter.id)
					.link(Member, lam1Dom.id)
					.from
					.link(Member, lam2Dom.id)
					.unfocus
					.node(lam1CodInter.id)
					.link(Member, lam1Cod.id)
					.from
					.link(Member, lam2Cod.id)
					.unfocus
					
				g10
			}
			case _ => error("!!!")
			
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
	
	// steps:
	// - garbage collection
	// - instantiation
	// - unification (intersection)
	// - remove intersections/unions with single member
	// - combine parent/child intersections/unions
	// - unboxing
	
	def intersect1(g: Graph[NodeLabel,EdgeLabel]): Graph[NodeLabel,EdgeLabel] = {
		val intersections = for (n <- g.nodes; if (n.value == Intersection)) yield n
		if (intersections.isEmpty) g
		else {
			val intersection = intersections.head
			val members = (for (e <- intersection.from; if (e.value == Member)) yield e).toList
			// XXX: Handle 0/1 members
			intersect(g, members(0).id, members(1).id)
		}
	}
	
	def instantiate1(g: Graph[NodeLabel,EdgeLabel]): Graph[NodeLabel,EdgeLabel] = {
		val instantiations = (for (e <- g.edges; if (e.value == Instantiate)) yield e).toList
		if (instantiations.isEmpty) g
		else instantiate(instantiations(0)).unfocus
			/*
			val target = e.from
			val targetBindings = for (e <- target.to; if (e.value == Binding)) yield e
			assert(targetBindings.length == 1)
			val targetBinding = targetBindings(0)
			for (binding <- e.to.edges; if (binding.value == Binding)) {
			
			}
			*/
	}
	
	def main(args: Array[String]): Unit = {
		val swapFocus = createSwap(Graph.empty)
		val swapSwapFocus = createComposition(swapFocus.unfocus, swapFocus.id, swapFocus.id)
		val start = swapSwapFocus.unfocus
		printDot(intersect1(instantiate1(instantiate1(start))))
	}
}
