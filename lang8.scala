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

	def containsNode(id: NodeId): Boolean =
		nmap.contains(id)
	def containsEdge(id: EdgeId): Boolean =
		emap.contains(id)
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

	def newScope[N,E](g: Graph[N,E]): Scope[N,E] = new Scope(g, Map.empty[String,NodeId]::Nil)
	
	class Scope[+N,+E](val g: Graph[N,E], val nameStack: List[Map[String,NodeId]]) {
		def graph = g
		def nest: Scope[N,E] = {
			new Scope(g, Map.empty[String,NodeId]::nameStack)
		}
		def unnest: Scope[N,E] = {
			new Scope(g, nameStack.tail)
		}
		private def names(name: String): NodeId = {
			nameStack.foldLeft[Option[NodeId]](None) {
				case (None, nameMap) => nameMap.get(name) match {
					case None => None
					case s => s
				}
				case (s, _) => s
			}.get
		}
		def addNodeRef[N1>:N](name: String, nid: NodeId): Scope[N1,E] = {
			//assert(!names.contains(name))
			val nf = g.node(nid)
			new Scope(nf.unfocus, nameStack.head.updated(name, nf.id)::nameStack.tail)
		}
		def addNode[N1>:N](name: String, value: N1): Scope[N1,E] = {
			//assert(!names.contains(name))
			val nf = g.addNode(value)
			new Scope(nf.unfocus, nameStack.head.updated(name, nf.id)::nameStack.tail)
		}
		def addEdge[E1>:E](value: E1, from: String, to: String): Scope[N,E1] = {
			val fromId = names(from)
			val toId = names(to)
			new Scope(g.node(fromId).link(value, toId).unfocus, nameStack)
		}
		def nodeRef(name: String): NodeId = {
			names(name)
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
	case object Root extends NodeLabel
	case object Variable extends NodeLabel
	case object Lambda extends NodeLabel
	case object Pair extends NodeLabel
	case object Symbol extends NodeLabel
	case object Instantiation extends NodeLabel
	
	trait EdgeLabel
	// For root
	case object Pin extends EdgeLabel
	// For lambda
	case object Domain extends EdgeLabel
	case object Codomain extends EdgeLabel
	case object Binding extends EdgeLabel
	// For instantiation
	case object Template extends EdgeLabel
	case object Target extends EdgeLabel
	// For pair
	case object Left extends EdgeLabel
	case object Right extends EdgeLabel
	
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
	
	def unify(g: Graph[NodeLabel,EdgeLabel], nids: List[NodeId]): NodeFocus[NodeLabel,EdgeLabel] = {
		assert(!nids.isEmpty)
		// merge equal nids
		val uniqueNids = nids.removeDuplicates
		if (nids.length == 1) g.node(nids.head)
		else {
			// Find value for replacement node
			val values = uniqueNids map {
				case nid => g.node(nid).value
			} filter {
				case value => value != Variable
			} removeDuplicates
			val value: NodeLabel = values match {
				case Nil => Variable
				case head::Nil => g.node(nids.head).value
				case _ => error("Cannot unify nodes with different types: " + values)
			}
			// Find binder for replacement node
			val topBinder: Option[NodeId] = uniqueNids map {
				case nid => {
					(nid, bindings(g.node(nid)))
					}
			} sortWith {
				case ((nid1, binders1), (nid2, binders2)) => binders1.length < binders2.length
			} match {
				case (_, Nil)::_ => None
				case (nid, _)::_ => Some(inEdgeByLabel(g.node(nid), Binding).get.from.id)
				case Nil => error("should never occur!")
			}
			// Create list of all outgoing edges
			val outgoingLabels = (for (nid <- uniqueNids; e <- g.node(nid).from) yield {
				e.value
			}).toList removeDuplicates
			
			// Create replacement node
			val replacement = g.addNode(value)
			val g1 = replacement.unfocus
			val g2 = topBinder match {
				case None => g1
				case Some(nid) => g1.node(nid).link(Binding, replacement.id).unfocus
			}
			val g3 = uniqueNids.foldLeft(g2) {
				case (gx, nid) => relinkMatchingInEdges(gx.node(nid), replacement.id, nonBinding)
			}
			val g4 = outgoingLabels.foldLeft(g3) {
				case (gx, label) => {
					val existingEdges = (for (nid <- uniqueNids; e <- gx.node(nid).from; if (e.value == label)) yield e).toList
					if (label == Binding) {
						existingEdges.foldLeft(gx) {
							// Link to bound children
							case (gx1, e) => gx1.edge(e.id).delete.unfocus.node(replacement.id).link(Binding, e.to.id).unfocus
						}
					} else {
						// Create new child by unifying existing children
						val childReplacement = unify(gx, for (e <- existingEdges) yield e.to.id)
						// Link to new child
						childReplacement.unfocus.node(replacement.id).link(label, childReplacement.id).unfocus
					}
				}
			}
			g4.node(replacement.id)
		}
	} 
	
	sealed trait StepResult
	case class NoStep(g: Graph[NodeLabel,EdgeLabel]) extends StepResult
	case class Step(g: Graph[NodeLabel,EdgeLabel], description: String) extends StepResult
	
	// input is focus on instantiation edge, output is focus on result node
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
		val bindingParentId = inEdgeByLabel(nf, Binding).get.from.id
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
		val g3 = g2.node(bindingParentId).link(Binding, instantiation).unfocus.node(nf.id).delete
		unify(g3, List(instantiationTargetId, instantiation))
	}
	
	def bindings(n: NodeFocus[NodeLabel,EdgeLabel]): List[NodeId] = {
		// Make tail recursive?
		inEdgeByLabel(n, Binding) match {
			case None => Nil
			case Some(e) => {
				e.id::bindings(e.from)
			}
		}
	}
	
	def sortByDominant(g: Graph[NodeLabel,EdgeLabel], nodes: List[NodeId]): List[NodeId] = {
		(for (c <- nodes) yield {
			val b = bindings(g.node(c))
			(c, b.length)
		}) sortWith {
			case ((_, bl1), (_, bl2)) => bl1 < bl2
		} map {
			case (c, b) => c
		}
	}
	
	def merge1(g: Graph[NodeLabel,EdgeLabel]): StepResult = {
		for (n1 <- g.nodes; n2 <- g.nodes; if (n1.id != n2.id)) {
			//println(n1.id + " eq " + n2.id)
			if (equalValue(g, n1.id, n2.id)) {
				val keep::delete::Nil = sortByDominant(g, n1.id::n2.id::Nil)
				return Step(relinkMatchingInEdges(g.node(delete), keep, nonBinding).node(delete).delete, "Merged equal value " + delete + " into " + keep)
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
					((pair1Left.id == pair2Left.id) && (pair1Right.id == pair2Right.id))
				}
				case (Lambda, Lambda) => {
					val lam1Dom = outEdgeByLabel(nf1, Domain).get.to
					val lam1Cod = outEdgeByLabel(nf1, Codomain).get.to
					val lam2Dom = outEdgeByLabel(nf2, Domain).get.to
					val lam2Cod = outEdgeByLabel(nf2, Codomain).get.to
					((lam1Dom.id == lam2Dom.id) && (lam1Cod.id == lam2Cod.id))
				}
				case (_, _) => {
					false
				}
			}
		}
	}
	
	def markSweep(g: Graph[NodeLabel,EdgeLabel]): StepResult = {
		val rootValues = List(Root, Instantiation)
		def mark(pending: List[NodeId], marked: List[NodeId]): List[NodeId] = {
			pending match {
				case Nil =>
					marked
				case head::tail => {
					val refs = for (e <- g.node(head).from; if (e.value != Binding)) yield e.to.id
					val unmarkedRefs = for (r <- refs; if (!marked.contains(refs))) yield r
					mark(unmarkedRefs.toList ++ tail, head::marked)
				}
			}
		}
		val roots = for (n <- g.nodes; if (rootValues.contains(n.value))) yield n.id
		val marked = mark(roots.toList, Nil)
		// sweep
		val g2 = g.nodes.foldLeft(g) { case (g1, n) => if (marked.contains(n.id)) g1 else g1.node(n.id).delete }
		if (g == g2) NoStep(g) else Step(g2, "Garbage collection")
	}
	
	// steps:
	// - garbage collection
	// - instantiation
	// - unification
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
	
	def instantiate1(g: Graph[NodeLabel,EdgeLabel]): StepResult = {
		val instantiations = (for (n <- g.nodes; if (n.value == Instantiation)) yield n).toList
		if (instantiations.isEmpty) NoStep(g)
		else {
			val instantiation = instantiations(0)
			val instantiationResult = instantiate(instantiation)
			Step(instantiationResult.unfocus, "Instantiated " + instantiation.id + " to " + instantiationResult.id)
		}
	}
	
	def main(args: Array[String]): Unit = {
	
	def compose(s: Scope[NodeLabel,EdgeLabel], name: String, components: String): Scope[NodeLabel,EdgeLabel] = {
		s
		.addNode(name, Lambda)
	}

	def createComposition(s: Scope[NodeLabel,EdgeLabel], name: String, lam1: String, lam2: String): Scope[NodeLabel,EdgeLabel] = {
		newScope[NodeLabel,EdgeLabel](g)
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
		.addEdge(Template, "lam1inst", lam1)
		.addEdge(Target, "lam1inst", "lam1target")
		.addEdge(Template, "lam2inst", lam2)
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

	
		val start = newScope[NodeLabel,EdgeLabel](Graph.empty)
		.addNode("root", Root)
		
		// Id
		.addNode("id", Lambda)
		.addEdge(Pin, "root", "id")
		.nest
		.addNode("a", Variable)
		.addEdge(Domain, "id", "a")
		.addEdge(Codomain, "id", "a")
		.addEdge(Binding, "id", "a")
		.unnest

		// Swap
		.addNode("swap", Lambda)
		.addEdge(Pin, "root", "swap")
		.nest
		.addNode("inpair1", Pair)
		.addNode("inpair2", Pair)
		.addNode("outpair1", Pair)
		.addNode("outpair2", Pair)
		.addNode("a", Variable)
		.addNode("b", Variable)
		.addNode("rest", Variable)
		.addEdge(Domain, "swap", "inpair1")
		.addEdge(Left, "inpair1", "b")
		.addEdge(Right, "inpair1", "inpair2")
		.addEdge(Left, "inpair2", "a")
		.addEdge(Right, "inpair2", "rest")
		.addEdge(Codomain, "swap", "outpair1")
		.addEdge(Left, "outpair1", "a")
		.addEdge(Right, "outpair1", "outpair2")
		.addEdge(Left, "outpair2", "b")
		.addEdge(Right, "outpair2", "rest")
		.addEdge(Binding, "swap", "inpair1")
		.addEdge(Binding, "swap", "inpair2")
		.addEdge(Binding, "swap", "outpair1")
		.addEdge(Binding, "swap", "outpair2")
		.addEdge(Binding, "swap", "a")
		.addEdge(Binding, "swap", "b")
		.addEdge(Binding, "swap", "rest")
		.unnest
		
		// Apply
		.addNode("apply", Lambda)
		.addEdge(Pin, "root", "apply")
		.nest
		.addNode("inpair", Pair)
		.addNode("lam", Lambda)
		.addNode("rest", Variable)
		.addNode("out", Variable)
		.addEdge(Domain, "apply", "inpair")
		.addEdge(Codomain, "apply", "out")
		.addEdge(Domain, "lam", "rest")
		.addEdge(Codomain, "lam", "out")
		.addEdge(Left, "inpair", "lam")
		.addEdge(Right, "inpair", "rest")
		.addEdge(Binding, "apply", "inpair")
		.addEdge(Binding, "apply", "lam")
		.addEdge(Binding, "apply", "rest")
		.addEdge(Binding, "apply", "out")
		.unnest
		
		// Zero
		.addNode("zero", Symbol)
		.addEdge(Pin, "root", "zero")
		.nest
		
		// Succ
		.addNode("succ", Symbol)
		.addEdge(Pin, "root", "succ")
		.nest
		
		// Inc
		.addNode("inc", Lambda)
		.addEdge(Pin, "root", "inc")
		.nest
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
	
		val stepFunctions: List[Graph[NodeLabel,EdgeLabel]=>StepResult] = List(
			markSweep _,
			merge1 _,
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
