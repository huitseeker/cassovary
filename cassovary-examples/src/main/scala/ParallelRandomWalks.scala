import com.twitter.cassovary.graph.GraphUtils.RandomWalkParams
import com.twitter.cassovary.graph.{DirectedPath, GraphUtils, TestGraphs}
import com.twitter.util.{Duration, Stopwatch}
import com.twitter.cassovary.util.io.AdjacencyListGraphReader
import com.twitter.cassovary.util.NodeNumberer
import java.util.concurrent.Executors
import scala.collection.JavaConversions._
import java.util.zip.GZIPInputStream
import java.io.FileInputStream
import java.io.BufferedInputStream
import com.twitter.cassovary.graph.GraphDir._
import com.twitter.cassovary.graph.RandomBoundedTraverser
import com.twitter.cassovary.graph.tourist.IntInfoKeeper
import com.twitter.cassovary.graph.GraphDir
import com.twitter.cassovary.graph.Graph
import com.twitter.cassovary.graph.Traverser
import scala.util.Random
import com.twitter.cassovary.graph.Node
import com.twitter.cassovary.graph.NodeUtils
import scala.collection.mutable.HashMap
import scala.collection.mutable.Map
import scala.annotation.tailrec

object ParallelRandomWalk {

  class DrunkardMobTraverser(graph: Graph, dir: GraphDir, homeNodeIds: Array[Int],
    maxSteps: Int, randNumGen: Random = new Random) {

    // a map from a node index to their parent in the FPG graph
    val nodeFPG = new IntInfoKeeper(false)
    // the value of the first meeting distance for that node index
    val valFPG = new IntInfoKeeper(false)

    private val walks: Array[Int] = homeNodeIds.clone()

    // Advance all walks by one step, do not look at where they start from or are currently at
    private def takeRandomStep(walks: Array[Int]): Unit = {
      for ((x, i) <- walks.view.zipWithIndex)
        // -1 marks a finished walk, which occurs if the cur node doesn't have outgoing edges
        if (x != -1) walks(i) = graph.getNodeById(x).flatMap{ _.randomNeighbor(dir, randNumGen) }.getOrElse(-1)
    }

    private def coalesceStep(walks: Array[Int], numSteps: Int): Unit = {
      // find walks meeting at this node
      val curNodeToSourceIdx = homeNodeIds.indices.groupBy {
        case (i) => walks(i)
      }
      // build the FPG for each non-minimal walk meeting here
      curNodeToSourceIdx foreach {
        case (curNode, sourceIndexes) if (curNode != -1) => // for all s in sources, walks from homeNodeIds(s) are meeting at curNode !
          val smallestSourceIdx = sourceIndexes.minBy((i) => homeNodeIds(i)) // We arbitrarily choose the smallest node id
          val toReindex = sourceIndexes.filter { (i) => !valFPG.infoOfNode(homeNodeIds(i)).isDefined } // nodes shouldn't already be in the FPG
          toReindex.foreach((i) => {
            if (i != smallestSourceIdx) {
              assert (homeNodeIds(i) != homeNodeIds(smallestSourceIdx))
              nodeFPG.recordInfo(homeNodeIds(i), homeNodeIds(smallestSourceIdx))
              valFPG.recordInfo(homeNodeIds(i), numSteps)
            }
          })
          // only the walk with smallest source is allowed to pursue
          sourceIndexes foreach { (i) => if (i != smallestSourceIdx) walks(i) = -1 }
        case _ => {}
      }
    }
    private var hasRun = false
    def run(): (IntInfoKeeper, IntInfoKeeper) = {
      if (!hasRun) {
        var stepsTaken = 0
        var allFinished = false
        while (stepsTaken < maxSteps && !allFinished) {
          takeRandomStep(walks)
          coalesceStep(walks, stepsTaken)
          stepsTaken += 1
          allFinished = walks.forall(_ == -1)
        }
        hasRun = true
      }
      (nodeFPG, valFPG)
    }

    class UnionFind[T]() {
      private val parent: Map[T, T] = new HashMap[T, T] {
        override def default(s: T) = {
          get(s) match {
            case Some(v) => v
            case None => put(s, s); s
          }
        }
      }

      private val rank: Map[T, Int] = new HashMap[T, Int] {
        override def default(s: T) = {
          get(s) match {
            case Some(v) => v
            case None => put(s, 1); 1
          }
        }
      }

      /**
       * Return the parent (representant) of the equivalence class.
       * Uses path compression.
       */
      def find(s: T): T = {
        val ps = parent(s)
        if (ps == s) s else {
          val cs = find(ps)
          parent(s) = cs
          cs
        }
      }

      /**
       *  Unify equivalence classes of elements.
       *  Uses union by rank.
       */
      def union(x: T, y: T): Unit = {
        val cx = find(x)
        val cy = find(y)
        if (cx != cy) {
          val rx = rank(x)
          val ry = rank(y)
          if (rx > ry) parent(cy) = cx
          else if (rx < ry) parent(cx) = cy
          else {
            rank(cx) += 1
            parent(cy) = cx
          }
        }
      }

    }

    sealed trait Tree
    case class TreeNode(val id: Int, var children: List[TreeNode], var coloured: Boolean, var ancestor: Option[TreeNode]) extends Tree

    val uf = new UnionFind[Int]()

    @tailrec
    private def allPairs(l: List[Int], res: List[Long]): List[Long] = l match {
      case Nil => res
      case x :: Nil => res
      case x:: xs => allPairs(xs, (for (y <- xs) yield productFromComponents(x, y)) ++ res)
    }

    def productFromComponents(x: Int, y: Int) = ((x.toLong) << 32) | (y.toLong & 0xffffffffL)
    def leftFromProduct(l: Long) = (l >> 32).toInt
    def rightFromProduct(l: Long) = l.toInt
    def pairFromProduct(l: Long) = ((l >>32).toInt, l.toInt)

    def runLCA(P: List[Long], u: TreeNode, lcaMap: Map[Long, Int], idToNode:Map[Int, TreeNode]): Unit = {
      u.ancestor = Some(u)
      u.children foreach { node =>
        runLCA(P, node, lcaMap, idToNode)
        uf.union(u.id, node.id)
        idToNode(uf.find(u.id)).ancestor = Some(u)
        u.coloured = true
      }
      P.filter{ pairFromProduct(_) match {
        case(a, b) => a == u.id && idToNode(b).coloured
        }
      } foreach { pairFromProduct(_) match {
          case (a,b) => lcaMap(productFromComponents(a, b)) = idToNode(uf.find(b)).ancestor.get.id
        }
      }
    }

    def buildDistances(watch: Stopwatch.Elapsed): (Map[Long, Int], Int) = {
      val dMap = new HashMap[Long, Int]()

      val (nodeFPG, valFPG) = run()
      printf("\nFinished building the FPG at %s milis. It holds %s nodes.", watch().inMillis.toInt, nodeFPG.infoAllNodes.values.size())

      val rootsUF = new UnionFind[Int]()

      val idToNode = new HashMap[Int, TreeNode]()

      def findLastNodeValue(nodeTable: IntInfoKeeper, valueTable: IntInfoKeeper, sourceNode: Int, stopNode: Int): Option[Int] = {
        val next = nodeTable.infoOfNode(sourceNode)
        if (!next.isDefined || next.get == -1) None
        else {
          assert(next.get != sourceNode)
          if (next.get == stopNode) valueTable.infoOfNode(sourceNode)
          else findLastNodeValue(nodeTable, valueTable, next.get, stopNode)
        }
      }

      @tailrec
      def findPath(nodeTable: IntInfoKeeper, sourceNode: Int, res:List[Int] = Nil): List[Int] = {
        val next = nodeTable.infoOfNode(sourceNode)
        if (!next.isDefined || next.get == -1 || res.size > 100) res
        else {
          assert(sourceNode != next.get)
          findPath(nodeTable, next.get, sourceNode :: res)
        }
      }

      nodeFPG.infoAllNodes foreach {
        case (nodeId, parentId) =>
          assert(parentId != nodeId)
          assert(parentId < nodeId)
          rootsUF.union(nodeId, parentId)

          // the first node has no parent to attach to
          if (!idToNode.contains(parentId)) idToNode(parentId) = TreeNode(parentId, List(), false, None)
          val parentNode = idToNode(parentId)
          val childNode = TreeNode(nodeId, List(), false, None)
          parentNode.children = childNode :: parentNode.children
          // you never see a node twice
          idToNode(nodeId) = childNode
      }

      val rootIds = (homeNodeIds map { (id) => rootsUF.find(id) } toSet) filter {(id) => idToNode.contains(id)}
      printf("\nWe have to treat %s connected components.", rootIds.size)
      val notHere = homeNodeIds.toList filter {(id) => !idToNode.contains(id)}
      printf ("\nMissing node info for %s ids!", notHere.size)
      if (notHere.size < 100) printf ("\nMissing ids: " + notHere.toString)

      val lcaMap = new HashMap[Long, Int]()
      val base = homeNodeIds filter {idToNode.contains(_)} take 100
      lazy val pairs = allPairs(base.toList, List())

      rootIds foreach { rId =>
        runLCA(pairs, idToNode(rId), lcaMap, idToNode)
      }

      var expected = 0
      pairs foreach {
        pairFromProduct(_) match {
          case (a, b) =>
            val lcaNodeId = lcaMap.get(productFromComponents(a, b))
            if (lcaNodeId.isDefined) {
              // They meet !
              expected += 1
              val distance: Option[Int] =
                if (lcaNodeId.get == a) findLastNodeValue(nodeFPG, valFPG, b, a)
                else if (lcaNodeId.get == b) findLastNodeValue(nodeFPG, valFPG, a, b)
                else {
                  val left = findLastNodeValue(nodeFPG, valFPG, a, lcaNodeId.get)
                  val right = findLastNodeValue(nodeFPG, valFPG, b, lcaNodeId.get)
                  (left, right) match {
                    case (Some(x), Some(y)) => Some(x max y)
                    case (x, None) => x
                    case (None, y) => y
                  }
                }
              if (distance.isDefined) dMap(productFromComponents(a, b)) = distance.get
            }
            else {
              // printf("\nInvestigating non-meet between %s and %s", a, b)
              assert(idToNode.contains(a))
              assert(idToNode.contains(b))
              val leftPath = findPath(nodeFPG, a)
              val rightPath = findPath(nodeFPG, b)
              assert (leftPath.toSet.intersect(rightPath.toSet).isEmpty)
            }
        }
      }

      (dMap, expected)
    }

  }

  def main(args: Array[String]): Unit = {

    val threadPool = Executors.newFixedThreadPool(4)
    val graph = AdjacencyListGraphReader.forIntIds("/Users/huitseeker/tmp/Weve/hostgraph/hostgraph-split", "adj.hostgraph_",
      threadPool).toArrayBasedDirectedGraph()
    threadPool.shutdown()

    printf("\nThe graph loaded from adjacency list files with %s nodes has %s directed edges.",
      graph.nodeCount, graph.edgeCount)

    val startStream = new GZIPInputStream(new BufferedInputStream(new FileInputStream("/Users/huitseeker/tmp/Weve/hostgraph/walk_sources.csv.gz")))

    val startNodes = scala.io.Source.fromInputStream(startStream).getLines().map((x) => Integer.parseInt(x)).toSeq
    val cleanStartNodes = startNodes.filter( (node) => graph.getNodeById(node).isDefined )

    val maxSteps = 500

    val graphUtils = new GraphUtils(graph)
    printf("Now doing random walks of %s steps from %s Nodes...\n", maxSteps, cleanStartNodes.size)


    val elapsed = Stopwatch.start()
    printf("\nWe have %s starting nodes from %s to %s", startNodes.size, startNodes.min, startNodes.max)
    val maxWalks = 100
    var walksDone = 0
    while (walksDone < maxWalks) {
      printf("\nStarting walk %s.", walksDone)
      val (distanceMap,expectedN) = (new DrunkardMobTraverser(graph, GraphDir.OutDir, startNodes.toArray, maxSteps, new Random())).buildDistances(elapsed)
      def expectedDistances(n: Int) = (n * (n+1)) / 2
      printf("\nWalk number %s computed %s distances out of an expected %s", walksDone, expectedN, expectedDistances(100))
      walksDone += 1
    }

     val duration = elapsed()
    printf("\nDrunk mob made %s walks in %s ms:\n", walksDone, duration.inMillis.toInt)

  }
}