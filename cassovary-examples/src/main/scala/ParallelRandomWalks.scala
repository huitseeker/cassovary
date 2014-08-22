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
import scala.collection.mutable
import scala.annotation.tailrec
import scala.collection.breakOut
import it.unimi.dsi.fastutil.longs.{Long2IntMap, Long2IntOpenHashMap}

object ParallelRandomWalks {

  class DrunkardMobTraverser(graph: Graph, dir: GraphDir, homeNodeIds: Array[Int],
    maxSteps: Int, randNumGen: Random = new Random) {

    val debug = true

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
          // smallestSource is still walking
          assert(walks(smallestSourceIdx) != -1)
        case _ => {}
      }
    }
    private var hasRun = false
    private var nonCoalesced = 0
    def run(): (IntInfoKeeper, IntInfoKeeper) = {
      if (!hasRun) {
        var stepsTaken = 0
        var allFinished = false
        var walksCounter = 0
        while (stepsTaken < maxSteps && !allFinished) {
          if (debug) walksCounter = walks.filter(_ != -1).size
          takeRandomStep(walks)
          if (debug) walksCounter -= walks.filter(_ != -1).size
          if (debug) nonCoalesced += walksCounter
          coalesceStep(walks, stepsTaken)
          stepsTaken += 1
          allFinished = walks.forall(_ == -1)
        }
        if (debug) {
          nonCoalesced += walks.filter(_ != -1).size
          printf("\nAt end of walk, %s walkers still walking", walks.filter(_ != -1).size)
        }
        hasRun = true
      }
      (nodeFPG, valFPG)
    }

    class UnionFind[T]() {

      private val parent: mutable.Map[T, T] = new mutable.HashMap[T, T] {
        override def default(s: T) = {
          get(s) match {
            case Some(v) => v
            case None => put(s, s); s
          }
        }
      }

      private val rank: mutable.Map[T, Int] = new mutable.HashMap[T, Int] {
        override def default(s: T) = {
          get(s) match {
            case Some(v) => v
            case None => put(s, 1); 1
          }
        }
      }

      def size(): Int = parent.keys.size

      /**
       * Return the parent (representant) of the equivalence class.
       * Uses path compression.
       */
      def find(s: T): T = {
        val ps = parent(s)
        if (ps == s) s else {
          parent(s) = find(ps)
          parent(s)
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

    case class TreeNode(val id: Int, var children: List[Int], var coloured: Boolean, var ancestor: Option[Int])

    // Let's build an Iterator for this one, so as not to store it in memory
    private def pairsAsLongIterator(l: List[Int]): Iterator[Long] = new Iterator[Long] {
      var unusedHeads: List[Int] = if (l.isEmpty) Nil else l.tail
      var chosenHeadList: List[Long] = if (l.isEmpty) Nil else for (y <- l.tail) yield productFromComponents(l.head, y)
      override def hasNext(): Boolean = {
        !(chosenHeadList.isEmpty && unusedHeads.size <= 1)
      }
      override def next(): Long = {
        if (chosenHeadList.isEmpty){
          // unusedHeads nonEmpty
          val x = unusedHeads.head
          chosenHeadList = for (y <- unusedHeads.tail) yield productFromComponents(x, y)
          unusedHeads = unusedHeads.tail
        }
        val res = chosenHeadList.head
        chosenHeadList = chosenHeadList.tail
        res
      }

    }

    // Encode info about pairs of Ints as Longs
    def productFromComponents(x: Int, y: Int) = ((x.toLong) << 32) | (y.toLong & 0xffffffffL)
    def pairFromLong(l: Long) = ((l >>32).toInt, l.toInt)

    def runLCA(P: Iterator[Long], uId: Int, lcaMap: Long2IntMap, idToNode: mutable.Map[Int, TreeNode], uf: UnionFind[Int]): Unit = {
      val u = idToNode(uId)
      uf.find(uId)
      u.ancestor = Some(uId)
      u.children foreach { node =>
        runLCA(P, node, lcaMap, idToNode, uf)
        uf.union(uId, node)
        idToNode(uf.find(uId)).ancestor = Some(uId)
      }
      u.coloured = true
      P foreach { pairFromLong(_) match {
          case (a,b) =>
            if (a == uId && idToNode(b).coloured) lcaMap(productFromComponents((a min b), (a max b))) = idToNode(uf.find(b)).ancestor.get
            if (b == uId && idToNode(a).coloured) lcaMap(productFromComponents((a min b), (a max b))) = idToNode(uf.find(a)).ancestor.get
        }
      }
    }

    def buildDistances(watch: Stopwatch.Elapsed): (Long2IntMap, Int) = {
      val dMap = new Long2IntOpenHashMap()

      val (nodeFPG, valFPG) = run()
      if (debug) printf("\nFinished building the FPG at %s milis. It holds %s nodes (expected %s).", watch().inMillis.toInt, nodeFPG.infoAllNodes.values.size(), homeNodeIds.size - nonCoalesced)

      val idToNode = new mutable.HashMap[Int, TreeNode]()

      @tailrec
      def findLastEdgeValue(nodeTable: IntInfoKeeper, valueTable: IntInfoKeeper, sourceNode: Int, stopNode: Int): Option[Int] = {
        val next = nodeTable.infoOfNode(sourceNode)
        if (!next.isDefined) None
        else {
          assert(next.get != sourceNode)
          if (next.get == stopNode) valueTable.infoOfNode(sourceNode)
          else findLastEdgeValue(nodeTable, valueTable, next.get, stopNode)
        }
      }

      @tailrec
      def seenIds(l: List[TreeNode], seen: Set[Int] = Set()): Set[Int] = l match {
        case Nil => seen
        case t :: ts => seenIds(ts ++ t.children.map(idToNode(_)), seen + t.id)
      }

      @tailrec
      def findPath(nodeTable: IntInfoKeeper, sourceNode: Int, res:List[Int] = Nil): List[Int] = {
        val next = nodeTable.infoOfNode(sourceNode)
        if (!next.isDefined || res.size > 100) sourceNode :: res
        else {
          assert(next.get != -1)
          assert(sourceNode != next.get)
          findPath(nodeTable, next.get, sourceNode :: res)
        }
      }

      nodeFPG.infoAllNodes foreach {
        case (nodeId, parentId) =>
          assert(parentId != nodeId)
          assert(parentId < nodeId)
          // the first node has no parent to attach to
          if (!idToNode.contains(parentId)) idToNode(parentId) = TreeNode(parentId, List(), false, None)
          idToNode(parentId).children = nodeId :: idToNode(parentId).children
          if (!idToNode.contains(nodeId)) idToNode(nodeId) = TreeNode(nodeId, List(), false, None)
      }

      // Do not use an UF 'naively' here : it may give you the correct component, but may not give you the root as its class' representant
      val childrenIds = (nodeFPG.infoAllNodes.keys.map((x) => x:Int)).toSet
      val rootIds = (idToNode.keys.toSet &~ childrenIds.toSet)

      // DEBUG printing for Tree construction
      if (debug) {
        printf("\nThe FPG contains %s nodes in %s connected components.", nodeFPG.infoAllNodes.keys.size(), rootIds.size)

        val seenFromRoots = seenIds(rootIds.map(idToNode(_)).toList)
        val notSeen = (idToNode.keys.toSet &~ seenFromRoots)

        if (notSeen.nonEmpty) {
          printf("\n\t BUG: %s nodes not seen from Roots.", notSeen.size)
          val rng = new Random
          val indices = List.tabulate(10)((n) => rng.nextInt(notSeen.size))
          for (i <- indices)
            printf("\n\t Example problematic path: source %s, path %s", notSeen.toList(i), findPath(nodeFPG, notSeen.toList(i)).map { (node) => (node, idToNode(node).children.sorted) }.toString())
        }
      }
      // END DEBUG

      val lcaMap = new Long2IntOpenHashMap()
      val base = homeNodeIds filter {idToNode.contains(_)} take 100
      def pairs = pairsAsLongIterator(base.sorted.toList)

      // DEBUG printing for tree construction
      if (debug) {
        @tailrec
        def treeCount(l: List[TreeNode], nodesSeen: Int = 0): Int = l match {
          case Nil => nodesSeen
          case t :: ts => treeCount(ts ++ t.children.map(idToNode(_)), nodesSeen + 1)
        }

        // the roots are in the node table, yet are not listed in nodeFPG (they have no parent)
        printf("\nThe Node table contains %s nodes, expected %s.", idToNode.keys.size, nodeFPG.infoAllNodes.keys.size() + rootIds.size)
        printf("\nThe Node table contains %s children, expected %s.", idToNode.values.map((node) => node.children.size).sum, nodeFPG.infoAllNodes.keys.size())
        printf("\nThe FPG tree contains %s nodes, expected %s.", treeCount(rootIds.map(idToNode(_)).toList), nodeFPG.infoAllNodes.keys.size() + rootIds.size)
      }
      // END DEBUG

      var pairsExpected = 0
      rootIds foreach { rId =>
        if (seenIds(List(idToNode(rId))).size > 1) {
          var lcaAdded = 0
          if (debug) lcaAdded -= lcaMap.size()
          def soughtPairs = pairsAsLongIterator(seenIds(List(idToNode(rId))).toList.sorted)
          if (debug) {
            val seenIdsSize = seenIds(List(idToNode(rId))).size
            def expectedDistances(n: Int) = (n * (n-1)) / 2
            assert (soughtPairs.size == expectedDistances(seenIdsSize))
          }
          if (debug) assert(soughtPairs.forall(pairFromLong(_) match { case (a,b) => idToNode.get(a).isDefined && idToNode.get(b).isDefined}))
          val uf = new UnionFind[Int]()
          runLCA(soughtPairs, rId, lcaMap, idToNode, uf)
          assert(uf.size() == seenIds(List(idToNode(rId))).size)
          pairsExpected += soughtPairs.size
          if (debug) {
            assert(seenIds(List(idToNode(rId))) forall { (id) =>
              idToNode(id).coloured
            })
          }
          if (debug) lcaAdded += lcaMap.size()
          if (false) assert(lcaAdded == soughtPairs.size)
        }
      }
      if (debug) printf("\n The LCA map records %s intersections, expected to account for %s distances.", lcaMap.size, pairsExpected)

      var expected = 0
      var missed = 0
      pairs foreach {
        pairFromLong(_) match {
          case (a, b) =>
            if (lcaMap.containsKey(productFromComponents(a,b))) {
            // They meet !
              val lcaNodeId = lcaMap.get(productFromComponents(a, b))

              expected += 1
              val distance: Option[Int] =
                if (lcaNodeId == a) findLastEdgeValue(nodeFPG, valFPG, b, a)
                else if (lcaNodeId == b) findLastEdgeValue(nodeFPG, valFPG, a, b)
                else {
                  val left = findLastEdgeValue(nodeFPG, valFPG, a, lcaNodeId)
                  val right = findLastEdgeValue(nodeFPG, valFPG, b, lcaNodeId)
                  (left, right) match {
                    case (Some(x), Some(y)) => Some(x max y)
                    case (x, None) => x
                    case (None, y) => y
                  }
                }
              if (distance.isDefined) dMap(productFromComponents(a, b)) = distance.get
            }
            else if (debug) {
              // printf("\nInvestigating non-meet between %s and %s", a, b)
              assert(idToNode.contains(a))
              assert(idToNode.contains(b))
              val leftPath = findPath(nodeFPG, a)
              val rightPath = findPath(nodeFPG, b)
              if (leftPath.toSet.intersect(rightPath.toSet).nonEmpty) missed += 1
            }
        }
      }
      if (debug && missed > 0) printf("\n\t BUG in the LCA algorithm ! Missed %s intersections", missed)

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

    val maxSteps = 100

    val graphUtils = new GraphUtils(graph)
    printf("\n Now doing random walks of %s steps from %s Nodes...\n", maxSteps, cleanStartNodes.size)


    val elapsed = Stopwatch.start()
    val maxWalks = 100
    var walksDone = 0
    while (walksDone < maxWalks) {
      printf("\nStarting walk %s. Expecting %s nodes to walk.", walksDone, cleanStartNodes.size)
      val (distanceMap,expectedN) = (new DrunkardMobTraverser(graph, GraphDir.OutDir, cleanStartNodes.toArray, maxSteps, new Random())).buildDistances(elapsed)
      printf("\nWalk number %s computed %s distances.", walksDone, expectedN)
      walksDone += 1
      if (walksDone % 5 == 0) assert(false)
    }

     val duration = elapsed()
    printf("\nDrunk mob made %s walks in %s ms:\n", walksDone, duration.inMillis.toInt)

  }
}