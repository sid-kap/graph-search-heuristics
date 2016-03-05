#! /usr/bin/env stack
-- stack runghc --resolver lts-5.2 --package diagrams --package hmatrix --package containers --package pqueue --package hashtables --package monad-loops --package basic-prelude
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, NoImplicitPrelude, BangPatterns #-}

import BasicPrelude

import Data.Maybe (isJust, isNothing)
import qualified Data.Maybe as Maybe (fromJust)

import Diagrams.Prelude hiding ((<>))
import Diagrams.Backend.SVG

import Control.Monad.Loops (whileM_, unfoldrM)

import qualified Data.Array as Array
import Data.Array (Array)

import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra (Vector, Matrix)

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as V

import qualified Control.Monad.ST as ST
import qualified Data.STRef as ST

import qualified Data.PQueue.Prio.Min as PQueue
import qualified Data.HashTable.ST.Basic as HT
import qualified Data.HashTable.Class as HT (toList)

import Debug.Trace (traceShow, traceShowId)

unlessM cond val = do
  c <- cond
  unless c val

unfoldrM'' :: (Monad m) => (a -> m (Maybe a)) -> a -> m [a]
unfoldrM'' f a = unfoldrM f' a
  where
    f' x = do
      x' <- f x
      return (case x' of
        Just w  -> Just (w, w)
        Nothing -> Nothing)

-- floating point infinity
infinity :: Double
infinity = 1e100

type Potential = Vertex -> Double

data SearchResult = SearchResult
  { path    :: [Vertex]
  , prev    :: Map Vertex Vertex
  , dists   :: Map Vertex Double
  , visited :: Set Vertex
  }

main = do
  let
    -- 195
    -- seed = 284
    -- 311 is interesting
    seed = 311
    (graph, getVertexVector) = generateGraph 2000 4 seed

    s = 0
    t = 1

    manhattanDistance :: V2 Double -> V2 Double -> Double
    manhattanDistance (V2 x y) (V2 x' y') = abs (x - x') + abs (y - y')

    dijikstraPotential, euclideanPotential, manhattanPotential :: Potential
    dijikstraPotential v = 0
    euclideanPotential v = distance (getVertexVector t) (getVertexVector v)
    manhattanPotential v = manhattanDistance (getVertexVector t) (getVertexVector v)

    results = map (search graph s t) [dijikstraPotential, euclideanPotential, manhattanPotential]

    mkDiagram result = drawGraph (graph, getVertexVector, s, t, result)

    diagram = foldl1' (===) (map mkDiagram results)

  forM_ results (\res -> print (Map.lookup t (dists res)))

  renderSVG "graph.svg" (mkWidth 500) diagram

search :: Graph Double -> Vertex -> Vertex -> Potential -> SearchResult
search graph s t potential = ST.runST $ do
  heap :: ST.STRef s (PQueue.MinPQueue Double Vertex) <- ST.newSTRef (PQueue.singleton (potential s) s)
  dists   :: HT.HashTable s Vertex Double <- HT.new
  visited :: HT.HashTable s Vertex ()   <- HT.new
  prev :: HT.HashTable s Vertex Vertex  <- HT.new

  HT.insert dists s 0

  let
    loopCondition = do
      heapNotNull <- not . PQueue.null <$> ST.readSTRef heap
      tNotVisited <- isNothing <$> HT.lookup visited t
      return (heapNotNull && tNotVisited)

  whileM_ loopCondition $ do
    ((_, u), newHeap) <- PQueue.deleteFindMin <$> ST.readSTRef heap
    ST.writeSTRef heap newHeap
    unlessM (isJust <$> HT.lookup visited u) $ do
      HT.insert visited u ()
      forM_ (graph Array.! u) $ \(v, weight) -> do
        u_dist <- Maybe.fromJust <$> (HT.lookup dists u) -- u is in the heap, so it must also be in `dists`
        v_dist <- maybe infinity id <$> (HT.lookup dists v)
        when (u_dist + weight < v_dist) $ do
          HT.insert dists v (u_dist + weight)
          HT.insert prev v u
          ST.modifySTRef heap $ \h -> PQueue.insert (u_dist + weight + (potential v)) v h

  -- follow the back-pointers from `t` until the back-pointer is null
  path <- reverse . (t:) <$> unfoldrM'' (HT.lookup prev) t

  prevMap  <- Map.fromList <$> HT.toList prev
  distsMap <- Map.fromList <$> HT.toList dists
  visitedSet <- (Set.fromList . map fst) <$> HT.toList visited

  return (SearchResult path prevMap distsMap visitedSet)

spot         = circle 0.003 # fc blue  # lw 0
startSpot    = circle 0.008 # fc green # lw 0
endSpot      = circle 0.008 # fc red   # lw 0
visitedSpot  = circle 0.005 # fc lightgreen # lw 0

-- edgeStyle     = lc blue
pathEdgeStyle = lc red
seenEdgeStyle = lc gray

drawGraph :: (Graph Double, Vertex -> V2 Double, Vertex, Vertex, SearchResult) -> Diagram B
drawGraph (graph, getVertexVector, s, t, SearchResult path prev _ visited) =
  atPoints (verticesToPoints [s]) (repeat startSpot)
  <> atPoints (verticesToPoints [t]) (repeat endSpot)
  <> atPoints (verticesToPoints $ map fst $ Map.toList prev) (repeat visitedSpot)
  -- <> atPoints (verticesToPoints $ Set.toList visited) (repeat visitedSpot)
  <> mconcat pathEdges
  <> atPoints nodes (repeat spot)
  <> mconcat seenEdges
  -- <> mconcat edges
  <> square 1 # fc white # alignBL
  where
    nodes = verticesToPoints [0..length (vertices graph) - 1]

    -- edges = map (\(u,v, _) -> getVertexPoint u ~~ getVertexPoint v # edgeStyle) (getEdges graph)

    seenEdges = map (\(u,v) -> getVertexPoint u ~~ getVertexPoint v # seenEdgeStyle) (Map.toList prev)

    vectorToPoint :: V2 Double -> Point V2 Double
    vectorToPoint v = v ^. from (relative origin)

    getVertexPoint = vectorToPoint . getVertexVector
    verticesToPoints = map getVertexPoint

    pathEdges = map (\(u,v) -> getVertexPoint u ~~ getVertexPoint v # pathEdgeStyle) (zip path (tail path))

generateGraph :: Int -> Int -> LA.Seed -> (Graph Double, Vertex -> V2 Double)
generateGraph n d seed = (graphFromEdges adjacencyList, getVertex)
  where
    vectors :: Matrix Double
    vectors = LA.uniformSample seed n [(0,1), (0,1)]

    pairwiseDistances :: Matrix Double
    pairwiseDistances = LA.pairwiseD2 vectors vectors

    adjacencyList :: [(Int, [(Int, Double)])]
    adjacencyList =
      let
        rows = LA.toRows pairwiseDistances

        -- call `tail` to remove self-loops (since the closest point will always
        -- be the point itself)
        toPairs row =
          zip ((take d . tail . map fromIntegral . LA.toList . LA.sortIndex) row)
              ((take d . tail . LA.toList . LA.sortVector) row)
      in
        zip [0..] (map toPairs rows)

    vectorToV2 :: Numeric.LinearAlgebra.Vector Double -> V2 Double
    vectorToV2 v = let v' = LA.toList v in V2 (v' !! 0) (v' !! 1)

    getVertex :: Int -> V2 Double
    getVertex v = (map vectorToV2 (LA.toRows vectors)) !! v

type Vertex  = Int
type Graph a = Array Vertex [(Vertex, a)]
type Edge a  = (Vertex, Vertex, a)

graphFromEdges :: [(Vertex, [(Vertex, a)])] -> Graph a
graphFromEdges edges = Array.array bounds edges
  where
    bounds = (0, length edges - 1)

-- | All vertices of a graph.
vertices :: Graph a -> [Vertex]
vertices = Array.indices

-- | All edges of a graph.
getEdges :: Graph a -> [Edge a]
getEdges g = [ (v, w, a) | v <- vertices g, (w, a) <- g Array.! v ]
