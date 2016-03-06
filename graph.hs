#! /usr/bin/env stack
-- stack runghc --resolver lts-5.2 --package diagrams --package hmatrix --package containers --package pqueue --package hashtables --package monad-loops --package basic-prelude
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, NoImplicitPrelude #-}
-- {-# LANGUAGE BangPatterns #-}

import BasicPrelude

import Data.Maybe (isJust, isNothing)
import qualified Data.Maybe as Maybe (fromJust)
import Data.List.Split (chunksOf)

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

main = do
  let
    -- 195
    -- seed = 284
    -- 311 is interesting
    -- seed = 154
    seed = 1042
    (graph, getVertexVector) = generateGraph 2000 4 seed

    s = 0
    t = 1

    manhattanDistance :: V2 Double -> V2 Double -> Double
    manhattanDistance (V2 x y) (V2 x' y') = abs (x - x') + abs (y - y')

    dijikstraPotential, euclideanPotential, manhattanPotential :: Potential
    dijikstraPotential v = 0
    euclideanPotential v = distance (getVertexVector t) (getVertexVector v)
    manhattanPotential v = manhattanDistance (getVertexVector t) (getVertexVector v)

    potentials = [dijikstraPotential, euclideanPotential, manhattanPotential]

    results = map (search graph s t) potentials

    mkDiagram result = drawGraph (graph, getVertexVector, s, t, result)

    wholeGraph = drawWholeGraph (graph, getVertexVector, s, t)
    diagram = foldl1' (===) $ map (foldl1' (|||)) $ chunksOf 2 (wholeGraph:(map mkDiagram results))

    getPathLength :: [Vertex] -> Double
    getPathLength xs = sum $ map (\(u,v) -> distance (getVertexVector u) (getVertexVector v)) (zip xs (tail xs))

  forM_ (zip potentials results) (\(potential, res) -> print (Map.lookup t (dists res)))

  renderSVG "graph.svg" (mkWidth 500) diagram

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

search :: Graph Double -> Vertex -> Vertex -> Potential -> SearchResult
search graph s t potential = ST.runST $ do
  heap :: ST.STRef s (PQueue.MinPQueue Double Vertex) <- ST.newSTRef (PQueue.singleton (potential s) s)
  dists   :: HT.HashTable s Vertex Double  <- HT.new
  visited :: HT.HashTable s Vertex ()      <- HT.new
  prev    :: HT.HashTable s Vertex Vertex  <- HT.new

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
startSpot    = circle 0.015 # fc green # lw 0
endSpot      = circle 0.015 # fc red   # lw 0
visitedSpot  = circle 0.005 # fc lightgreen # lw 0

edgeStyle     = lc blue # lw 0.1
pathEdgeStyle = lc red
seenEdgeStyle = lc gray

drawGraph :: (Graph Double, Vertex -> V2 Double, Vertex, Vertex, SearchResult) -> Diagram B
drawGraph (graph, getVertexVector, s, t, SearchResult path prev _ visited) =
  position [(vertexToPoint s, startSpot), (vertexToPoint t, endSpot)]
  <> atPoints (map (vertexToPoint . fst) $ Map.toList prev) (repeat visitedSpot) -- was visited
  <> mconcat pathEdges
  <> atPoints nodes (repeat spot)
  <> mconcat seenEdges
  <> square 1 # fc white # alignBL
  where
    nodes = map vertexToPoint [0..length (vertices graph) - 1]

    seenEdges = map (\(u,v) -> vertexToPoint u ~~ vertexToPoint v # seenEdgeStyle) (Map.toList prev)
    pathEdges = map (\(u,v) -> vertexToPoint u ~~ vertexToPoint v # pathEdgeStyle) (zip path (tail path))

    vertexToPoint :: Vertex -> Point V2 Double
    vertexToPoint = vectorToPoint . getVertexVector

drawWholeGraph :: (Graph Double, Vertex -> V2 Double, Vertex, Vertex) -> Diagram B
drawWholeGraph (graph, getVertexVector, s, t) =
  position [(vertexToPoint s, startSpot), (vertexToPoint t, endSpot)]
  <> atPoints nodes (repeat spot)
  <> mconcat edges
  <> square 1 # fc white # alignBL
  where
    nodes = map vertexToPoint [0..length (vertices graph) - 1]

    edges = map (\(u,v, _) -> vertexToPoint u ~~ vertexToPoint v # edgeStyle) (getEdges graph)

    vertexToPoint :: Vertex -> Point V2 Double
    vertexToPoint = vectorToPoint . getVertexVector

vectorToPoint :: V2 Double -> Point V2 Double
vectorToPoint v = v ^. from (relative origin)

generateGraph :: Int -> Int -> LA.Seed -> (Graph Double, Vertex -> V2 Double)
generateGraph n d seed = (graphFromEdges adjacencyList, getVertex)
  where
    vectors :: Matrix Double
    vectors = LA.uniformSample seed n [(0,1), (0,1)]

    pairwiseSquaredDistances :: Matrix Double
    pairwiseSquaredDistances = LA.pairwiseD2 vectors vectors

    adjacencyList :: [(Int, [(Int, Double)])]
    adjacencyList =
      let
        rows = LA.toRows pairwiseSquaredDistances

        -- call `tail` to remove self-loops (since the closest point will always
        -- be the point itself)
        toPairs row =
          zip ((take d . tail . map fromIntegral . LA.toList . LA.sortIndex) row)
              ((map sqrt . take d . tail . LA.toList . LA.sortVector) row)
      in
        zip [0..] (map toPairs rows)

    vectorToV2 :: Numeric.LinearAlgebra.Vector Double -> V2 Double
    vectorToV2 v = let v' = LA.toList v in V2 (v' !! 0) (v' !! 1)

    getVertex :: Int -> V2 Double
    getVertex v = (map vectorToV2 (LA.toRows vectors)) !! v

------------------------------------------------------------------------
-- Weighted graphs.
-- Based on Data.Graph, but modified to allow for weighted edges.
------------------------------------------------------------------------

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
