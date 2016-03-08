{-# LANGUAGE OverloadedStrings, ScopedTypeVariables, NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}

import BasicPrelude

import Data.Maybe (isJust, isNothing)
import qualified Data.Maybe as Maybe (fromJust, catMaybes)
import Data.List.Split (chunksOf)

import Diagrams.Prelude hiding ((<>))
-- import Diagrams.Backend.SVG
import Diagrams.Backend.Cairo

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
import System.Random (randomIO)
import qualified Control.Exception (catch)
import GHC.Exception (ErrorCall)

main :: IO ()
main = replicateM_ 20 (Control.Exception.catch doPart1 (\(e::ErrorCall) -> return ()))
  where
    doPart1 = do
      part1
      putStrLn ""

part1 :: IO ()
part1 = do
  seed <- randomIO
  let
    -- 195
    -- seed = 284
    -- 311 is interesting
    -- seed = 154
    -- seed = 1042
    (graph, getVertexVector) = generateGraph 2000 4 seed

    s = 0
    t = 1

    manhattanDistance :: V2 Double -> V2 Double -> Double
    manhattanDistance (V2 x y) (V2 x' y') = abs (x - x') + abs (y - y')

    dijikstraPotential, euclideanPotential, manhattanPotential :: Potential
    dijikstraPotential v = 0
    euclideanPotential v = distance (getVertexVector t) (getVertexVector v)
    manhattanPotential v = manhattanDistance (getVertexVector t) (getVertexVector v)

    landmarks = [103..122]
    landmarkPotential = mkLandmarkPotential graph landmarks

    potentials = [ ("Dijikstra", dijikstraPotential)
                 , ("Euclidean", euclideanPotential)
                 , ("Manhattan", manhattanPotential)
                 , ("ALT",       landmarkPotential t)]

    results = map
      (\(name, potential) -> (name, search graph s (Just t) potential)) potentials

    mkDiagram :: (Text, SearchResult) -> Diagram B
    mkDiagram (name, result) = drawGraph name (graph, getVertexVector, s, t, result)

    wholeGraph = drawWholeGraph (graph, getVertexVector, s, t)
    diagram = foldl1' (===) $ map (foldl1' (|||)) $ chunksOf 2 (wholeGraph:(map mkDiagram results))

    getPathLength :: [Vertex] -> Double
    getPathLength xs = sum $ map (\(u,v) -> distance (getVertexVector u) (getVertexVector v)) (zip xs (tail xs))

    showResult :: (Text, SearchResult) -> IO ()
    showResult (text, res) = putStrLn (text <> ": searched " <> (show numNodesSearched) <> " nodes, " <> (show numEdgesSearched) <> " edges; distance " <> (show distance))
      where
        numNodesSearched = length (visited res)
        numEdgesSearched = sum [ w | v <- Set.toList (visited res) , (_,w) <- graph Array.! v ]
        distance = Maybe.fromJust $ Map.lookup t (dists res)

  mapM_ showResult results

  -- renderSVG "graph.svg" (mkWidth 1000) diagram
  -- renderCairo "graph.png" (mkWidth 1000) diagram

mkLandmarkPotential graph landmarks = landmarkPotential
  where
    landmarkResults = map (\l -> search graph l Nothing (const 0)) landmarks

    landmarkPotential t u =
      case Maybe.catMaybes maybePairs of
        [] -> 0
        -- xs -> maximum (map abs xs)
        xs -> maximum xs
      where
        -- if one is Nothing, make it nothing. Not sure if this is how it's supposed
        -- to be implemented, but it works!
        maybePairs =
          [ (subtract) <$> Map.lookup u dists' <*> Map.lookup t dists'
          | SearchResult _ _ dists' _ <- landmarkResults ]

part2 = do
  let
    -- seeds = [400..410]
    -- seeds = [400]

    -- s = 0
    -- t = 1

    -- the points are random anyway, let's choose points 3 to 22 as our "random" landmarks
    landmarks = [103..122]

    landmarkPotential = mkLandmarkPotential graph landmarks

    seed = 314
    (graph, vertexToVector) = generateGraph 2000 4 seed

    results = map (\l -> search graph l Nothing (const 0)) landmarks

    diagrams :: [Diagram B]
    diagrams
      = map (\(s,t) -> makeAltGraph (graph, vertexToVector) landmarks (landmarkPotential t) (s,t))
          [ (12, 13)
          , (14, 15)
          , (16, 17)
          , (18, 19)
          , (20, 21)
          , (22, 23) ]

    diagram = foldl1' (===) diagrams

  renderCairo "alt.png" (mkWidth 1000) diagram
  -- renderSVG "alt.svg" (mkWidth 1000) diagram
  -- putStrLn "hi"

makeAltGraph :: (Graph Double, Vertex -> V2 Double) -> [Vertex] -> Potential -> (Vertex, Vertex) -> Diagram B
makeAltGraph (graph, vertexToVector) landmarks potential (s,t) =
  let
    result = search graph s (Just t) potential
    diagram = drawGraph "ALT" (graph, vertexToVector, s, t, result)

    -- Landmarks dots that we will superimpose on the graph
    landmarksDiagram :: Diagram B
    landmarksDiagram = atPoints
      (map (vectorToPoint . vertexToVector) landmarks)
      (repeat landmarkSpot)

    euclideanResult = search graph s (Just t) (\u -> distance (vertexToVector u) (vertexToVector t))
    euclideanDiagram = drawGraph "Euclidean" (graph, vertexToVector, s, t, euclideanResult)
  in
    euclideanDiagram ||| (landmarksDiagram <> diagram)

-------------------------------------------------------------
-- Helper functions
-------------------------------------------------------------

unlessM cond val = do
  c <- cond
  unless c val

unfoldrM'' :: (Monad m) => (a -> m (Maybe a)) -> a -> m [a]
unfoldrM'' f a = unfoldrM f' a
  where
    f' x = do
      !x' <- f x
      return (case x' of
        Just !w -> Just (w, w)
        Nothing -> Nothing)

-- floating point infinity
infinity :: Double
infinity = 1e100

fromJust' :: String -> Maybe a -> a
fromJust' message a = case a of
  Just a' -> a'
  Nothing -> error ("fromJust: Nothing. Message: " <> message)

-----------------------------------------------------------
-- Actual stuff
-----------------------------------------------------------

type Potential = Vertex -> Double

data SearchResult = SearchResult
  { path    :: !(Maybe [Vertex])
  , prev    :: !(Map Vertex Vertex)
  , dists   :: !(Map Vertex Double)
  , visited :: !(Set Vertex)
  }

-- If t = Nothing, finds single source shortest path from s.
-- If t = Just t', quits once it finds the shortest path from s to t.
search :: Graph Double -> Vertex -> Maybe Vertex -> Potential -> SearchResult
search graph s t potential = ST.runST $ do
  heap :: ST.STRef s (PQueue.MinPQueue Double Vertex) <- ST.newSTRef (PQueue.singleton (potential s) s)
  dists   :: HT.HashTable s Vertex Double  <- HT.newSized 2000
  visited :: HT.HashTable s Vertex ()      <- HT.newSized 2000
  prev    :: HT.HashTable s Vertex Vertex  <- HT.newSized 2000

  HT.insert dists s 0

  let
    loopCondition = do
      heapNotNull <- not . PQueue.null <$> ST.readSTRef heap

      -- If there is an end, quit when we find the end node.  Otherwise,
      -- continue until we find the whole connected component of s.
      case t of
        Just t' -> do
          tNotVisited <- isNothing <$> HT.lookup visited t'
          return (heapNotNull && tNotVisited)
        Nothing ->
          return heapNotNull

  whileM_ loopCondition $ do
    ((_, u), newHeap) <- PQueue.deleteFindMin <$> ST.readSTRef heap
    ST.writeSTRef heap newHeap
    unlessM (isJust <$> HT.lookup visited u) $ do
      HT.insert visited u ()
      forM_ (graph Array.! u) $ \(!v, !weight) -> do
        !u_dist <- (fromJust' "u is in the heap") <$> (HT.lookup dists u) -- u is in the heap, so it must also be in `dists`
        !v_dist <- maybe infinity id <$> (HT.lookup dists v)
        when (u_dist + weight < v_dist) $ do
          HT.insert dists v $! (u_dist + weight)
          HT.insert prev v u
          ST.modifySTRef heap $ \h -> PQueue.insert (u_dist + weight + (potential v)) v h

  -- follow the back-pointers from `t` until the back-pointer is null
  path <- (case t of
    Just t' -> Just . reverse . (t':) <$> unfoldrM'' (HT.lookup prev) t'
    Nothing -> return Nothing)

  prevMap  <- Map.fromList <$> HT.toList prev
  distsMap <- Map.fromList <$> HT.toList dists
  visitedSet <- (Set.fromList . map fst) <$> HT.toList visited

  return (SearchResult path prevMap distsMap visitedSet)

spot         = circle 0.003 # fc blue  # lw 0
startSpot    = circle 0.015 # fc green # lw 0
endSpot      = circle 0.015 # fc red   # lw 0
visitedSpot  = circle 0.005 # fc lightgreen # lw 0
landmarkSpot = square 0.030 # fc black # lw 0

edgeStyle     = lc blue # lw 0.1
pathEdgeStyle = lc red
seenEdgeStyle = lc gray

drawGraph :: Text -> (Graph Double, Vertex -> V2 Double, Vertex, Vertex, SearchResult) -> Diagram B
drawGraph name (graph, getVertexVector, s, t, SearchResult path prev _ visited) =
  (position [(vertexToPoint s, startSpot), (vertexToPoint t, endSpot)]
  <> atPoints (map (vertexToPoint . fst) $ Map.toList prev) (repeat visitedSpot) -- was visited
  <> mconcat pathEdges
  <> atPoints nodes (repeat spot)
  <> mconcat seenEdges
  <> square 1 # fc white # alignBL)
  === txt
  where
    nodes = map vertexToPoint [0..length (vertices graph) - 1]

    seenEdges = map (\(u,v) -> vertexToPoint u ~~ vertexToPoint v # seenEdgeStyle) (Map.toList prev)
    pathEdges =
      case path of
        Just p -> map (\(u,v) -> vertexToPoint u ~~ vertexToPoint v # pathEdgeStyle) (zip p (tail p))
        Nothing -> []

    vertexToPoint :: Vertex -> Point V2 Double
    vertexToPoint = vectorToPoint . getVertexVector

    txt = strut (V2 0 0.05) <> text (textToString (name <> ": " <> (show numNodesSearched) <> " nodes searched")) # fontSize 18 # translate (V2 0.5 0)
    numNodesSearched = length visited

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
vectorToPoint !v = v ^. from (relative origin)

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
    vectorToV2 !v = let v' = LA.toList v in V2 (v' !! 0) (v' !! 1)

    getVertex :: Int -> V2 Double
    getVertex !v = (map vectorToV2 (LA.toRows vectors)) !! v

------------------------------------------------------------------------
-- Weighted graphs.
-- Based on Data.Graph, but modified to allow for weighted edges.
------------------------------------------------------------------------

type Vertex  = Int
type Graph a = Array Vertex [(Vertex, a)]
type Edge a  = (Vertex, Vertex, a)

graphFromEdges :: [(Vertex, [(Vertex, a)])] -> Graph a
graphFromEdges !edges = Array.array bounds edges
  where
    bounds = (0, length edges - 1)

-- | All vertices of a graph.
vertices :: Graph a -> [Vertex]
vertices = Array.indices

-- | All edges of a graph.
getEdges :: Graph a -> [Edge a]
getEdges g = [ (v, w, a) | v <- vertices g, (w, a) <- g Array.! v ]
