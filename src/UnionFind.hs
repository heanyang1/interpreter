{-# LANGUAGE DeriveGeneric #-}
module UnionFind where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (foldl')
import GHC.Generics (Generic)

instance Eq a => Eq (UnionFind a) where
    _ == _ = False

data UnionFind a = UnionFind
    { parent :: Map a a
    , rank :: Map a Int
    }
    deriving (Show, Generic)

mkUnionFind :: (Ord a, Show a) => [a] -> UnionFind a
mkUnionFind elems = UnionFind
    { parent = Map.fromList [(x, x) | x <- elems]
    , rank = Map.fromList [(x, 0) | x <- elems]
    }

find :: (Ord a, Show a) => UnionFind a -> a -> Either String a
find uf x = case Map.lookup x (parent uf) of
    Nothing -> Left (show x ++ " is not in the union-find")
    Just p
        | p == x -> Right p
        | otherwise -> do
            root <- find uf p
            let newParent = Map.insert x root (parent uf)
            return root

union :: (Ord a, Show a) => UnionFind a -> a -> a -> Either String (UnionFind a, a)
union uf x y = do
    rootX <- find uf x
    rootY <- find uf y
    if rootX == rootY
        then return (uf, rootX)
        else do
            let rankX = Map.findWithDefault 0 rootX (rank uf)
            let rankY = Map.findWithDefault 0 rootY (rank uf)
            case compare rankX rankY of
                LT -> do
                    let newParent = Map.insert rootX rootY (parent uf)
                    return (uf {parent = newParent}, rootY)
                GT -> do
                    let newParent = Map.insert rootY rootX (parent uf)
                    return (uf {parent = newParent}, rootX)
                EQ -> do
                    let newParent = Map.insert rootY rootX (parent uf)
                    let newRank = Map.insert rootX (rankX + 1) (rank uf)
                    return (uf {parent = newParent, rank = newRank}, rootX)

connected :: (Ord a, Show a) => UnionFind a -> a -> a -> Either String Bool
connected uf x y = do
    rootX <- find uf x
    rootY <- find uf y
    return (rootX == rootY)