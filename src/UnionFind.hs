module UnionFind where

import AST (Type (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

data UnionFind = UnionFind
  { parent :: Map Type Type,
    rank :: Map Type Int
  }
  deriving (Show)

mkUnionFind :: [Type] -> UnionFind
mkUnionFind elems =
  UnionFind
    { parent = Map.fromList [(x, x) | x <- elems],
      rank = Map.fromList [(x, 0) | x <- elems]
    }

find :: UnionFind -> Type -> Type
find uf x = case Map.lookup x (parent uf) of
  Nothing -> x
  Just p
    | p == x -> p
    | otherwise -> find uf p

unionBy :: (Type -> Int) -> UnionFind -> Type -> Type -> UnionFind
unionBy level uf x y =
  let rootX = find uf x
      rootY = find uf y
  in if rootX == rootY
      then uf
      else
        case compare (level rootX) (level rootY) of
          GT ->
            let newParent = Map.insert rootY rootX (parent uf)
            in uf {parent = newParent}
          LT ->
            let newParent = Map.insert rootX rootY (parent uf)
            in uf {parent = newParent}
          EQ ->
            let rankX = Map.findWithDefault 0 rootX (rank uf)
                rankY = Map.findWithDefault 0 rootY (rank uf)
            in case compare rankX rankY of
              LT ->
                let newParent = Map.insert rootX rootY (parent uf)
                in uf {parent = newParent}
              GT ->
                let newParent = Map.insert rootY rootX (parent uf)
                in uf {parent = newParent}
              EQ ->
                let newParent = Map.insert rootY rootX (parent uf)
                    newRank = Map.insert rootX (rankX + 1) (rank uf)
                in uf {parent = newParent, rank = newRank}
