module Snips where

import Data.List

data Ty = A | B | C
  deriving (Eq, Show)
data Va = X | Y | Z
  deriving (Eq, Show)

nonrep :: [[Va]] -> [Ty] -> [[Va]]
nonrep [] _ = []
nonrep _ [] = []
--nonrep (vs:vss) (t:ts) = concatMap (\v -> [v] : map (v:) (nonrep (map (\xs -> delete v xs) vss) ts)) vs
nonrep ([]:vss) (t:ts) = nonrep vss ts
nonrep (vs:vss) (t:ts) = concatMap (\v -> [v] : map (v:) (nonrep vss ts)) vs


