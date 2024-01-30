module Sorted.Heap

import Control.Order
import Control.Relation
import Data.Fin
import Data.List.Views
import Data.Nat
import Data.Void

import Sorted.IsPermutationOf
import Sorted.IsSortingOf
import Sorted.Prop
import Sorted.Relates
import Sorted.Sorted

%default total

ford : (0 _: a = b) -> a -> b
ford Refl = id

export
Maybe' : Nat -> Type -> Type
Maybe' 0 _ = Void
Maybe' (S _) ty = ty

export
data Heap : LinearOrder a rel => (0 n: Nat) -> (0 h: Maybe' n a) -> Type where
    Nil : Heap @{lo} 0 _
    Singleton: (h: a) -> Heap @{lo} {a} 1 h
    Prick : (h: a) -> (s: a) -> (0 hs: rel h s) -> Heap @{lo} {rel} 2 h
    Balanced : (h: a) -> (0 hl: rel h l) -> (0 hr: rel h r) -> (left: Heap @{lo} (1+m) l) -> (right: Heap @{lo} (1+m) r) -> Heap @{lo} {rel} (3+m+m) h
    Imbalanced : (h: a) -> (0 hl: rel h l) -> (0 hr: rel h r) -> (left: Heap @{lo} (2 + m) l) -> (right: Heap @{lo} (1+m) r) -> Heap @{lo} {rel} (4+m+m) h

-- LinearOrder a rel => Container a (Heap {a} {rel} n h) where
--     x .#. Nil = 0

-- export
-- fromList : (xs: List a) -> List a # HeapOf lo xs
-- fromList [] = [] # ([], reflexive @{reflexiveIsPermutationOf})
-- fromList (x :: xs) = x :: fromList xs


-- covering
-- export
-- heapSort : (as: List a) ->  DecEq a => (lo: LinearOrder a rel) => (List a) # (IsSortingOf lo as)
-- heapSort x = toList $ fromList x
