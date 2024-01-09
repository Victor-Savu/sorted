module Sorted.SlowHeap

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

public export
data Heap : (0 lo: LinearOrder a rel) -> (0 _: List a) -> Type where
    Nil: Heap lo []
    Singleton: Heap lo [x]
    Balanced : (x: a) -> (leftH: Heap lo left) -> (rightH: Heap lo right) -> (balanced: length left = length right) -> (relXLeft: RelatesToAll rel x left) -> (relXRight: RelatesToAll rel x right) -> Heap lo {rel} (x :: (left ++ right))
    Imbalanced : (x: a) -> (leftH: Heap lo left) -> (rightH: Heap lo right) -> (imbalanced: length left = S (length right)) -> (relXLeft: RelatesToAll rel x left) -> (relXRight: RelatesToAll rel x right) -> Heap lo {rel} (x :: (left ++ right))

public export
HeapOf : LinearOrder a rel -> List a -> List a -> Type
HeapOf lo perm heap = (Heap lo heap, perm ~@~ heap)

public export
(::) : (x: a) -> List a # HeapOf lo xs -> List a # HeapOf lo (x::xs)
(::) {xs} x ([] # prf) = [x] # (Singleton, x :: snd prf)
(::) {xs} x ((y :: ys) # prf) = ?op_rhs_2

tail : (xs : List a) -> (lo: LinearOrder a rel) => (0 hxs: Heap lo (x::xs)) -> DecEq a => List a # HeapOf lo xs
tail [] hxs = [] # ([], reflexive @{reflexiveIsPermutationOf})
tail {rel} (y :: xs) hxs with (split xs)
  tail ([y]) hxs | SplitNil = [y] # (Singleton, Ipo id)
  tail ([y, z]) hxs | (SplitOne z) with (decEq y z)
    tail ([y, y]) hxs | (SplitOne y) | (Yes Refl) = [y, y] # (Imbalanced y Singleton [] Refl ((reflexive {rel} :: [] {rel}) {rel}) ([] {rel}), reflexive @{reflexiveIsPermutationOf})
    tail ([y, z]) hxs | (SplitOne z) | (No yNEqZ) with (connex {rel} yNEqZ)
      tail ([y, z]) hxs | (SplitOne z) | (No yNEqZ) | (Left relYZ) = [y, z] # (
        (Imbalanced y Singleton [] Refl ((relYZ :: ([] {rel})) {rel}) ([] {rel})),
        reflexive @{reflexiveIsPermutationOf})
      tail ([y, z]) hxs | (SplitOne z) | (No yNEqZ) | Right relZY = [z, y] # (
        (Imbalanced z Singleton [] Refl ((relZY :: ([] {rel})) {rel}) ([] {rel})),
        AdditionOfPermutationsCommutes {xs=[y]} {ys=[z]} $ reflexive {x=[y] ++ [z]} @{reflexiveIsPermutationOf})
  tail (y :: (z :: (ys ++ (w :: zs)))) hxs | (SplitPair z ys w zs) = ?tail_rhs_1_rhs1_2

public export
fromList : (xs: List a) -> List a # HeapOf lo xs
fromList [] = [] # ([], reflexive @{reflexiveIsPermutationOf})
fromList (x :: xs) = x :: fromList xs

covering
public export
toList : {0 rel: Rel a} -> {lo: LinearOrder a rel} -> List a # HeapOf {rel=rel} lo as -> DecEq a => (List a) # (IsSortingOf {rel=rel} lo as)
toList ([] # prf) = [] # ([], snd prf)
toList {rel} {lo} ((x :: xs) # prf) =
    let
        (xs' # soxs') = toList $ tail xs (fst prf)
    in x::xs' #
        let
            (sxs', pxs') = soxs'
            (h, pxxs) = prf
            pxxs' = x :: pxs'
            sortedXXs' = case h of
                Singleton => rewrite PermutationOfNilIsNil pxs' in Singleton
                (Balanced x leftH rightH balanced relXLeft relXRight) =>
                    ((((relXLeft ++ relXRight) {rel=rel} {e=x}) -@-> pxs') {rel=rel} :: sxs') {rel=rel}
                (Imbalanced x leftH rightH imbalanced relXLeft relXRight) =>
                    ((((relXLeft ++ relXRight) {rel=rel} {e=x}) -@-> pxs') {rel=rel} :: sxs') {rel=rel}
        in (sortedXXs', (pxxs `transitive` pxxs') @{transitiveIsPermutationOf})

covering
public export
heapSort : (as: List a) ->  DecEq a => (lo: LinearOrder a rel) => (List a) # (IsSortingOf lo as)
heapSort x = toList $ fromList x
