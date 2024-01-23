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
Maybe' 0 _ = Unit
Maybe' (S _) ty = ty

export
data Heap : (0 n: Nat) -> (0 lo: LinearOrder a rel) -> (0 h: Maybe' n a) -> Type where
    Nil : Heap 0 lo {rel} {a} ()
    Singleton: Heap 1 lo {rel} {a} h
    Prick : (h: a) -> (s: a) -> (0 hs: rel h s) -> Heap 2 lo {rel} {a} h
    Balanced : (h: a) -> (0 hl: rel h l) -> (0 hr: rel h r) -> (left: Heap (1+m) lo {rel} {a} l) -> (right: Heap (1+m) lo {rel} {a} r) -> Heap (3+m+m) lo {rel} {a} h
    Imbalanced : (h: a) -> (0 hl: rel h l) -> (0 hr: rel h r) -> (left: Heap (2 + m) lo {rel} {a} l) -> (right: Heap (1+m) lo {rel} {a} r) -> Heap (4+m+m) lo {rel} {a} h

export
data OccursH : a -> Nat -> Heap n lo {rel} {a} h -> Type where
    ||| A proof that the occurrent is not in the empty heap
    Nowhere : OccursH occurrent 0 [] {lo} {rel} {a}
    ||| A proof that the occurrent is not in the singleton heap
    NSingleton: Not (occurrent=notTheOccurrent) -> OccursH occurrent 0 (Singleton {lo} {rel} {a} {h=notTheOccurrent}) {lo} {rel} {a}
    ||| A proof that the occurrent is not in the singleton heap
    YSingleton: OccursH occurrent 1 (Singleton {lo} {rel} {a} {h=occurrent}) {lo} {rel} {a}
    ||| Occurrences in Prick
    NPrick : Not (occurrent=h) -> Not (occurrent=s) -> OccursH occurrent 0 (Prick h s _ {lo} {rel} {a}) {lo} {rel} {a}
    HPrick : Not (occurrent=s) -> OccursH occurrent 1 (Prick occurrent s _ {lo} {rel} {a}) {lo} {rel} {a}
    SPrick : Not (occurrent=h) -> OccursH occurrent 1 (Prick h occurrent _ {lo} {rel} {a}) {lo} {rel} {a}
    YPrick : OccursH occurrent 2 (Prick occurrent occurrent _ {lo} {rel} {a}) {lo} {rel} {a}
    ||| Occurrences in Balanced
    NBalanced : Not (occurs=h) -> (leftH: OccursH occurrent occl left {n=(1+m)} {lo} {rel} {a}) -> (rightH: OccursH occurrent occr right {n=1+m} {lo} {rel} {a}) -> OccursH occurrent (occl+occr) (Balanced {m} {lo} {rel} {a} h hl hr left right) {lo} {rel} {a}
    YBalanced : (leftH: OccursH occurrent occl left {n=(1+m)} {lo} {rel} {a}) -> (rightH: OccursH occurrent occr right {n=1+m} {lo} {rel} {a}) -> OccursH occurrent (1+occl+occr) (Balanced {m} {lo} {rel} {a} occurrent hl hr left right) {lo} {rel} {a}
    ||| Occurrences in Imbalanced
    NImbalanced : Not (occurs=h) -> (leftH: OccursH occurrent occl left {n=(2+m)} {lo} {rel} {a}) -> (rightH: OccursH occurrent occr right {n=1+m} {lo} {rel} {a}) -> OccursH occurrent (occl+occr) (Imbalanced {m} {lo} {rel} {a} h hl hr left right) {lo} {rel} {a}
    YImbalanced : (leftH: OccursH occurrent occl left {n=(2+m)} {lo} {rel} {a}) -> (rightH: OccursH occurrent occr right {n=1+m} {lo} {rel} {a}) -> OccursH occurrent (1+occl+occr) (Imbalanced {m} {lo} {rel} {a} occurrent hl hr left right) {lo} {rel} {a}

||| Count the number of times a value occurs in a heap.
export
0 countOccurrences: DecEq a => (x: a) -> (heap: Heap n lo h) -> DPair Nat (\occ => OccursH x occ heap)
countOccurrences x [] = (0 ** Nowhere)
countOccurrences {h} x Singleton with (decEq x h)
  countOccurrences h Singleton | (Yes Refl) = (1 ** YSingleton)
  countOccurrences x Singleton | (No xNEqH) = (0 ** NSingleton xNEqH)
countOccurrences x (Prick h s hs) with (decEq x h, decEq x s)
  countOccurrences h (Prick h h hs) | (Yes Refl, Yes Refl) = (2 ** YPrick)
  countOccurrences h (Prick h s hs) | (Yes Refl, No xNEqS) = (1 ** HPrick xNEqS)
  countOccurrences s (Prick h s hs) | (No xNEqH, Yes Refl) = (1 ** SPrick xNEqH)
  countOccurrences x (Prick h s hs) | (No xNEqH, No xNEqS) = (0 ** NPrick xNEqH xNEqS)
countOccurrences x (Balanced h hl hr left right) with (decEq x h)
  countOccurrences h (Balanced h hl hr left right) | (Yes Refl) =
    let
        (occl ** hInLeft) = countOccurrences h left
        (occr ** hInRight) = countOccurrences h right
    in (1+occl+occr ** YBalanced hInLeft hInRight)
  countOccurrences x (Balanced h hl hr left right) | (No xNEqH) =
    let
        (occl ** hInLeft) = countOccurrences x left
        (occr ** hInRight) = countOccurrences x right
    in (occl+occr ** NBalanced xNEqH hInLeft hInRight)
countOccurrences x (Imbalanced h hl hr left right) with (decEq x h)
  countOccurrences h (Imbalanced h hl hr left right) | (Yes Refl) =
    let
        (occl ** hInLeft) = countOccurrences h left
        (occr ** hInRight) = countOccurrences h right
    in (1+occl+occr ** YImbalanced hInLeft hInRight)
  countOccurrences x (Imbalanced h hl hr left right) | (No xNEqH) =
    let
        (occl ** hInLeft) = countOccurrences x left
        (occr ** hInRight) = countOccurrences x right
    in (occl+occr ** NImbalanced xNEqH hInLeft hInRight)

-- covering
-- export
-- toList : Heap n lo top {rel} {a} -> DecEq a => List a # Sorted lo
-- toList [] = [] # []
-- toList Singleton = ?toList_rhs_1
-- toList (Prick top s hs) = ?toList_rhs_2
-- toList (Balanced top hl hr left right) = ?toList_rhs_3
-- toList (Imbalanced top hl hr left right) = ?toList_rhs_4

-- export
-- fromList : (0 lo: LinearOrder a rel) -> (xs: List a) -> Heap lo top {rel} {a}

-- 0 correct : (0 lo: LinearOrder a rel) -> DecEq a => (xs: List a) -> IsSortingOf lo xs (toList $ fromJust lo xs)
-- correct lo xs = (?correct_IsSorted, ?correct_IsPermutationOf)

-- covering
-- export
-- toList : {0 rel: Rel a} -> {lo: LinearOrder a rel} -> Heap {rel=rel} lo n -> DecEq a => List a
-- toList [] = []
-- toList (Singleton x) = [x]
-- toList (Balanced x leftH rightH relXLeft relXRight) = ?toList_rhs_2
-- toList (Imbalanced x leftH rightH relXLeft relXRight) = ?toList_rhs_3


-- toList ([] # prf) = [] # ([], snd prf)
-- toList {rel} {lo} ((x :: xs) # prf) =
--     let
--         (xs' # soxs') = toList $ tail xs (fst prf)
--     in x::xs' #
--         let
--             (sxs', pxs') = soxs'
--             (h, pxxs) = prf
--             pxxs' = x :: pxs'
--             sortedXXs' = case h of
--                 Singleton => rewrite PermutationOfNilIsNil pxs' in Singleton
--                 (Balanced x leftH rightH balanced relXLeft relXRight) =>
--                     ((((relXLeft ++ relXRight) {rel=rel} {e=x}) -@-> pxs') {rel=rel} :: sxs') {rel=rel}
--                 (Imbalanced x leftH rightH imbalanced relXLeft relXRight) =>
--                     ((((relXLeft ++ relXRight) {rel=rel} {e=x}) -@-> pxs') {rel=rel} :: sxs') {rel=rel}
--         in (sortedXXs', (pxxs \=> pxxs') @{transitiveIsPermutationOf})

-- export
-- HeapOf : (0 lo: LinearOrder a rel) -> List a -> Heap lo n -> Type
-- HeapOf lo perm heap = perm ~@~ toList heap

-- export
-- (::) : (x: a) -> List a # HeapOf lo xs -> List a # HeapOf lo (x::xs)
-- (::) {xs} x ([] # prf) = [x] # (Singleton, x :: snd prf)
-- (::) {xs} x ((y :: ys) # prf) = ?op_rhs_2

-- tail : (xs : List a) -> (lo: LinearOrder a rel) => (0 hxs: Heap lo (x::xs)) -> DecEq a => List a # HeapOf lo xs
-- tail [] hxs = [] # ([], reflexive @{reflexiveIsPermutationOf})
-- tail {rel} (y :: xs) hxs with (split xs)
--   tail ([y]) hxs | SplitNil = [y] # (Singleton, Ipo id)
--   tail ([y, z]) hxs | (SplitOne z) with (decEq y z)
--     tail ([y, y]) hxs | (SplitOne y) | (Yes Refl) = [y, y] # (Imbalanced y Singleton [] Refl ((reflexive {rel} :: [] {rel}) {rel}) ([] {rel}), reflexive @{reflexiveIsPermutationOf})
--     tail ([y, z]) hxs | (SplitOne z) | (No yNEqZ) with (connex {rel} yNEqZ)
--       tail ([y, z]) hxs | (SplitOne z) | (No yNEqZ) | (Left relYZ) = [y, z] # (
--         (Imbalanced y Singleton [] Refl ((relYZ :: ([] {rel})) {rel}) ([] {rel})),
--         reflexive @{reflexiveIsPermutationOf})
--       tail ([y, z]) hxs | (SplitOne z) | (No yNEqZ) | Right relZY = [z, y] # (
--         (Imbalanced z Singleton [] Refl ((relZY :: ([] {rel})) {rel}) ([] {rel})),
--         AdditionOfPermutationsCommutes {xs=[y]} {ys=[z]} $ reflexive {x=[y] ++ [z]} @{reflexiveIsPermutationOf})
--   tail (y :: (z :: (ys ++ (w :: zs)))) hxs | (SplitPair z ys w zs) = ?tail_rhs_1_rhs1_2

-- export
-- fromList : (xs: List a) -> List a # HeapOf lo xs
-- fromList [] = [] # ([], reflexive @{reflexiveIsPermutationOf})
-- fromList (x :: xs) = x :: fromList xs


-- covering
-- export
-- heapSort : (as: List a) ->  DecEq a => (lo: LinearOrder a rel) => (List a) # (IsSortingOf lo as)
-- heapSort x = toList $ fromList x
