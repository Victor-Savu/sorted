module Sorted.Container.Heap

import Data.Heap
import Control.Order
import Control.Relation

import Sorted.Container

-- %default total

export
data HeapFamily : LinearOrder a rel => Type -> Type where
    MkHeapFamily : Heap @{lo} {a} {rel} n h -> HeapFamily @{lo} {rel} a

export
DecEq a => LinearOrder a rel => Container a (HeapFamily {rel} a) where

    x .#. h = ?help

    [] = []

    IsNil h = ?helpIsNil

    ∀x‥x⋕【】≐0 = ?help1

    x :: y = ?help2

    Cons with (decEq x' x)
      Cons | (Yes Refl) = Left ?help3
      Cons | (No x'≠x) = Right ?help4

    ConsBisurjective {x∷xs} x∷xs≠【】 = ?help5

    xs ++ ys = ?help6

    ConcAddsCounts {xs} {ys} = ?help7

    ContainerSized = MkSized ?help8

    ⋕⎨【】⎬≐0 = ?help9

    ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ = ?help10

    ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】{xs} the⋕⎨x∷xs⎬≐0 = ?help11
    

--     x .#. (MkHeapFamily xs) = cnt x xs
    
--     Nil = MkHeapFamily []
--     NilIsEmpty = Refl

--     NilIsUnique {xs = (MkHeapFamily {n=0} {h=()} [])} uniq = Refl
--     NilIsUnique {xs = (MkHeapFamily {n=S m} {h} xs)} uniq = absurdity @{ui {xs=xs} {n=m} {h}} uniq

--     x :: (MkHeapFamily xs) = MkHeapFamily ((x::xs) {rel})

--     ConsAddsOne {xs = (MkHeapFamily xs)} = ConsAddsOne xs

--     ConsKeepsRest {xs=MkHeapFamily []} x'≠x = let Element _ p = no x'≠x in rewrite p in Refl
--     ConsKeepsRest {xs=MkHeapFamily (Singleton h)} x'≠x = ?ckr_1
--     ConsKeepsRest {xs=MkHeapFamily (Prick h s h≤s)} x'≠x = ?ckr_2
--     ConsKeepsRest {xs=MkHeapFamily (Balanced h h≤l h≤r left right)} x'≠x = ?ckr_3
--     ConsKeepsRest {xs=MkHeapFamily (Imbalanced h h≤l h≤r left right)} x'≠x = ?ckr_4

--     ConsBiinjective = MkBiinjective impl where
--         impl : {x: a} -> {xs, ys: HeapFamily {rel} a} -> Container.(::) x xs = Container.(::) y ys -> (x = y, xs = ys)

--     (MkHeapFamily xs) ++ (MkHeapFamily ys) = MkHeapFamily (xs++ys)
--     ConcNilLeftNeutral {xs=MkHeapFamily xs} = Refl
--     ConcReduces {xs=MkHeapFamily xs} {ys=MkHeapFamily ys} = ?cr

--     ContainerSized = MkSized (\(MkHeapFamily xs) => length xs)
--     SizedNil = Refl
--     SizedCons {xs=MkHeapFamily xs} = ?sc

--     Match (MkHeapFamily {rel} {n} xs) = ?match
--     Match xs = ?Match_rhs

-- export
-- fromList : (xs: List a) -> List a # HeapOf lo xs
-- fromList [] = [] # ([], reflexive @{reflexiveIsPermutationOf})
-- fromList (x :: xs) = x :: fromList xs


-- covering
-- export
-- heapSort : (as: List a) ->  DecEq a => (lo: LinearOrder a rel) => (List a) # (IsSortingOf lo as)
-- heapSort x = toList $ fromList x
