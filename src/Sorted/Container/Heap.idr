module Sorted.Container.Heap

import Data.Heap
import Data.Nat
import Decidable.Equality
import Control.Order
import Control.Relation

import Sorted.Container

-- %default total

export
data HeapFamily : LinearOrder a rel => Type -> Type where
  MkHeapFamily : Heap @{lo} {a} {rel} n h -> HeapFamily @{lo} {rel} a

LinearOrder a rel => Sized (HeapFamily {rel} a) where
  size (MkHeapFamily x) = length x

export
DecEq a => LinearOrder a rel => Container a (HeapFamily {rel} a) where

    x .#. (MkHeapFamily h) = cnt x h

    [] = MkHeapFamily []

    IsNil (MkHeapFamily []) = Yes Refl
    IsNil (MkHeapFamily (Singleton h)) = No (\x∷xs≐【】 => case x∷xs≐【】 of Refl impossible)
    IsNil (MkHeapFamily (Prick h s h≤s)) = No (\x∷xs≐【】 => case x∷xs≐【】 of Refl impossible)
    IsNil (MkHeapFamily (Balanced h h≤l h≤r left right)) = No (\x∷xs≐【】 => case x∷xs≐【】 of Refl impossible)
    IsNil (MkHeapFamily (Imbalanced h h≤l h≤r left right)) = No (\x∷xs≐【】 => case x∷xs≐【】 of Refl impossible)

    ∀x‥x⋕【】≐0 = Refl

    x :: (MkHeapFamily h) = MkHeapFamily (x :: h)

    ConsAddsOne =
      let
        0 l0: (S (x .#. xs) = x .#. (x :: xs)) =
          let
            MkHeapFamily xs = xs
          in
            ConsAddsOne x xs
      in rewrite l0 in Refl

    ConsKeepsRest {xs} x'≠x =
      let
        0 l0 : (x' .#. xs =  x' .#. (x::xs)) =
          let
            MkHeapFamily xs = xs
          in
            ConsKeepsRest {x} {x'} {xs} x'≠x
      in rewrite l0 in Refl

    Head (MkHeapFamily {n} x∷xs)  x∷xs≠【】 =
      let 
        0 prff : (m: Nat ** S m = n) = case n of
          0 => void $ x∷xs≠【】$ case x∷xs of
            [] => Refl
          (S m) => (m ** Refl)
        x∷xs: Heap (S prff.fst) _ = rewrite prff.snd in x∷xs
        Element x _ = Data.Heap.Head x∷xs 
      in x

    Tail (MkHeapFamily [])  x∷xs≠【】 = void $ x∷xs≠【】 Refl
    Tail (MkHeapFamily (Singleton h))  x∷xs≠【】 = []
    Tail (MkHeapFamily (Prick h s h≤s))  x∷xs≠【】 = MkHeapFamily (Singleton s)
    Tail (MkHeapFamily hp@(Balanced h h≤l h≤r left right))  x∷xs≠【】 = case Data.Heap.Tail hp of
      ((_ ** (Element xs _))) => MkHeapFamily xs
    Tail (MkHeapFamily hp@(Imbalanced h h≤l h≤r left right))  x∷xs≠【】 = case Data.Heap.Tail hp of
      ((_ ** (Element xs _))) => MkHeapFamily xs

    HeadTail (MkHeapFamily {n = 0} [])  x∷xs≠【】 = void $ x∷xs≠【】 Refl
    HeadTail (MkHeapFamily {n = 1} (Singleton h))  x∷xs≠【】 = Refl
    HeadTail (MkHeapFamily {n = 2} (Prick h s h≤s))  x∷xs≠【】 with (decEq h s)
      -- h≤h is not necessarily the result of reflexive
      HeadTail (MkHeapFamily {n = 2} (Prick h h h≤h))  x∷xs≠【】 | (Yes Refl) = ?hjkgahj_2_rhs2_0
      HeadTail (MkHeapFamily {n = 2} (Prick h s h≤s))  x∷xs≠【】 | (No contra) = ?hjkgahj_2_rhs2_1
    HeadTail (MkHeapFamily {n = (1 + ((1 + m) + (1 + m)))} (Balanced h h≤l h≤r left right))  x∷xs≠【】 = ?hjkgahj_3
    HeadTail (MkHeapFamily {n = (1 + ((2 + m) + (1 + m)))} (Imbalanced h h≤l h≤r left right))  x∷xs≠【】 = ?hjkgahj_4

    -- HeadTail x∷xs@(MkHeapFamily {n} x∷xs')  x∷xs≠【】 =
      -- let
      --   0 prff : (m: Nat ** S m = n) = case n of
      --     0 => void $ x∷xs≠【】$ case x∷xs' of
      --       [] => Refl
      --     (S m) => (m ** Refl)
      --   x∷xs'': Heap (S prff.fst) _ = rewrite prff.snd in x∷xs'
      --   0 x∷xs≠【】': (Not (MkHeapFamily x∷xs' = Nil)) = \arg => x∷xs≠【】 ?sads
      --   0 l0: ((let Element x _ = Head x∷xs' in x) :: Tail (MkHeapFamily x∷xs') x∷xs≠【】 = MkHeapFamily x∷xs') = ?sda
      -- in
      --   rewrite l0 in Refl

    (MkHeapFamily xs) ++ (MkHeapFamily ys) = MkHeapFamily (xs ++ ys)

    ConcAddsCounts {xs = (MkHeapFamily xs)} {ys = (MkHeapFamily ys)} =
      let
        0 l0 : (cnt x (xs ++ ys) = plus (cnt x xs) (cnt x ys)) = case xs of
          [] => Refl
          (Singleton h) => case ys of
            [] => sym $ plusZeroRightNeutral _
            (Singleton h') =>  ?help7_9
            (Prick h' s h'≤s) => ?help7_10
            (Balanced h' h'≤l h'≤r left right) => ?help7_11
            (Imbalanced h' h'≤l h'≤r left right) => ?help7_12
          (Prick h s h≤s) => ?help7_5
          (Balanced h h≤l h≤r left right) => ?help7_6
          (Imbalanced h h≤l h≤r left right) => ?help7_7
      in rewrite l0 in Refl

    ⋕⎨【】⎬≐0 = Refl

    ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ {xs = (MkHeapFamily xs)} =
      let
        0 l0 : (length (x :: xs) = S (length xs)) = case xs of
          [] => Refl
          (Singleton h) => Refl
          (Prick h s h≤s) => Refl
          (Balanced h h≤l h≤r left right) => Refl
          (Imbalanced h h≤l h≤r left right) => cong S ?ads_4
      in rewrite l0 in Refl

    ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】 {xs = (MkHeapFamily xs)} the⋕⎨x∷xs⎬≐0 = 
      let
        0 l0 : (MkHeapFamily xs = MkHeapFamily []) = case xs of
          [] => Refl
          (Singleton h) => void $ SIsNotZ the⋕⎨x∷xs⎬≐0
          (Prick h s h≤s) => void $ SIsNotZ the⋕⎨x∷xs⎬≐0
          (Balanced h h≤l h≤r left right) => void $ SIsNotZ the⋕⎨x∷xs⎬≐0
          (Imbalanced h h≤l h≤r left right) => void $ SIsNotZ the⋕⎨x∷xs⎬≐0
      in rewrite l0 in Refl
    

--     x .#. (MkHeapFamily xs) = cnt x xs
    
--     Nil = MkHeapFamily []
--     NilIsEmpty = Refl

--     NilIsUnique {xs = (MkHeapFamily {n=0} {h=()} [])} uniq = Refl
--     NilIsUnique {xs = (MkHeapFamily {n=S m} {h} xs)} uniq = absurdity @{ui {xs=xs} {n=m} {h}} uniq

--     x :: (MkHeapFamily xs) = MkHeapFamily ((x::xs) {rel})

--     ConsAddsOne {xs = (MkHeapFamily xs)} = ConsAddsOne xs

--     ConsKeepsRest {xs=MkHeapFamily []} x'≠x = rewrite decEqContraIsNo x'≠x in Refl
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
