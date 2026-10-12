module Sorted.Container.Vect

import Control.Function
import Control.WellFounded
import Data.Nat
import Data.Vect
import Data.Void
import Decidable.Equality


import Sorted.Sequence

import public Sorted.Container

%default total

public export
data VectFamily : Type -> Type where
  MkVectFamily : Vect n a -> VectFamily a

export
Sized (VectFamily a) where
  size (MkVectFamily xs) = length xs

cnt : DecEq a => (x: a) -> (xs: Vect n a) -> Nat
cnt x [] = 0
cnt x (x' :: xs) with (decEq x x')
  cnt x (x :: xs) | (Yes Refl) = 1 + cnt x xs
  cnt x (x' :: xs) | (No _) = cnt x xs

concAddsCnt : DecEq a => (x: a) -> (xs: Vect m a) -> (ys: Vect n a) -> cnt x (xs ++ ys) = cnt x xs + cnt x ys
concAddsCnt x [] ys = Refl
concAddsCnt x (x' :: xs) ys with (decEq x x')
  concAddsCnt x (x :: xs) ys | (Yes Refl) = cong S $ concAddsCnt x xs ys
  concAddsCnt x (x' :: xs) ys | (No _) = concAddsCnt x xs ys

public export
DecEq a => Container a (VectFamily a) where
  x .#. (MkVectFamily xs) = cnt x xs
  
  [] = MkVectFamily []

  IsNil (MkVectFamily []) = Yes Refl
  IsNil (MkVectFamily (x :: xs)) = No (\x∷xs≐【】 => case x∷xs≐【】 of Refl impossible)

  ∀x‥x⋕【】≐0 = Refl

  x :: MkVectFamily ys = MkVectFamily (x :: ys)

  ConsAddsOne =
    let
      0 l0: ((1 + x .#. xs) = x .#. (x :: xs)) = case xs of
        (MkVectFamily []) => rewrite decEqSelfIsYes {x} in Refl
        (MkVectFamily (y :: ys)) =>  rewrite decEqSelfIsYes {x} in Refl
    in rewrite l0 in Refl

  ConsKeepsRest x'≠x =
    let
      0 l0: (x' .#. xs =  x' .#. (x::xs)) = case xs of
        (MkVectFamily []) => rewrite (decEqContraIsNo x'≠x).snd in Refl
        (MkVectFamily (y :: ys)) => rewrite (decEqContraIsNo x'≠x).snd in Refl
    in rewrite l0 in Refl

  -- Match (MkVectFamily []) = void $ x∷xs≠【】 Refl
  -- Match (MkVectFamily (x :: xs)) = Bievidence x (MkVectFamily xs) Refl

  Head (MkVectFamily []) x∷xs≠【】 = void $ x∷xs≠【】 Refl
  Head (MkVectFamily (x :: _)) _ = x

  Tail (MkVectFamily []) x∷xs≠【】 = void $ x∷xs≠【】 Refl
  Tail (MkVectFamily (_ :: xs)) _ = MkVectFamily xs

  HeadTail x∷xs x∷xs≠【】 =
    let
      0 l0: (Head x∷xs x∷xs≠【】 :: Tail x∷xs x∷xs≠【】 = x∷xs) =
        case x∷xs of
          (MkVectFamily []) => void $ x∷xs≠【】 Refl
          (MkVectFamily (x :: xs)) => Refl
    in rewrite l0 in Refl

  MkVectFamily xs ++ MkVectFamily ys = MkVectFamily (xs ++ ys)

  ConcAddsCounts {xs = MkVectFamily xs} {ys = MkVectFamily ys} = rewrite concAddsCnt x xs ys in Refl

  ⋕⎨【】⎬≐0 = Refl

  ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ {xs = MkVectFamily xs} = Refl

  ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】 the⋕⎨x∷xs⎬≐0 =
    let 
      0 prf: (xs = []) = case xs of
        MkVectFamily [] => Refl
        MkVectFamily (x::xs) => absurdity the⋕⎨x∷xs⎬≐0
    in rewrite prf in Refl


DecEq a => OutputSequence a (VectFamily a) where
  OutSequenceHead x∷xs x∷xs≠【】 x∷xs≠【】'=
    let
      0 l0: (Head x∷xs x∷xs≠【】 = Head x∷xs x∷xs≠【】') =
        case x∷xs of
          (MkVectFamily []) => void $ x∷xs≠【】 Refl
          (MkVectFamily (x :: xs)) => Refl
    in rewrite l0 in Refl
  OutSequenceTail x∷xs x∷xs≠【】 x∷xs≠【】' =
    let
      0 l0: (Tail x∷xs x∷xs≠【】 = Tail x∷xs x∷xs≠【】') =
        case x∷xs of
          (MkVectFamily []) => void $ x∷xs≠【】 Refl
          (MkVectFamily (x :: xs)) => Refl
    in rewrite l0 in Refl

DecEq a => Sequence a (VectFamily a) where
  InSequenceHead x xs =
    let
      0 l0: (Head (x::xs) (uninhabited @{UninhabitedConsIsNil {c=VectFamily a} {x} {xs}}) = x) =
        case xs of
          (MkVectFamily []) => Refl
          (MkVectFamily (x' :: xs')) => Refl
    in rewrite l0 in Refl

  InSequenceTail x xs =
    let
      0 l0: (Tail (x::xs) (uninhabited @{UninhabitedConsIsNil {c=VectFamily a} {x} {xs}}) = xs) =
        case xs of
          (MkVectFamily []) => Refl
          (MkVectFamily (x' :: xs')) => Refl
    in rewrite l0 in Refl

