module Sorted.Container.List

import Control.Function
import Control.WellFounded
import Data.Void
import Data.List
import Data.Nat
import Decidable.Equality

import Sorted.Sequence

import public Sorted.Container

%default total

public export
DecEq a =>  Container a (List a) where

    x .#. [] = 0
    x .#. (x' :: xs) with (decEq x x')
        x .#. (x :: xs) | (Yes Refl) = 1 + x .#. xs
        x .#. (x' :: xs) | (No _) = x .#. xs

    Nil = []

    IsNil [] = Yes Refl
    IsNil (x :: xs) = No (\x∷xs≐【】 => absurd x∷xs≐【】)

    ∀x‥x⋕【】≐0 = Refl

    x :: y = x :: y

    Cons with (decEq x' x)
      Cons | (Yes Refl) = Left (Refl, rewrite yes x' in  Refl)
      Cons | (No x'≠x) = Right (x'≠x, Refl)

    Match [] = void $ x∷xs≠【】 Refl
    Match (x :: xs) = Bievidence x xs Refl

    xs ++ ys = xs ++ ys

    ConcAddsCounts {xs = []} {ys = []} = Refl
    ConcAddsCounts {xs = []} {ys = (y :: xs)} = Refl
    ConcAddsCounts {xs = (y :: xs)} {ys = []} = rewrite appendNilRightNeutral xs in (Refl \=> sym (plusZeroRightNeutral _))
    ConcAddsCounts {xs = (x' :: xs)}  with (decEq x x')
      ConcAddsCounts {xs = (_ :: xs)} | (Yes Refl) = cong S (ConcAddsCounts {c=List a})
      ConcAddsCounts {xs = (x' :: xs)} | (No x≠x') = (ConcAddsCounts {c=List a})

    ContainerSized = MkSized length

    ⋕⎨【】⎬≐0 = Refl

    ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ = Refl

    ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】{xs = []} _ = Refl
    ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】{xs = (x :: xs)} the⋕⎨x∷xs⎬≐0 = absurdity the⋕⎨x∷xs⎬≐0


DecEq a => OutputSequence a (List a) where
    OutSequenceHead {x∷xs = []} x∷xs≠【】 x∷xs≠【】' = void $ x∷xs≠【】 $ NilIsUnique (\x => Refl)
    OutSequenceHead {x∷xs = (x :: xs)} x∷xs≠【】 x∷xs≠【】' = Refl
    OutSequenceTail {x∷xs = []} x∷xs≠【】 x∷xs≠【】' = void $ x∷xs≠【】 $ NilIsUnique (\x => Refl)
    OutSequenceTail {x∷xs = (x :: xs)} x∷xs≠【】 x∷xs≠【】' = Refl

DecEq a => Sequence a (List a) where
    InSequenceHead = Refl
    InSequenceTail = Refl
