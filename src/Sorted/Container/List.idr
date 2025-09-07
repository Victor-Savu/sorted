module Sorted.Container.List

import Control.Function
import Control.WellFounded
import Data.Void
import Data.List
import Data.Nat
import Decidable.Equality

import public Sorted.Container

%default total

export
DecEq a =>  Container a (List a) where

    x .#. [] = 0
    x .#. (x' :: xs) with (decEq x x')
        x .#. (x :: xs) | (Yes Refl) = 1 + x .#. xs
        x .#. (x' :: xs) | (No _) = x .#. xs

    [] = []

    IsNil [] = Yes Refl
    IsNil (x :: xs) = No (\x∷xs≐【】 => absurd x∷xs≐【】)

    ∀x‥x⋕【】≐0 = Refl

    x :: y = x :: y

    Cons with (decEq x' x)
      Cons | (Yes Refl) = Left (Refl, rewrite yes x' in  Refl)
      Cons | (No x'≠x) = Right (x'≠x, Refl)

    ConsBisurjective {x∷xs = []} x∷xs≠【】= void $ x∷xs≠【】 Refl
    ConsBisurjective {x∷xs = (x :: xs)} x∷xs≠【】= Bievidence x xs Refl

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
    

DecEq a => Sequence a (List a) where
    Next {xss≠【】} [] = void $ xss≠【】 Refl
    Next (x :: xs)  = Element (x, xs) ((rewrite yes x in Refl), \x' => ConsKeepsRest {x} {xs} {x'})

    NextIndifferent [] p0 p1 = void $ p0 Refl
    NextIndifferent (x :: xs) p0 p1 = Refl

