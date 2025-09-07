module Sorted.Container.Vect

import Control.Function
import Control.WellFounded
import Data.Nat
import Data.Vect
import Data.Void
import Decidable.Equality

import public Sorted.Container

%default total

export
data VectFamily : Type -> Type where
  MkVectFamily : Vect n a -> VectFamily a

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

export
DecEq a => Container a (VectFamily a) where
    x .#. (MkVectFamily xs) = cnt x xs
    
    [] = MkVectFamily []

    IsNil (MkVectFamily []) = Yes Refl
    IsNil (MkVectFamily (x :: xs)) = No (\x∷xs≐【】 => case x∷xs≐【】 of Refl impossible)

    ∀x‥x⋕【】≐0 = Refl

    x :: MkVectFamily ys = MkVectFamily (x :: ys)

    Cons with (decEq x' x)
      Cons {xs = MkVectFamily xslist} | (Yes Refl) = Left (Refl, rewrite yes x' in Refl)
      Cons {xs = MkVectFamily xslist} | (No x'≠x) = Right (x'≠x, let Element _ p = no x'≠x in rewrite p in Refl)

    ConsBisurjective {x∷xs = (MkVectFamily [])} x∷xs≠【】 = void $ x∷xs≠【】 Refl
    ConsBisurjective {x∷xs = (MkVectFamily (x :: xs))} x∷xs≠【】 = Bievidence x (MkVectFamily xs) Refl

    MkVectFamily xs ++ MkVectFamily ys = MkVectFamily (xs ++ ys)

    ConcAddsCounts {xs = MkVectFamily xs} {ys = MkVectFamily ys} = concAddsCnt x xs ys

    ContainerSized = MkSized (\(MkVectFamily xs) => length xs)

    ⋕⎨【】⎬≐0 = Refl

    ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ {xs = MkVectFamily xs} = Refl

    ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】 the⋕⎨x∷xs⎬≐0 {xs = MkVectFamily []} = Refl
    ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】 the⋕⎨x∷xs⎬≐0 {xs = MkVectFamily (x::xs)} = absurdity the⋕⎨x∷xs⎬≐0
