module Sorted.Container.Vect

import Control.Function
import Control.WellFounded
import Data.Nat
import Data.Vect
import Decidable.Equality

import public Sorted.Container

%default total


data VectFamily : Type -> Type where
  MkVectFamily : Vect n a -> VectFamily a

Sized (VectFamily a) where
    size (MkVectFamily xs) = length xs

cnt : DecEq a => (x: a) -> (xs: Vect n a) -> Nat
cnt x [] = 0
cnt x (x' :: xs) with (decEq x x')
  cnt x (x :: xs) | (Yes Refl) = 1 + cnt x xs
  cnt x (x' :: xs) | (No _) = cnt x xs

export
DecEq a => Container a (VectFamily a) where
    x .#. (MkVectFamily xs) = cnt x xs
    
    Nil = MkVectFamily []
    NilIsEmpty = Refl
    NilIsUnique {xs = (MkVectFamily [])} uniq = Refl
    NilIsUnique {xs = (MkVectFamily (x :: xs))} uniq =
        void $ SIsNotZ $ ((rewrite yes x in cong S $ plusZeroLeftNeutral $ (x .#. (MkVectFamily xs))) \=> (uniq {x}))

    x :: (MkVectFamily xs) = MkVectFamily (x::xs)

    ConsAddsOne {x} {xs=MkVectFamily xs} = rewrite yes x in Refl
    ConsKeepsRest {xs=MkVectFamily xs} x'≠x = let _ # p = no x'≠x in rewrite p in Refl
    ConsBiinjective = MkBiinjective impl where
        impl : {x: a} -> {xs, ys: VectFamily a} -> Container.(::) x xs = Container.(::) y ys -> (x = y, xs = ys)
        impl {x=x} {xs=(MkVectFamily ys)} {ys=(MkVectFamily ys)} Refl = (Refl, Refl)

    (MkVectFamily xs) ++ (MkVectFamily ys) = MkVectFamily (xs++ys)
    ConcNilLeftNeutral {xs=MkVectFamily xs} = Refl
    ConcReduces {xs=MkVectFamily xs} {ys=MkVectFamily ys} = Refl

    ContainerSized = MkSized (\(MkVectFamily xs) => length xs)
    SizedNil = Refl
    SizedCons {xs=MkVectFamily xs} = Refl

    Match (MkVectFamily []) = Left Refl
    Match (MkVectFamily (x :: xs)) = Right ((x, MkVectFamily xs) # Refl)
