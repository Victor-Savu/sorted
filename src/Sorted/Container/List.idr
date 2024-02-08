module Sorted.Container.List

import Control.Function
import Control.WellFounded
import Data.Void
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
    NilIsEmpty = Refl
    NilIsUnique {xs = []} uniq = Refl 
    NilIsUnique {xs = (x :: xs)} uniq = void $ SIsNotZ $ (rewrite yes x in cong S $ plusZeroLeftNeutral $ x .#. xs) \=> (uniq {x=x})

    x :: xs = x::xs
    ConsAddsOne {x} {xs} = rewrite yes x in Refl
    ConsKeepsRest x'≠x = let _ # p = no x'≠x in rewrite p in Refl
    ConsBiinjective = MkBiinjective impl where
        impl : {x: a} -> {xs, ys: List a} -> Container.(::) x xs = Container.(::) y ys -> (x = y, xs = ys)
        impl Refl = (Refl, Refl)

    xs ++ ys = xs ++ ys
    ConcNilLeftNeutral = Refl
    ConcReduces = Refl

    ContainerSized = MkSized length
    SizedNil = Refl
    SizedCons = Refl

    Match [] = Left Refl
    Match (x :: xs) = Right ((x, xs) # Refl)
