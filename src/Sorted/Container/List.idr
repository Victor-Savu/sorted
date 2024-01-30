module Sorted.Container.List

import Control.Function
import Control.WellFounded
import Data.Nat
import Decidable.Equality

import public Sorted.Container

%default total


predec : {x: Nat} -> Not (x = 0) -> Nat # (\pred => x = S pred)
predec {x = 0} f = void $ f Refl
predec {x = (S k)} f = k # Refl

export
DecEq a =>  Container a (List a) where
    x .#. [] = 0
    x .#. (x' :: xs) with (decEq x x')
        x .#. (x :: xs) | (Yes Refl) = 1 + x .#. xs
        x .#. (x' :: xs) | (No _) = x .#. xs

    [] = []
    NilIsEmpty x = Refl
    NilIsUnique [] uniq = Refl
    NilIsUnique (x :: xs) uniq  with (decEq (x .#. xs) 0)
      NilIsUnique (x :: xs) uniq | Yes yes0 = void $ SIsNotZ $ (uniq {m=1} x) (rewrite yes x in rewrite yes0 in rewrite sym (Next {c=List a} yes0) in Refl)
      NilIsUnique (x :: xs) uniq | No not0 =
        let
          n # pdk = predec not0
        in void $ SIsNotZ $ uniq {m=S (x .#. xs)} x $ rewrite ConsAddsOne x xs in rewrite yes x in rewrite cong S $ (plusZeroLeftNeutral $ x .#. xs) in rewrite cong S pdk in rewrite sym (Next {c=List a} pdk) in Refl 

    x :: xs = x::xs
    ConsAddsOne x xs = rewrite yes x in Refl
    ConsKeepsRest x xs x' x'NEqX = let _ # p = no x'NEqX in rewrite p in Refl
    ConsBiinjective = MkBiinjective impl where
        impl : {x: a} -> {xs, ys: List a} -> Container.(::) x xs = Container.(::) y ys -> (x = y, xs = ys)
        impl Refl = (Refl, Refl)

    xs ++ ys = xs ++ ys
    ConcNilLeftNeutral xs = Refl
    ConcReduces x xs ys = Refl

    ContainerSized = MkSized length
    SizedNil = Refl
    SizedCons = Refl

    Match [] = Left Refl
    Match (x :: xs) = Right ((x, xs) # Refl)
