module Sorted.Container

import Decidable.Equality

import Sorted.Prop

infixr 9 .#.

||| A container is a type that
||| a. has an element representing the empty container
||| b. has a way to add an element to an existing container such that the resulting container contains exactly one more instance of that new element
|||    and just as many instances of any other element of the original container
|||
||| The container interface is satisfied by:
||| - the type a representing the type of elements in the container
||| - the type construtor c: Type -> Type which constructs the type of the container: c a
||| if it can:
||| 1. provide a counting function (.#.): a -> c a -> Nat which counts the number of occurrences of a value of type a in the container of type c a
||| 1. produce an "empty" container from thin air (using Nil). The empty container is a specific instance of c a (call it xs) which must satisfy the
|||    property that any value of type a occurs 0 times in xs according to the counting function. Basically, a container is empty if nothing occurs in it.
||| 2. produce an "inhabited" container by applying (::) to an element of type a (call it x) and another container of type c a (call it xs). The
|||    "inhabited" container is a specific instance of c a (call it xxs) which must satisfy two properties:
|||    1. As counted by (.#.), x occurs in xxs one time more than it occurs in xs (showing that x was inserted exactly once by (::))
|||    2. Given any other element of a (call it x'), that element will occur the same number of times in xs as it does in xxs (showing that no other
|||       element of xs was duplicated or removed by (::))
public export
interface Container a c where
    (.#.) : a -> c a -> Nat
    Nil : c a # (\xs => (0 x: a) -> x .#. xs = 0)
    (::) : (x: a) -> (xs : c a) -> c a # (\xxs => ((1 + x .#. xs) = x .#. xxs, (0 x': a) -> (0_: Not (x'=x)) -> x' .#. xs =  x' .#. xxs))
    (++) : (xs: c a) -> (ys: c a) -> c a # (\xys => (x: a) -> x .#. xys = x .#. xs + x .#. ys)

-- Implementation for List

yes : DecEq a => (x: a) -> decEq x x = Yes Refl
yes x with (decEq x x)
  yes x | (Yes Refl) = Refl
  yes x | (No xNEqX) = void $ xNEqX Refl

no : DecEq a => {x, x': a} -> (xNEqX': Not (x=x')) -> Not (x=x') # (\ctra => decEq x x' = No {prop=(x=x')} ctra)
no xNEqX' with (decEq x x')
  no x'NEqX' | (Yes Refl) = void $ x'NEqX' Refl
  no _ | (No xNEqX') = xNEqX' # Refl

public export
DecEq a =>  Container a List where
    x .#. [] = 0
    x .#. (x' :: xs) with (decEq x x')
        x .#. (x :: xs) | (Yes Refl) = 1 + x .#. xs
        x .#. (x' :: xs) | (No _) = x .#. xs

    [] = [] # \_ => Refl
    x :: xs = x::xs # (rewrite yes x in Refl, \x' => \x'NEqX => let _ # p = no x'NEqX in rewrite p in Refl)
    xs ++ ys = xs ++ ys # \x => prf x xs ys where
        prf : (x:a) -> (xs: List a) -> (ys: List a) -> x .#. (xs ++ ys) = (x .#. xs) + (x .#. ys)
        prf x [] ys = Refl
        prf x (y :: xs) ys with (decEq x y)
          prf x (x :: xs) ys | (Yes Refl) = cong S $ prf x xs ys
          prf x (y :: xs) ys | (No contra) = prf x xs ys
