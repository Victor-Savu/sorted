module Sorted.Container

import public Control.Relation
import Data.Void
import Data.Nat
import Decidable.Equality

import public Sorted.Prop

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
interface Container a (0 c: Type -> Type) | c where
    constructor MkContainer

    (.#.) : a -> c a -> Nat

    Nil : c a
    0 NilIsEmpty : (x: a) -> x .#. [] = 0
    0 NilIsUnique : (xs: c a) -> ({m: Nat} -> (x': a) -> x' .#. xs = m -> m = 0) -> xs = []

    (::) : a -> c a -> c a
    0 ConsAddsOne : (x: a) -> (xs : c a) -> (1 + x .#. xs) = x .#. (x :: xs)
    0 ConsKeepsRest : (x: a) -> (xs : c a) -> (x': a) -> (ne: Not (x'=x)) -> x' .#. xs =  x' .#. (x::xs)
    0 ConsBiinjective : (x: a) -> Biinjective (::)

    (++) : (xs: c a) -> (ys: c a) -> c a
    0 ConcMerges : (xs: c a) -> (ys: c a) -> (x: a) -> x .#. (xs ++ ys) = x .#. xs + x .#. ys
    0 ConcNilRightNeutral : (xs: c a) -> xs ++ [] = xs

export
[uninhabitedConsIsNil] {0 x: a} -> {0 xs: c a} -> Container a c => Uninhabited (x::xs = []) where
   uninhabited xXsIsNil = absurdity $ transitive (ConsAddsOne x xs) $ transitive (cong (x .#.) xXsIsNil) (NilIsEmpty x)

headIsSame : {x, y: a} -> {xs, ys: c a} -> DecEq a => Container a c => x::xs = y::ys -> x = y
headIsSame prf with (decEq x y)
  headIsSame prf | (Yes Refl) = Refl
  headIsSame prf | (No xNEqY) = ?headIsSame_rhs_rhss_1

-- Implementation for List

public export
yes : DecEq a => (x: a) -> decEq x x = Yes Refl
yes x with (decEq x x)
  yes x | (Yes Refl) = Refl
  yes x | (No xNEqX) = void $ xNEqX Refl

public export
no : DecEq a => {x, x': a} -> (xNEqX': Not (x=x')) -> Not (x=x') # (\ctra => decEq x x' = No {prop=(x=x')} ctra)
no xNEqX' with (decEq x x')
  no x'NEqX' | (Yes Refl) = void $ x'NEqX' Refl
  no _ | (No xNEqX') = xNEqX' # Refl


0 Next : {x: a} -> {xs: c a} -> Container a c => {n: Nat} -> x .#. xs = n -> x .#. (Container.(::) x xs) = 1+n
Next prf = (sym $ ConsAddsOne x xs) `transitive` (cong S prf)

public export
ford : (0 _: a = b) -> a -> b
ford Refl = id

predec : {x: Nat} -> Not (x = 0) -> Nat # (\pred => x = S pred)
predec {x = 0} f = void $ f Refl
predec {x = (S k)} f = k # Refl

public export
DecEq a =>  Container a List where
    x .#. [] = 0
    x .#. (x' :: xs) with (decEq x x')
        x .#. (x :: xs) | (Yes Refl) = 1 + x .#. xs
        x .#. (x' :: xs) | (No _) = x .#. xs

    [] = []
    NilIsEmpty x = Refl
    NilIsUnique [] uniq = Refl
    NilIsUnique (x :: xs) uniq  with (decEq (x .#. xs) 0)
      NilIsUnique (x :: xs) uniq | Yes yes0 = void $ SIsNotZ $ (uniq {m=1} x) (rewrite yes x in rewrite yes0 in rewrite sym (Next {c=List} {a} yes0) in Refl)
      NilIsUnique (x :: xs) uniq | No not0 =
        let
          n # pdk = predec not0
        in void $ SIsNotZ $ uniq {m=S (x .#. xs)} x $ rewrite ConsAddsOne x xs in rewrite yes x in rewrite cong S $ (plusZeroLeftNeutral $ x .#. xs) in rewrite cong S pdk in rewrite sym (Next {c=List} {a} pdk) in Refl 

    x :: xs = x::xs
    ConsAddsOne x xs = rewrite yes x in Refl
    ConsKeepsRest x xs x' x'NEqX = let _ # p = no x'NEqX in rewrite p in Refl
    ConsBiinjective x = MkBiinjective ?impls where
        impl : {xs, ys: List a} -> Container.(::) x xs = Container.(::) y ys -> (x = y, xs = ys)
        impl Refl = (Refl, Refl)

    xs ++ ys = xs ++ ys
    ConcMerges [] ys x = Refl
    ConcMerges (y :: xs) ys x with (decEq x y)
      ConcMerges (x :: xs) ys x | (Yes Refl) = cong S $ ConcMerges xs ys x
      ConcMerges (y :: xs) ys x | (No contra) = ConcMerges xs ys x
    
    ConcNilRightNeutral [] = Refl
    ConcNilRightNeutral (x :: xs) = cong (x ::) (ConcNilRightNeutral xs)
