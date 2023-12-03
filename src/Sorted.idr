module Sorted

import Control.Order
import Control.WellFounded
import Data.Linear.LMaybe
import Data.Linear.LNat
import Data.Linear.Notation
import Data.Nat
import Data.Nat.Views
import Data.Vect
import Decidable.Equality

%default total

smallHalf : Nat -> Nat
smallHalf n with (half n)
    smallHalf (j + j) | HalfEven j = j
    smallHalf (1 + (j + j)) | HalfOdd j = j

largeHalf : Nat -> Nat
largeHalf n with (half n)
    largeHalf (j + j) | HalfEven j = j
    largeHalf (1 + (j + j)) | HalfOdd j = S j

smallAndLargeHalfMakeWhole : (n: Nat) -> (smallHalf n + largeHalf n = n)
smallAndLargeHalfMakeWhole n with (half n)
    smallAndLargeHalfMakeWhole (j + j) | HalfEven j = Refl
    smallAndLargeHalfMakeWhole (1 + (j + j)) | HalfOdd j = sym (plusSuccRightSucc j j)

smallHalfGrowsEvery2 : (n: Nat) -> (smallHalf (S (S n)) = S (smallHalf n))
smallHalfGrowsEvery2 n with (half n)
    smallHalfGrowsEvery2 _ | HalfOdd j = Refl
    smallHalfGrowsEvery2 _ | HalfEven (S j) = Refl
    smallHalfGrowsEvery2 _ | HalfEven 0 = Refl

largeHalfGrowsEvery2 : (n: Nat) -> (largeHalf (S (S n)) = S (largeHalf n))
largeHalfGrowsEvery2 n with (half n)
    largeHalfGrowsEvery2 _ | HalfOdd j = Refl
    largeHalfGrowsEvery2 _ | HalfEven (S j) = Refl
    largeHalfGrowsEvery2 _ | HalfEven 0 = Refl

namespace Prop
    public export
    data Prop: (a: Type) -> (a -> Type) -> Type where
        (#): (f: a) -> (0 prf: p f) -> Prop a p

public export
(#) : (a: Type) -> (a-> Type) -> Type
(#) a f = Prop a f

public export
subject : a # p -> a
subject (f # prf) = f

public export
data Sorted: (0 lo: LinearOrder a rel) => (Vect n a) -> Type where
    NilIsSorted: Sorted @{lo} Nil
    SingletonIsSorted : Sorted @{lo} [x]
    SeveralAreSorted: (LinearOrder a rel) => (0 _: rel x y) -> (0 _: Sorted @{lo} (y::ys)) -> Sorted @{lo} (x::y::ys)

public export
0 sortedTail : (0 lo: LinearOrder a rel) => Sorted @{lo} (x::xs) -> Sorted @{lo} xs
sortedTail SingletonIsSorted = NilIsSorted
sortedTail (SeveralAreSorted z w) = w

public export
split : Vect n a -@ LPair (Vect (smallHalf n) a) (Vect (largeHalf n) a)
split [] = ([] # [])
split [x] = ([] # [x])
split {n=1 + (1 + m)} (x::y::tail) =
    let (xs # ys) = Sorted.split tail in
        ( rewrite (smallHalfGrowsEvery2 m) in (x::xs)
        # rewrite (largeHalfGrowsEvery2 m) in (y::ys))

public export
merge: (DecEq a) => (lo: LinearOrder a rel) => (xs: (Vect m a) # (Sorted @{lo})) -> (ys: (Vect n a) # (Sorted @{lo}))
    -> ((Vect (m+n) a) # (Sorted @{lo})) # \merged => (forall j . (Sorted @{lo} (j::subject xs)) -> (Sorted @{lo} (j::subject ys)) -> Sorted @{lo} (j::(subject merged)))
merge ([] # _)  y =  y # (\_ => \a => a)
merge x ([] # _) = rewrite (plusZeroRightNeutral  m) in (x # (\w => \_ => w))
merge {m = S pm} {n = S pn} ((x::xs) # px) ((y::ys) # py) =
    let
        xrely: Either (rel x y) (rel y x) = case decEq x y of
            Yes xEqy => Left (rewrite xEqy in reflexive)
            No xNEqy => connex xNEqy
    in
        case xrely of
            Left vrel =>
                let
                    (xsz # pxz) # f = merge (xs # (sortedTail px)) (y::ys # py)
                in
                    ((x :: xsz) # (f px (SeveralAreSorted @{lo} vrel py))) # (
                        \(SeveralAreSorted xxa xxb) => \(SeveralAreSorted yya yyb) => (SeveralAreSorted xxa $ f xxb $ SeveralAreSorted vrel yyb))
            Right vrel =>
                let
                    ((ysz # pxz) # f) = merge (x::xs # px) (ys # (sortedTail py))
                in
                rewrite sym (eqSucc _ _ (plusSuccRightSucc pm pn)) in
                    (((y :: ysz) # (f (SeveralAreSorted vrel px) py)) # (
                        \(SeveralAreSorted xxa xxb) => \(SeveralAreSorted yya yyb) => (SeveralAreSorted yya $ f (SeveralAreSorted vrel xxb) yyb)))

public export
mergeSort : (DecEq a) => (lo: LinearOrder a rel) => Vect m a -> (Vect m a) # (Sorted @{lo})
mergeSort [] = [] # NilIsSorted
mergeSort [x] = [x] # SingletonIsSorted
mergeSort {m = S (S n)} (x::y::tail) =
    let
        (l # r) = Sorted.split tail
        l' = mergeSort (assert_smaller (x::y::tail) (x::l))
        r' = mergeSort (assert_smaller (x::y::tail) (y::r))
        (res # _) = merge  l' r'
    in
        rewrite sym $ smallAndLargeHalfMakeWhole n in rewrite plusSuccRightSucc (smallHalf n) (largeHalf n) in res
