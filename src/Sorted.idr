module Sorted

import Data.Vect
import Data.Nat
import Data.Linear.Notation
import Data.Linear.LMaybe
import Data.Linear.LNat
import Control.Order
import Decidable.Equality

%default total

namespace Prop
    public export
    data Prop: (a: Type) -> (a -> Type) -> Type where
        (#): (f: a) -> (0 prf: p f) -> Prop a p

(#) : (a: Type) -> (a-> Type) -> Type
(#) a f = Prop a f

data Sorted: (0 lo: LinearOrder a rel) => (Vect n a) -> Type where
    NilIsSorted: Sorted @{lo} Nil
    SingletonIsSorted : Sorted @{lo} [x]
    SeveralAreSorted: (LinearOrder a rel) => (0 _: rel x y) -> (0 _: Sorted @{lo} (y::ys)) -> Sorted @{lo} (x::y::ys)

subject : a # p -> a
subject (f # prf) = f

0 sortedTail : (0 lo: LinearOrder a rel) => Sorted @{lo} (x::xs) -> Sorted @{lo} xs
sortedTail SingletonIsSorted = NilIsSorted
sortedTail (SeveralAreSorted z w) = w

data Parity : Nat -> Type where
   Even : {n : _} -> Parity (n + n)
   Odd  : {n : _} -> Parity (S (n + n))

parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j))) | Even
      = rewrite plusSuccRightSucc j j in Even {n = S j}
  parity (S (S (S (j + j)))) | Odd
      = rewrite plusSuccRightSucc j j in Odd {n = S j}

smallHalf : Nat -> Nat
smallHalf n with (parity n)
    smallHalf (j + j) | Even = j
    smallHalf (S (j + j)) | Odd = j

largeHalf : Nat -> Nat
largeHalf n with (parity n)
    largeHalf (j + j) | Even = j
    largeHalf (S (j + j)) | Odd = S j

smallAndLargeHalfMakeWhole : (n: Nat) -> (smallHalf n + largeHalf n = n)
smallAndLargeHalfMakeWhole n with (parity n)
    smallAndLargeHalfMakeWhole (j + j) | Even = Refl
    smallAndLargeHalfMakeWhole (S (j + j)) | Odd = sym (plusSuccRightSucc j j)

smallHalfGrowsEvery2 : (n: Nat) -> (smallHalf (S (S n)) = S (smallHalf n))
smallHalfGrowsEvery2 n with (parity n)
  smallHalfGrowsEvery2 (j+j) | Even = Refl
  smallHalfGrowsEvery2 (S (j+j)) | Odd = Refl

largeHalfGrowsEvery2 : (n: Nat) -> (largeHalf (S (S n)) = S (largeHalf n))
largeHalfGrowsEvery2 n with (parity n)
  largeHalfGrowsEvery2 (j+j) | Even = Refl
  largeHalfGrowsEvery2 (S (j+j)) | Odd = Refl

0 veclen : (_: Vect n a) -> Nat
veclen _ = n

split : Vect n a -@ LPair (Vect (smallHalf n) a) (Vect (largeHalf n) a)
split [] = ([] # [])
split [x] = ([] # [x])
split (x::y::tail) =
    let (xs # ys) = Sorted.split tail in
        ( rewrite (smallHalfGrowsEvery2 (veclen tail)) in (x::xs)
        # rewrite (largeHalfGrowsEvery2 (veclen tail)) in (y::ys))

sucIsEqual' : {m, n: Nat} -> n=m -> S n = S m
sucIsEqual' Refl = Refl

plusZeroIsSame: (m: Nat) -> (m+0 = m)
plusZeroIsSame 0 = Refl
plusZeroIsSame (S k) = rewrite plusZeroIsSame k in (sucIsEqual' Refl)

equalityExtendsReflexion : (Reflexive a rel) => {x, y: a} -> (x = y) -> rel x y
equalityExtendsReflexion Refl = reflexive

merge: {a: Type} -> (DecEq a) => {rel: a->a-> Type} -> (lo: LinearOrder a rel) => {m: Nat} -> (xs: (Vect m a) # (Sorted @{lo})) -> {n: Nat} -> (ys: (Vect n a) # (Sorted @{lo}))
    -> ((Vect (m+n) a) # (Sorted @{lo})) # \merged => (forall j . (Sorted @{lo} (j::subject xs)) -> (Sorted @{lo} (j::subject ys)) -> Sorted @{lo} (j::(subject merged)))
merge ([] # _)  y =  y # (\_ => \a => a)
merge x ([] # _) = rewrite (plusZeroIsSame m) in (x # (\w => \_ => w))
merge ((x::xs) # px) ((y::ys) # py) =
    let
        xrely: Either (rel x y) (rel y x) = case decEq x y of
            Yes xEqy => Left (equalityExtendsReflexion xEqy)
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
                    replace
                        { p = \swe => ((Vect swe a) # (Sorted @{lo})) # \merged => (forall j . (xsz: Sorted @{lo} (j:: x :: xs)) -> (ysz: Sorted @{lo} (j:: y :: ys)) -> Sorted @{lo} (j::(subject merged))) }
                        (sucIsEqual' (plusSuccRightSucc _ _))
                        (((y :: ysz) # (f (SeveralAreSorted @{lo} vrel px) py)) # (\(SeveralAreSorted xxa xxb) => \(SeveralAreSorted yya yyb) => (SeveralAreSorted yya $ f (SeveralAreSorted vrel xxb) yyb)))

nat0to3 : (Vect 4 Nat) # (Sorted {rel = LTE})
nat0to3 = [0, 1, 2, 3] # (SeveralAreSorted LTEZero (SeveralAreSorted (LTESucc LTEZero) (SeveralAreSorted (LTESucc (LTESucc LTEZero)) (SingletonIsSorted))))

nat4to6 : (Vect 3 Nat) # (Sorted {rel = LTE})
nat4to6 = [4, 5, 6] # (SeveralAreSorted (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) (SeveralAreSorted (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))) (SingletonIsSorted)))

nat0to6 : (Vect 7 Nat) # (Sorted {rel = LTE})
nat0to6 = subject $ merge {rel=LTE} nat0to3 nat4to6

public export
mergeSort : {a: Type} -> (DecEq a) => {rel: a->a->Type} -> (lo: LinearOrder a rel) => {m: Nat} -> Vect m a -> (Vect m a) # (Sorted @{lo})
mergeSort [] = [] # NilIsSorted
mergeSort [x] = [x] # SingletonIsSorted
mergeSort v =
    let
        (l # r) = Sorted.split v
        l' = mergeSort (assert_smaller v l)
        r' = mergeSort (assert_smaller v r)
        (res # _) = merge l' r'
    in
        rewrite (sym $ smallAndLargeHalfMakeWhole m) in res

main : IO ()
main = do
    putStrLn $ show $ subject (mergeSort {rel=LTE} [1, 2, 3, 4, 5])
