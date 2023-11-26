module Help

import Data.Vect
import Data.Nat
import Data.Nat.Order
import Control.Order

%default total

public export
interface (PartialOrder ty rel, StronglyConnex ty rel) => StrongLinearOrder ty rel where

data Sorted: (0 lo: StrongLinearOrder a rel) => (0 rel: a -> a -> Type) -> (0 _: Vect n a) -> Type where
    NilIsSorted: Sorted @{lo} rel Nil
    SingletonIsSorted : (0 x: a) -> Sorted @{lo} rel [x]
    ListIsSorted: (0 x: a) -> (0 _: rel x y) -> (0 _: Sorted @{lo} rel (y::ys)) -> Sorted @{lo} rel (x::y::ys)


data Prop: (a: Type) -> (p : (0 _:a) -> Type) -> Type where
    (#): {a: Type} -> {0 p : (0 _:a) -> Type} -> (f: a) -> (0 prf: p f) -> Prop a p

subject : Prop a p -> a
subject (f # prf) = f


0 sortedTail : (0 lo: StrongLinearOrder a rel) => Sorted @{lo} rel (x::xs) -> Sorted @{lo} rel xs
sortedTail (SingletonIsSorted x) = NilIsSorted
sortedTail (ListIsSorted x z w) = w

x : Prop (Vect 4 Nat) (Sorted @{_} LTE)
x = [0, 1, 2, 3] # (ListIsSorted 0 LTEZero (ListIsSorted 1 (LTESucc LTEZero) (ListIsSorted 2 (LTESucc (LTESucc LTEZero)) (SingletonIsSorted 3))))

y : Prop (Vect 3 Nat) (Sorted @{_} LTE)
y = [4, 5, 6] # (ListIsSorted 4 (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) (ListIsSorted 5 (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))) (SingletonIsSorted 6)))

-- We need to prove that any natural number can be written as either 2*n or 2*n+1

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

smallAndLargeMakeWhole : (n: Nat) -> (smallHalf n + largeHalf n = n)
smallAndLargeMakeWhole n with (parity n)
    smallAndLargeMakeWhole (j + j) | Even = Refl
    smallAndLargeMakeWhole (S (j + j)) | Odd = sym (plusSuccRightSucc j j)

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

split : Vect n a -> Pair (Vect (smallHalf n) a) (Vect (largeHalf n) a)
split [] = ([], [])
split (x :: Nil) = ([], [x])
split (x::y::tail) =
    let (xs, ys) = Help.split tail in
        ( replace {p = \k => Vect k a} (sym (smallHalfGrowsEvery2 (veclen tail))) (x::xs)
        , replace {p = \k => Vect k a} (sym (largeHalfGrowsEvery2 (veclen tail))) (y::ys))

sucIsEqual: (n: Nat) -> (S n = S n)
sucIsEqual n = Refl

plusZeroIsSame: (m: Nat) -> (m+0 = m)
plusZeroIsSame 0 = Refl
plusZeroIsSame (S k) = rewrite plusZeroIsSame k in (sucIsEqual k)

pairwise : {1 n: Nat} -> (1 _: Vect (n+n) a) -> Vect n (a, a)
pairwise {n = 0} Nil = Nil
pairwise {n = S k} (x::xs) =
    let
        prf = sym (plusSuccRightSucc k k)
        y::ys : Vect (S (k+k)) a = replace {p = \swe => Vect swe a} prf xs
    in
        (x, y)::(pairwise ys)

merge: {0 m: Nat} -> {0 n: Nat} -> (lo: StrongLinearOrder a rel) -> (Prop (Vect m a) (Sorted @{lo} rel)) -> (Prop (Vect n a) (Sorted @{lo} rel)) -> (Prop (Vect (m+n) a) (Sorted @{lo} rel))
merge {m} _ x ([] # _) =
    let
        0 theEquality = sym (plusZeroIsSame m)
        qqq : (Prop (Vect (m+0) a) (Sorted @{_} rel)) = replace {p = \m => Prop (Vect m a) (Sorted @{_} rel)} theEquality x
    in
        ?help -- replace {p = \k => Prop (Vect k a) (Sorted @{_} _)} theEquality (x # px)
merge _ ([] # _) y = y
merge lo ((x::xs) # px) ((y::ys) # py) =
    case order @{_} x y of
        Left vrel =>
            let
                (xsz # pxz) = merge lo (xs # (sortedTail px)) (y::ys # py)
            in
                (x::xsz # (ListIsSorted x ?xSmallest pxz))
        Right vrel =>
            let
                (ysz # pxz) = merge lo (x::xs # px) (ys # (sortedTail py))
            in
                ?help1 -- ((y::ysz) # (ListIsSorted y vrel ?pyz))

-- mergeSort : (lo: StrongLinearOrder a rel) -> List a -> Prop (List a) (Sorted @{lo} rel)
-- mergeSort lo [] = ?mergeSort_rhs_0
-- mergeSort lo (x :: []) = ?mergeSort_rhs_2
-- mergeSort lo (x :: (y :: xs)) = ?mergeSort_rhs_3
        