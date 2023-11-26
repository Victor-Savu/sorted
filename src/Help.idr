module Help

import Data.Nat
import Data.Nat.Order
import Control.Order

%default total

public export
interface (PartialOrder ty rel, StronglyConnex ty rel) => StrongLinearOrder ty rel where

data Sorted: (0 lo: StrongLinearOrder a rel) => (0 rel: a -> a -> Type) -> (0 _: List a) -> Type where
    NilIsSorted: Sorted @{lo} rel Nil
    SingletonIsSorted : (0 x: a) -> Sorted @{lo} rel [x]
    ListIsSorted: (0 x: a) -> (0 _: rel x y) -> (0 _: Sorted @{lo} rel (y::ys)) -> Sorted @{lo} rel (x::y::ys)


data Prop: (a: Type) -> (p : (0 _:a) -> Type) -> Type where
    (#): {a: Type} -> {0 p : (0 _:a) -> Type} -> (f: a) -> (0 prf: p f) -> Prop a p

0 sortedTail : (0 lo: StrongLinearOrder a rel) => Sorted @{lo} rel (x::xs) -> Sorted @{lo} rel xs
sortedTail (SingletonIsSorted x) = NilIsSorted
sortedTail (ListIsSorted x z w) = w

x : Prop (List Nat) (Sorted @{_} LTE)
x = [0, 1, 2, 3] # (ListIsSorted 0 LTEZero (ListIsSorted 1 (LTESucc LTEZero) (ListIsSorted 2 (LTESucc (LTESucc LTEZero)) (SingletonIsSorted 3))))

y : Prop (List Nat) (Sorted @{_} LTE)
y = [4, 5, 6] # (ListIsSorted 4 (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) (ListIsSorted 5 (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))) (SingletonIsSorted 6)))


split : List a -> Pair (List a) (List a)
split [] = ([], [])
split (x :: Nil) = ([], [x])
split (x::y::tail) = let (xs, ys) = Help.split tail in (x::xs, y::ys)

merge: (lo: StrongLinearOrder a rel) -> (Prop (List a) (Sorted @{lo} rel)) -> (Prop (List a) (Sorted @{lo} rel)) -> (Prop (List a) (Sorted @{lo} rel))
merge _ x ([] # _) = x
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

mergeSort : (lo: StrongLinearOrder a rel) -> List a -> Prop (List a) (Sorted @{lo} rel)
mergeSort lo [] = ?mergeSort_rhs_0
mergeSort lo (x :: []) = ?mergeSort_rhs_2
mergeSort lo (x :: (y :: xs)) = ?mergeSort_rhs_3
        