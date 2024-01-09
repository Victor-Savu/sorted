module Sorted.Relates

import Control.Relation
import Decidable.Equality

import Sorted.Occurs
import Sorted.IsPermutationOf

%default total

||| The type of proofs that a value relates to all the elements of a list.
public export
RelatesToAll : {a: Type} -> Rel a -> a -> List a -> Type
RelatesToAll relates socialButterfly party = {guest: a} -> {n: Nat} -> Occurs guest (S n) party -> relates socialButterfly guest

infixr 4 -@->

||| If x relates to all the elements of xs , then it relates to any permutation ys of the elements of xs
public export
(-@->) : {x: a} -> {xs, ys: List a} -> RelatesToAll rel x xs -> (xs ~@~ ys) -> DecEq a => RelatesToAll rel x ys
(-@->) f (Ipo g) y = let 
    (_ ** guestInXs) = countOccurrences guest xs
  in f $ replace {p = \arg => Occurs guest arg xs} (g guestInXs ..=.. y) guestInXs

public export
Nil : RelatesToAll rel x []
[] (Here _) impossible
[] (There _ _) impossible
[] Nowhere impossible

||| If x relates to y and x also relates to all the elements of the list xs then x relates to all the elements of y::xs
public export
(::) : {0 rel: Rel a} -> rel x y -> RelatesToAll rel x xs -> RelatesToAll rel x (y::xs)
(::) z f (Here x) = z
(::) z f (There x g) = f x

||| If e relates to all the elements in a non-empty list, it also relates to all the elements in the tail of the list
public export
tail : {x: a} -> RelatesToAll rel e (x::xs) -> DecEq a => RelatesToAll rel e xs
tail {guest=victor} {n=m} f y with (decEq victor x)
  tail {guest=victor} {n=m} f y | (Yes prf) = f $ rewrite sym prf in Here y
  tail {guest=victor} {n=m} f y | (No contra) = f $ There y contra

||| If e relates to all the elements in a non-empty list, it also relates to all the elements in the tail of the list
public export
head : {x: a} -> {xs: List a} -> RelatesToAll rel e (x::xs) -> DecEq a => rel e x
head r2a = r2a $ Here $ snd $ countOccurrences x xs

||| [] is right-neutral with respect to ++. Ideally this should have been provided by the Semigroup implementation for List but
||| the semigroup laws are not implemented.
public export
plusNilRightNeutral : {xs: List a} -> xs ++ [] = xs
plusNilRightNeutral {xs = []} = Refl
plusNilRightNeutral {xs = (x :: xs)} = cong (x ::) $ plusNilRightNeutral {xs=xs}

||| If e relates to all the elements in the list xs and to all the elements in the list ys then it relates to all the elements in the list xs++ys.
public export
(++) : {xs, ys: List a} -> RelatesToAll rel e xs -> RelatesToAll rel e ys -> DecEq a => RelatesToAll rel e (xs++ys)
(++) {xs = []} _ rYs x = rYs x
(++) {xs = (y :: xs)} {ys = []} rXs _ x = rXs $ rewrite sym $ plusNilRightNeutral {xs=y::xs} in x
(++) {xs = (x'' :: xs)} {ys = (y :: ys)} rXs _ (Here x) = rXs $ Here $ snd $ (countOccurrences guest xs)
(++) {xs = (x'' :: xs)} {ys = (y :: ys)} f g (There x f1) = (tail {rel=rel} f ++ g ) {rel=rel} x
