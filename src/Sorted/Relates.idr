module Sorted.Relates

import Control.Relation
import Decidable.Equality

import Sorted.Occurs
import Sorted.Perm

%default total

public export
RelatesToAll : {a: Type} -> Rel a -> a -> List a -> Type
RelatesToAll relates socialButterfly party = {guest: a} -> {n: Nat} -> Occurs guest (S n) party -> relates socialButterfly guest

infixr 4 -@->

public export
(-@->) : {x: a} -> {xs, ys: List a} -> RelatesToAll rel x xs -> (xs ~@~ ys) -> DecEq a => RelatesToAll rel x ys
(-@->) f g y = let 
    (_ ** gInXsPrf) = countOccurrences guest xs
  in f $ replace {p = \arg => Occurs guest arg xs} (g gInXsPrf y) gInXsPrf

public export
(::) : {0 a: Type} -> {0 x, y: a} -> {0 xs: List a} -> {0 rel: Rel a} -> rel x y -> RelatesToAll rel x xs -> RelatesToAll rel x (y::xs)
(::) z f (Here x) = z
(::) z f (There x g) = f x

public export
relatesToTail : {x: a} -> RelatesToAll rel e (x::xs) -> DecEq a => RelatesToAll rel e xs
relatesToTail {guest=victor} {n=m} f y with (decEq victor x)
  relatesToTail {guest=victor} {n=m} f y | (Yes prf) = f $ rewrite sym prf in Here y
  relatesToTail {guest=victor} {n=m} f y | (No contra) = f $ There y contra

public export
sameasitis : {xs: List a} -> xs ++ [] = xs
sameasitis {xs = []} = Refl
sameasitis {xs = (x :: xs)} = cong (x ::) $ sameasitis {xs=xs}

public export
(++) : {0 a: Type} -> {0 e: a} -> {0 rel: Rel a} -> {xs, ys: List a} -> RelatesToAll rel e xs -> RelatesToAll rel e ys -> DecEq a => RelatesToAll rel e (xs++ys)
(++) {xs = []} _ rYs x = rYs x
(++) {xs = (y :: xs)} {ys = []} rXs _ x = rXs $ rewrite sym $ sameasitis {xs=y::xs} in x
(++) {xs = (x'' :: xs)} {ys = (y :: ys)} rXs _ (Here x) = rXs $ Here $ snd $ (countOccurrences guest xs)
(++) {xs = (x'' :: xs)} {ys = (y :: ys)} f g (There x f1) = (++) (relatesToTail {rel=rel} f) {rel=rel} g x
