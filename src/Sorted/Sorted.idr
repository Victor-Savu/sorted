module Sorted.Sorted

import Control.Function
import Control.Order
import Control.Relation
import Data.Nat
import Data.Void
import Decidable.Equality

import Sorted.Container
import Sorted.Relates

%default total

export
infixr 4 :@:

%hide Stream.(::)
%hide Prelude.(::)
%hide Builtin.(#)
%hide Builtin.DPair.(#)
%hide Relates.(::)
%hide Relates.Nil
%hide Prelude.Nil

||| A list sorted according to a relation over the type of its elements.
public export
data Sorted: LinearOrder a rel => Sequence a c => c -> Type where
    ||| An empty list is always sorted.
    Nil:  Sorted @{lo} @{seq} ([] @{ct})

    ||| A list with a single element is always sorted.
    Singleton : (x: a) -> Sorted @{lo} @{seq} {rel} ((x :: ([] @{ct}))  @{ct})

    ||| Rel must induce a linear order over the type of elements in order to be useful for sorting.
    ||| If an element x relates to the head y of a sorted list y::ys, then x::y::ys is also sorted with respect to rel.
    Several: (lo: LinearOrder a rel) => (seq: Sequence a c) => {x, y: a} -> {xys, ys: c} -> rel x y -> {auto 0 xys≠【】: Not (xys = ([] {c}))} -> {auto 0 ys≠【】: Not (ys = ([] {c}))} -> (Sorted @{lo} @{seq} {rel} ys) -> ((Next @{seq} xys {xss≠【】 = xys≠【】}).fst = (x, ys)) ->  (fst ((Next ys {xss≠【】= ys≠【】}).fst) = y) ->  Sorted @{lo} @{seq} {rel} xys

||| If x relates to all the elements of xs and xs is sorted with respect to the linear order induced by rel,
||| then x::xs is also sorted with respect to the same linear order.
-- export
-- (::) : DecEq a => LinearOrder a rel => Sequence a c => RelatesToAll {c} rel x ys -> Sorted {c} {rel} ys -> Sorted {c} {rel} ((x::xs) {c})
-- (::) f [] = Singleton x
-- (::) f (Singleton y) = Several (f $ sym ConsAddsOne \=> cong S NilIsEmpty) (Singleton y) ?adsa
-- (::) f (Several y z prf) = ?op_rhs_2
-- (::) f [] = Singleton x
-- (::) f (Singleton {x=x'}) = (f $ sym ConsAddsOne \=> cong S NilIsEmpty) :@: Singleton x'
-- (::) f ((relX'Y :@: sortedYYs) {x=x'} {ys} {y}) = (f $ sym ConsAddsOne) :@: relX'Y :@: sortedYYs

-- export
-- infixr 4 -=@

-- ||| An alternative notation for a sorted list
-- export
-- (-=@) : LinearOrder a rel => Container a c => Sequence a c => c -> Type
-- (-=@) xs = Sorted {rel} xs

-- ||| The tail of a sorted list is also a sorted list.
-- export
-- 0 tail : LinearOrder a rel => DecEq a => Container a c => Sequence a c => {ys: c} -> {ysNotNil: Not (ys = [])} -> (Sorted {rel} {c} ys) -> (Sorted {c} {rel} (snd (Next ys ysNotNil).fst))
-- tail [] = absurdity @{uninhabitedConsIsNil} x∷xs≐ys
-- tail (Singleton y) with (ConsBiinjectiveWhenSingleton x∷xs≐ys)
--   tail (Singleton y) | (Refl, Refl) = []
-- tail (y :@: z) = ?tail_rhs_2_rhs2

-- tail [] = absurdity @{uninhabitedConsIsNil} ysIsCons
-- tail (Singleton y) = replace {p = \q => Sorted {rel} {c} q} (sym $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) []
-- tail (relXY :@: sortedYYs) = replace {p = \q => Sorted {rel} {c} q} (sym $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) sortedYYs

-- ||| The head of a sorted list is relates to all of the elements in the tail of the list.
-- export
-- 0 head : LinearOrder a rel => Container a c => DecEq a => {ysIsCons: x::xs = ys} -> Sorted {c} {rel} ys -> RelatesToAll {c} rel x xs
-- head [] _ = absurdity @{uninhabitedConsIsNil} ysIsCons
-- head (Singleton y) prf = void $ SIsNotZ $ (sym prf) \=> ((cong (guest .#.) $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) \=> NilIsEmpty)
-- head ((relXY :@: sortedYYs) {x=x'} {y} {ys}) prf with (biinjective @{ConsBiinjective {c}} ysIsCons)
--   head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) with (decEq guest y)
--     head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) | (Yes Refl) = relXY
--     head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) | (No guestNEqY) = relXY \=> (head {x=y} {xs=ys} {ys=y::ys} {ysIsCons=Refl} sortedYYs (ConsKeepsRest guestNEqY \=> prf))

{0 x: t} -> Uninhabited t => Uninhabited (x = x) where
  uninhabited Refl = absurdity x
