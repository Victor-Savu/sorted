module Sorted.Sorted

import Control.Function
import Control.Order
import Control.Relation
import Data.Nat
import Data.Void
import Decidable.Equality

import Sorted.Sequence
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
%hide Prelude.List.(++)
%hide Prelude.SnocList.(++)

namespace Sorted
  ||| A list sorted according to a relation over the type of its elements.
  public export
  data Sorted: LinearOrder a rel => OutputSequence a c => c -> Type where
      ||| An empty list is always sorted.
      Nil: (seq: OutputSequence a c) => Sorted @{lo} @{seq} []

      ||| A list with a single element is always sorted.
      Singleton: (seq: OutputSequence a c) => (x: a) -> Sorted @{lo} @{seq} [x]

      ||| Rel must induce a linear order over the type of elements in order to be useful for sorting.
      ||| If an element x relates to the head y of a sorted list y::ys, then x::y::ys is also sorted with respect to rel.
      Several: (seq: OutputSequence a c) =>
          {x∷y∷s: c} -> {auto 0 x∷y∷s≠【】: Not (x∷y∷s = [])} -> 
            (Sorted @{lo} @{seq} {rel} ((Match x∷y∷s).second)) ->
            {auto 0 y∷s≠【】: Not ((Match x∷y∷s).second = [])} ->
              rel (Match x∷y∷s).first (Match ((Match x∷y∷s).second)).first ->
              Sorted @{lo} @{seq} {rel} x∷y∷s


-- THIS CAUSES THE MEMORY TO EXPLODE!
-- ||| If x relates to all the elements of xs and xs is sorted with respect to the linear order induced by rel,
-- ||| then x::xs is also sorted with respect to the same linear order.
-- export
-- (::) : DecEq a => LinearOrder a rel => Sequence a c => {x: a} -> RelatesToAll {a} {c} rel x ys -> Sorted {a} {c} {rel} ys -> Sorted {a} {c} {rel} ((x::ys) {c})
-- (::) f [] = Singleton x
-- (::) f (Singleton y) =
--       let
--         0 ist = InSequenceTail {x=x} {xs=[y] {c}}
--         0 ish = InSequenceHead {x=x} {xs=[y] {c}}
--         0 ish' = InSequenceHead {c} {x=y} {xs=[]}
--         mu = sym (ConsAddsOne {x=y} {xs=[]} {c})
--         ucn = uninhabited @{UninhabitedConsIsNil {c} {x=y} {xs=[]}}
--         muda = \ala => ucn (rewrite sym ist in ala)
--         hjfks = (f {guest=y} mu)
--         -- 0 osha = OSH ((Match {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}} [x, y]) .second) ([y] {c})
--         shkh = cong2 rel ish ?bish
--       in Several
--           {x∷y∷s≠【】 = uninhabited @{UninhabitedConsIsNil}}
--           (ford (sym (cong (Sorted {rel}) (InSequenceTail {x=x} {xs=[y] {c}}))) (Singleton {c} y))
--           {y∷s≠【】 = muda}
--           (replace {p = \q => q} (sym shkh) hjfks) -- (cong2 ?ala ?bala ?op_rhs_3)
-- (::) f (Several g y) = ?op_rhs_2
-- (::) f [] = Singleton x
-- (::) f (Singleton y) = Several (f $ sym ConsAddsOne \=> cong S NilIsEmpty) (Singleton y) ?adsa
-- (::) f (Several y z prf) = ?op_rhs_2
-- (::) f [] = Singleton x
-- (::) f (Singleton {x=x'}) = (f $ sym ConsAddsOne \=> cong S NilIsEmpty) :@: Singleton x'
-- (::) f ((relX'Y :@: sortedYYs) {x=x'} {ys} {y}) = (f $ sym ConsAddsOne) :@: relX'Y :@: sortedYYs

export
infixr 4 -=@

||| An alternative notation for a sorted list
export
(-=@) : LinearOrder a rel => Container a c => Sequence a c => c -> Type
(-=@) xs = Sorted {rel} xs

-- ||| The tail of a sorted list is also a sorted list.
-- export
-- 0 tail : LinearOrder a rel => DecEq a => Container a c => Sequence a c => {ys: c} -> {ysNotNil: Not (ys = [])} -> (Sorted {rel} {c} ys) -> (Sorted {c} {rel} (snd (Next ys ysNotNil).fst))
-- tail [] = absurdity @{UninhabitedConsIsNil} x∷xs≐ys
-- tail (Singleton y) with (ConsBiinjectiveWhenSingleton x∷xs≐ys)
--   tail (Singleton y) | (Refl, Refl) = []
-- tail (y :@: z) = ?tail_rhs_2_rhs2

-- tail [] = absurdity @{UninhabitedConsIsNil} ysIsCons
-- tail (Singleton y) = replace {p = \q => Sorted {rel} {c} q} (sym $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) []
-- tail (relXY :@: sortedYYs) = replace {p = \q => Sorted {rel} {c} q} (sym $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) sortedYYs

-- ||| The head of a sorted list is relates to all of the elements in the tail of the list.
-- export
-- 0 head : LinearOrder a rel => Container a c => DecEq a => {ysIsCons: x::xs = ys} -> Sorted {c} {rel} ys -> RelatesToAll {c} rel x xs
-- head [] _ = absurdity @{UninhabitedConsIsNil} ysIsCons
-- head (Singleton y) prf = void $ SIsNotZ $ (sym prf) \=> ((cong (guest .#.) $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) \=> NilIsEmpty)
-- head ((relXY :@: sortedYYs) {x=x'} {y} {ys}) prf with (biinjective @{ConsBiinjective {c}} ysIsCons)
--   head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) with (decEq guest y)
--     head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) | (Yes Refl) = relXY
--     head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) | (No guestNEqY) = relXY \=> (head {x=y} {xs=ys} {ys=y::ys} {ysIsCons=Refl} sortedYYs (ConsKeepsRest guestNEqY \=> prf))

{0 x: t} -> Uninhabited t => Uninhabited (x = x) where
  uninhabited Refl = absurdity x
