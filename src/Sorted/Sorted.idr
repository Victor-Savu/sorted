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

||| If x relates to all the elements of xs and xs is sorted with respect to the linear order induced by rel,
||| then x::xs is also sorted with respect to the same linear order.
(::) : DecEq a => LinearOrder a rel => Sequence a c => {x: a} -> RelatesToAll {a} {c} rel x ys -> Sorted {a} {c} {rel} ys -> Sorted {a} {c} {rel} ((x::ys) {c})
(::) f [] = Singleton x
(::) f (Singleton y) = ?singleton_prf
    -- Solved but it takes a ton of time and memory to typecheck/build 
    -- let
    --     ist = InSequenceTail {x=x} {xs=[y] {c}}
    --     0 ish = InSequenceHead {x=x} {xs=[y] {c}}
    --     ish' = InSequenceHead {c} {x=y} {xs=[]}
    --     mu = sym (ConsAddsOne {x=y} {xs=[]} {c})
    --     ucn = uninhabited @{UninhabitedConsIsNil {c} {x=y} {xs=[]}}
    --     muda = \ala => ucn (rewrite sym ist in ala)
    --     hjfks = (f {guest=y} mu)
    --     osha = OSH ((Match {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}} [x, y]) .second) ([y] {c}) ist muda (uninhabited @{UninhabitedConsIsNil})
    --     shkh = cong2 rel ish (osha \=> ish')
    -- in Several
    --     {x∷y∷s≠【】 = uninhabited @{UninhabitedConsIsNil}}
    --     (ford (sym (cong (Sorted {rel}) (InSequenceTail {x=x} {xs=[y] {c}}))) (Singleton {c} y))
    --     {y∷s≠【】 = muda}
    --     (replace {p = \q => q} (sym shkh) hjfks)
(::) f (Several {x∷y∷s≠【】 = ys≠【】} g y) = ?several_prf
    -- Solved but it takes a ton of time and memory to typecheck/build 
    --   let
    --     0 l0: ((Match (x :: ys) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}}).second = ys) =
    --         InSequenceTail
    --     0 l1: (Sorted {rel} (Match (x :: ys) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}}).second = Sorted {rel} ys) =
    --         cong Sorted l0
    --     0 l3: (Not ((Match (x :: ys) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}}).second = [])) =
    --         \ctra => ys≠【】 (sym l0 \=> ctra)
    --     0 l5: ((Match (x :: ys) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}}) .first = x) =
    --         InSequenceHead
    --     0 l7: (((Match ((Match (x :: ys) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}}) .second) {x∷xs≠【】 = l3}) .first) = ((Match ys {x∷xs≠【】 = ys≠【】}) .first)) =
    --         OSH ((Match (x :: ys) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}}) .second) ys InSequenceTail l3 ys≠【】
    --     0 l6: ((rel ((Match (x :: ys) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}}).first) ((Match ((Match (x :: ys) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}}) .second) {x∷xs≠【】 = l3}) .first)) = rel x ((Match ys {x∷xs≠【】 = ys≠【】}) .first)) =
    --         cong2 rel (InSequenceHead) l7
    --     l8: ((Match ys {x∷xs≠【】=ys≠【】}).first .#. ys = S ((Match ys {x∷xs≠【】=ys≠【】}).first .#. (Match ys {x∷xs≠【】=ys≠【】}).second)) =
    --         sym (ConsAddsOne \=> cong ((Match ys {x∷xs≠【】=ys≠【】}).first .#.) (Match ys {x∷xs≠【】=ys≠【】}).biexists)
    --     l9: (rel x (Match ys {x∷xs≠【】=ys≠【】}).first) = f l8
    --     l4: rel ((Match (x :: ys) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}}).first) ((Match ((Match (x :: ys) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil}}) .second) {x∷xs≠【】 = l3}) .first) =
    --         ford (sym l6) l9
    --   in Several {x∷y∷s≠【】 = uninhabited @{UninhabitedConsIsNil}} (ford (sym l1) (Several g y)) l4

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
