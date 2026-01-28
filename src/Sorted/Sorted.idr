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
          (x∷y∷s: c) -> (0 x∷y∷s≠【】: Not (x∷y∷s = [])) -> 
            (Sorted @{lo} @{seq} {rel} (Tail x∷y∷s x∷y∷s≠【】)) ->
            (0 y∷s≠【】: Not (Tail x∷y∷s x∷y∷s≠【】 = [])) ->
              rel (Head x∷y∷s x∷y∷s≠【】) (Head (Tail x∷y∷s x∷y∷s≠【】) y∷s≠【】) ->
              Sorted @{lo} @{seq} {rel} x∷y∷s

||| If x relates to all the elements of xs and xs is sorted with respect to the linear order induced by rel,
||| then x::xs is also sorted with respect to the same linear order.
(::) : DecEq a => LinearOrder a rel => Sequence a c => {x: a} -> RelatesToAll {a} {c} rel x ys -> Sorted {a} {c} {rel} ys -> Sorted {a} {c} {rel} ((x::ys) {c})
(::) f [] = Singleton x
(::) f (Singleton y) =
    let
        0 l0: (Tail [x, y] (uninhabited @{UninhabitedConsIsNil {c}}) = [y]) = InSequenceTail x [y]
        0 l5: (Not (Tail [x, y] (uninhabited @{UninhabitedConsIsNil {c}}) = [])) = (\arg => uninhabited @{UninhabitedConsIsNil {c}} ((sym l0) \=> arg))
    in Several
        [x, y]
        (uninhabited @{UninhabitedConsIsNil})
        (ford (sym (cong Sorted (InSequenceTail x [y]))) (Singleton {c} y))
        l5
        (
            replace {p = \q => q}
                (sym (
                    cong2 rel
                        (InSequenceHead {x=x} {xs=[y] {c}})
                        (OSH (Tail [x, y] (uninhabited @{UninhabitedConsIsNil})) ([y] {c}) l0 l5 (uninhabited @{UninhabitedConsIsNil})
                            \=> (InSequenceHead {c} {x=y} {xs=[]})))
                )
                (f {guest=y} (sym (ConsAddsOne {x=y} {xs=[]} {c})))
        )
(::) f (Several ys x∷y∷s≠【】 y y∷s≠【】 z)=
    let
        0 l0: (Tail (x :: ys) (uninhabited @{UninhabitedConsIsNil}) = ys) = InSequenceTail x ys
        0 l5 = (\arg => x∷y∷s≠【】 ((sym l0) \=> arg))
    in Several
        (x::ys)
        (uninhabited @{UninhabitedConsIsNil})
        (ford (sym (cong Sorted l0)) (Several ys x∷y∷s≠【】 y y∷s≠【】 z))
        l5
        (
            replace {p = \q => q}
                (sym (
                    cong2 rel
                        (InSequenceHead x ys)
                        (OSH (Tail (x::ys) (uninhabited @{UninhabitedConsIsNil})) ys l0 l5 x∷y∷s≠【】))
                )
                (f {guest=Head ys x∷y∷s≠【】} (sym (ConsAddsOne \=> cong (Head ys x∷y∷s≠【】 .#.) (HeadTail ys x∷y∷s≠【】))))
        )

export
infixr 4 -=@

||| An alternative notation for a sorted list
export
(-=@) : LinearOrder a rel => OutputSequence a c => c -> Type
(-=@) xs = Sorted {rel} xs

-- let
--                       (_, mumu) = ThereCanOnlyBeOne {c} {a} x ?huba
--                     in replace {p = \q => Sorted {rel} {c} q} mumu Nil

||| The tail of a sorted list is also a sorted list.
export
0 tail : LinearOrder a rel => DecEq a => OutputSequence a c => {ys: c} -> {0 ys≠【】: Not (ys = [])} -> (Sorted {rel} {c} ys) -> (Sorted {c} {rel} (Tail ys ys≠【】))
tail [] = void $ ys≠【】 Refl
tail (Singleton x) = ?tail_rhs_1
tail (Several _ _ _ _ _) = ?tail_missing_case_1
-- tail (Several x y) = ?tail_rhs_2

-- tail [] = absurdity @{UninhabitedConsIsNil} x∷xs≐ys
-- tail (Singleton y) with (ConsBiinjectiveWhenSingleton x∷xs≐ys)
--   tail (Singleton y) | (Refl, Refl) = []
-- tail (y :@: z) = ?tail_rhs_2_rhs2

-- tail [] = absurdity @{UninhabitedConsIsNil} ysIsCons
-- tail (Singleton y) = replace {p = \q => Sorted {rel} {c} q} (sym $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) []
-- tail (relXY :@: sortedYYs) = replace {p = \q => Sorted {rel} {c} q} (sym $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) sortedYYs

||| The head of a sorted list is relates to all of the elements in the tail of the list.
export
0 head : LinearOrder a rel => OutputSequence a c => DecEq a => {ysIsCons: x::xs = ys} -> Sorted {c} {rel} ys -> RelatesToAll {c} rel x xs
-- head [] _ = absurdity @{UninhabitedConsIsNil} ysIsCons
-- head (Singleton y) prf = void $ SIsNotZ $ (sym prf) \=> ((cong (guest .#.) $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) \=> NilIsEmpty)
-- head ((relXY :@: sortedYYs) {x=x'} {y} {ys}) prf with (biinjective @{ConsBiinjective {c}} ysIsCons)
--   head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) with (decEq guest y)
--     head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) | (Yes Refl) = relXY
--     head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) | (No guestNEqY) = relXY \=> (head {x=y} {xs=ys} {ys=y::ys} {ysIsCons=Refl} sortedYYs (ConsKeepsRest guestNEqY \=> prf))

{0 x: t} -> Uninhabited t => Uninhabited (x = x) where
  uninhabited Refl = absurdity x
