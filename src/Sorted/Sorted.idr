module Sorted.Sorted

import Control.Function
import Control.Order
import Control.Relation
import Data.Nat
import Data.Void
import Decidable.Equality

import Sorted.Sequence
import public Sorted.Relates

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
export
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

||| The tail of a sorted list is also a sorted list.
export
0 tail : LinearOrder a rel => OutputSequence a c => {0 ys: c} -> {0 ys≠【】: Not (ys = [])} -> (Sorted {rel} {c} ys) -> (Sorted {c} {rel} (Tail ys ys≠【】))
tail [] = void $ ys≠【】 Refl
tail (Singleton x) = replace {p = Sorted} (sym $ ThereCanOnlyBeOneTail x ys≠【】) []
tail (Several ys x∷y∷s≠【】 sorted_y∷s y∷s≠【】 rel_x_y) =
    replace {p = Sorted} (OST _ _ Refl x∷y∷s≠【】 ys≠【】) sorted_y∷s

||| The head of a sorted list is relates to all of the elements in the tail of the list.
export
0 head : LinearOrder a rel => OutputSequence a c => (ys: c) -> (ys≠【】: Not (ys = [])) -> Sorted {c} {rel} ys -> RelatesToAll {c} rel (Head ys ys≠【】) (Tail ys ys≠【】)
head ys ys≠【】 x with (sizeAccessible @{ContainerSized} ys)
  head _ ys≠【】 [] | acc = void $ ys≠【】 Refl
  head _ ys≠【】 (Singleton x) | acc = \guestInTail => void $ SIsNotZ (sym guestInTail \=> (cong (guest .#.) $ ThereCanOnlyBeOneTail x ys≠【】) \=> ∀x‥x⋕【】≐0)
  head ys ys≠【】 (Several ys x∷y∷s≠【】 sorted_y∷s y∷s≠【】 rel_h_ht) | Access acc = case decEq @{DecEqElement {c}} guest (Head ys ys≠【】) of
    (Yes Refl) => \_ => reflexive
    (No contra) =>
        let
            rec_step = (head (Tail ys x∷y∷s≠【】) y∷s≠【】 sorted_y∷s | acc _ (eqLTE $ TailIsShorter _ x∷y∷s≠【】))
            ost = cong (guest .#.) $ sym $ OutSequenceTail ys ys≠【】 x∷y∷s≠【】
        in \guestInTail => case decEq @{DecEqElement {c}} guest (Head (Tail ys x∷y∷s≠【】) y∷s≠【】) of
            (Yes Refl) => replace {p = \q => rel q (Head (Tail ys x∷y∷s≠【】) y∷s≠【】)} (OutSequenceHead ys x∷y∷s≠【】 ys≠【】) rel_h_ht
            (No guest_not_ht) =>
                replace {p = \q => rel q guest}
                    (OutSequenceHead ys x∷y∷s≠【】 ys≠【】)
                    (
                        rel_h_ht
                        \=> rec_step (
                            ConsKeepsRest guest_not_ht
                            \=> (cong (guest .#.) $ HeadTail (Tail ys x∷y∷s≠【】) y∷s≠【】)
                            \=> ost
                            \=> guestInTail
                        )
                    )

{0 x: t} -> Uninhabited t => Uninhabited (x = x) where
  uninhabited Refl = absurdity x

export
0 RelatesToAllTheRest: LinearOrder a rel => OutputSequence a c => {x:a} -> {xs: c} -> (xs≠【】: Not (xs = [])) -> rel x (Head xs xs≠【】) -> Sorted {rel} xs -> RelatesToAll rel x xs
RelatesToAllTheRest xs≠【】 x_rel_hxs srtd prf = case decEq @{DecEqElement {c}} guest (Head xs xs≠【】) of
  (Yes Refl) => x_rel_hxs
  (No guest_not_head) => x_rel_hxs \=> head xs xs≠【】 srtd (ConsKeepsRest {c} {xs = Tail xs xs≠【】} guest_not_head \=> cong (guest .#.) (HeadTail xs xs≠【】) \=> prf)
