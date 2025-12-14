module Sorted.Sequence

import public Sorted.Container


%default total

%hide Prelude.(::)
%hide Prelude.List.(++)
%hide Prelude.SnocList.(++)
%hide Prelude.Stream.(::)
%hide Prelude.Nil


||| An output sequence guarentees that the sequence in which elements are extracted using
||| this container's ConsBisurjective method is indifferent with respect to the proof
||| that the container is non-empty.
public export
interface Container a c => OutputSequence a c | c where
    OutSequenceHead : {auto x∷xs: c} -> (x∷xs≠【】: Not (x∷xs = (Nil {c}))) -> (x∷xs≠【】': Not (x∷xs = (Nil {c}))) -> ((Match x∷xs {x∷xs≠【】 = x∷xs≠【】}) .first) = ((Match x∷xs {x∷xs≠【】 = x∷xs≠【】'}) .first)
    OutSequenceTail : {auto x∷xs: c} -> (x∷xs≠【】: Not (x∷xs = (Nil {c}))) -> (x∷xs≠【】': Not (x∷xs = (Nil {c}))) -> ((Match x∷xs {x∷xs≠【】 = x∷xs≠【】}) .second) = ((Match x∷xs {x∷xs≠【】 = x∷xs≠【】'}) .second)

export
OSH : OutputSequence a c => (x∷xs: c) -> (x∷xs': c) -> (same: x∷xs = x∷xs') -> (x∷xs≠【】: Not (x∷xs = (Nil {c}))) -> (x∷xs≠【】': Not (x∷xs' = (Nil {c}))) -> ((Match x∷xs {x∷xs≠【】 = x∷xs≠【】}) .first) = ((Match x∷xs' {x∷xs≠【】 = x∷xs≠【】'}) .first)
OSH _ _ Refl = OutSequenceHead

export
OST : OutputSequence a c => (x∷xs: c) -> (x∷xs': c) -> (same: x∷xs = x∷xs') -> (x∷xs≠【】: Not (x∷xs = (Nil {c}))) -> (x∷xs≠【】': Not (x∷xs' = (Nil {c}))) -> ((Match x∷xs {x∷xs≠【】 = x∷xs≠【】}) .second) = ((Match x∷xs' {x∷xs≠【】 = x∷xs≠【】'}) .second)
OST _ _ Refl = OutSequenceTail

||| A Sequence guarantees that the sequence in which elements are extracted from an
||| OutputSequence (using ConsBisurjective) matches the order in which they were inserted
||| using the (::) operator.
|||
||| Note 1: because this requires an OutputSequence, we can provide ConsBisurjective
||| a standard proof for x∷xs≠【】 (UninhabitedConsIsNil) and rest asured that any other proof
||| would produce the same output.
public export
interface OutputSequence a c => Sequence a c | c where
    InSequenceHead : {auto x: a} -> {auto xs: c} -> (Match (x :: xs) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil {x} {xs}}}).first = x
    InSequenceTail : {auto x: a} -> {auto xs: c} -> (Match (x :: xs) {x∷xs≠【】 = uninhabited @{UninhabitedConsIsNil {x} {xs}}}).second = xs
