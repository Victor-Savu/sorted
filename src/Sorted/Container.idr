module Sorted.Container

import public Control.Relation
import public Control.WellFounded
import Data.Void
import Data.Nat
import Data.Void
import public Data.DPair
import public Decidable.Equality

export infixr 9 .#.

export infixl 4 \=>

export
(\=>) : {x, y, z: ty} -> Transitive ty rel => rel x y -> rel y z -> rel x z
a \=> b = transitive a b

%default total

%hide Prelude.(::)
%hide Prelude.List.(++)
%hide Prelude.SnocList.(++)
%hide Prelude.Stream.(::)
%hide Prelude.Nil


export
ford : (0 _: a = b) -> a -> b
ford Refl = id


export
eqLTE : {x, y: Nat} -> x = y -> LTE x y
eqLTE Refl = reflexive

||| A container is a type that
||| a. has an element representing the empty container
||| b. has a way to add an element to an existing container such that the resulting container contains exactly one more instance of that new element
|||    and just as many instances of any other element of the original container
|||
||| The container interface is satisfied by:
||| - the type a representing the type of elements in the container
||| - the type construtor c: Type -> Type which constructs the type of the container: c
||| if it can:
||| 1. provide a counting function (.#.): a -> c -> Nat which counts the number of occurrences of a value of type a in the container of type c
||| 1. produce an "empty" container from thin air (using Nil). The empty container is a specific instance of c (call it xs) which must satisfy the
|||    property that any value of type a occurs 0 times in xs according to the counting function. Basically, a container is empty if nothing occurs in it.
||| 2. produce an "inhabited" container by applying (::) to an element of type a (call it x) and another container of type c (call it xs). The
|||    "inhabited" container is a specific instance of c (call it xxs) which must satisfy two properties:
|||    1. As counted by (.#.), x occurs in xxs one time more than it occurs in xs (showing that x was inserted exactly once by (::))
|||    2. Given any other element of a (call it x'), that element will occur the same number of times in xs as it does in xxs (showing that no other
|||       element of xs was duplicated or removed by (::))
export
interface Container a c | c where
    constructor MkContainer

    ||| Counts the number of occurrences of an an element in the container
    (.#.) : a -> c -> Nat

    ||| There exists an empty container
    Nil : c
    ||| It is decidable whether a container is empty
    IsNil: (xs: c) -> Dec (xs = Nil)
    ||| No element occurs in the empty container
    ∀x‥x⋕【】≐0 : {x: a} -> x .#. Nil = 0

    ||| Cons: adding an element to a container
    (::) : a -> c -> c
    ||| Given two elements and a container, at least one of the following is true:
    |||  1. The two elements are equal
    |||       AND
    |||     when we append an element to the container, the element will appear one extra time in the result than in the original container
    |||  2. The two elements are not equal
    |||       AND
    |||     when we append one element to the container, the other element will appear the same number of times in the result as it does in the original container
    Cons : {x, x': a} -> {xs: c} -> Either ((x'=x), (1 + x .#. xs) = x .#. (x :: xs)) (Not (x'=x), x' .#. xs =  x' .#. (x::xs))

    Head: (x∷xs: c) -> (0 x∷xs≠【】: Not (x∷xs = [])) -> a
    Tail: (x∷xs: c) -> (0 x∷xs≠【】: Not (x∷xs = [])) -> c
    
    HeadTail: (x∷xs: c) -> (0 x∷xs≠【】: Not (x∷xs = [])) -> (Head x∷xs x∷xs≠【】)::(Tail x∷xs x∷xs≠【】) = x∷xs

    ||| Concatenation
    (++) : (xs: c) -> (ys: c) -> c
    ||| An element occurs in the concatenation of two containers the total number of times it occurs in each container
    ConcAddsCounts : {x: a} -> {xs, ys: c} -> x .#. (xs ++ ys) = x .#. xs + x .#. ys
    
    ||| Containers are sized
    ContainerSized : Sized c
    ||| For the implementation of size, the size of te empty container is 0
    ⋕⎨【】⎬≐0: size @{ContainerSized} Nil = 0
    ||| Cons-ing an element to a container increases the size by exactly 1
    ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬: {x: a} -> {xs: c} -> size @{ContainerSized} (x::xs) = S (size @{ContainerSized} xs)
    ||| Only the empty container has size 0
    ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】: {xs: c} -> (size @{ContainerSized} xs = 0) -> xs = Nil

-- export
-- interface Container a c => Container a c' => ContainerImage a c c' where
--   image: c -> c'
--   elementInImage: (xs: c) -> (x: a) -> x .#. xs = S n -> x .#. image xs = 1
--   strangerNotInImage: (xs: c) -> (x: a) -> x .#. xs = 0 -> x .#. image xs = 0

export
SizedNil: Container a c => (y : c) -> LTE (S (size @{ContainerSized} y)) (size @{ContainerSized} (Nil {c})) -> Accessible (\x, y => LTE (S (size @{ContainerSized} x)) (size @{ContainerSized} y)) y
SizedNil y x = absurdity $ replace {p = \q => q} (cong (LTE (S (size @{ContainerSized} y))) (⋕⎨【】⎬≐0 {c})) x

export
AccessNil: Container a c => Accessible (\x, y => LTE (S (size @{ContainerSized} x)) (size @{ContainerSized} y)) (Nil {c})
AccessNil = Access SizedNil

||| The first half of `Container.Cons` above
export
ConsAddsOne : Container a c => {x: a} -> {xs: c} -> (1 + x .#. xs) = x .#. (x :: xs)
ConsAddsOne with (Cons {x} {x'=x} {xs})
  ConsAddsOne | (Left (_, cons_adds_one)) = cons_adds_one
  ConsAddsOne | (Right (x≠x, _)) = void $ x≠x Refl

||| The second half of `Container.Cons` above
export
ConsKeepsRest : Container a c => {x, x': a} -> {xs: c} -> Not (x'=x) ->  x' .#. xs =  x' .#. (x::xs)
ConsKeepsRest x'≠x with (Cons {x} {x'} {xs})
  ConsKeepsRest x'≠x | (Left (Refl, _)) = void $ x'≠x Refl
  ConsKeepsRest x'≠x | (Right (_, cons_keeps_rest)) = cons_keeps_rest

||| There is only one empty container
export
NilIsUnique : Container a c => {xs: c} -> ((x: a) -> (x .#. xs) {c} = 0) -> xs = Nil
NilIsUnique x∉xs = case IsNil xs of
  (Yes Refl) => Refl
  (No xs≠【】) => void $ SIsNotZ (ConsAddsOne \=> cong ((Head xs xs≠【】) .#.) (HeadTail xs xs≠【】) \=> x∉xs (Head xs xs≠【】))

export
[UninhabitedConsIsNil] Container a c => Uninhabited (x::xs = (Nil {c})) where
    uninhabited x∷xs≐【】 = absurdity $ ConsAddsOne \=> (cong (x .#.) x∷xs≐【】) \=>  (∀x‥x⋕【】≐0)

export
ConcNilNilNil: Container a c => [] ++ [] = ([] {c})
ConcNilNilNil = NilIsUnique (\x => ConcAddsCounts \=> cong2 (+) ∀x‥x⋕【】≐0 ∀x‥x⋕【】≐0)

export
TailIsShorter: Container a c => (xs: c) -> (0 xs≠【】: Not (xs = [] {c})) -> S (size @{ContainerSized} $ Tail xs xs≠【】) = size @{ContainerSized} xs
TailIsShorter xs xs≠【】 = sym ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=> cong (size @{ContainerSized}) (HeadTail xs xs≠【】)

ConcNotNilLeft: Container a c => {xs: c} -> {ys: c} -> {xs≠【】: Not (xs = [])} -> Not (xs ++ ys = (Nil {c}))
ConcNotNilLeft prf = SIsNotZ (cong (+ (Head xs xs≠【】 .#. ys)) (ConsAddsOne \=> (cong (Head xs xs≠【】 .#.) $ HeadTail xs xs≠【】)) \=> sym ConcAddsCounts \=> cong (Head xs xs≠【】 .#.) prf \=> ∀x‥x⋕【】≐0)

export
[DecEqElement] Container a c => DecEq a where
  decEq x y with (Cons {x=y} {x'=x} {xs=(Nil {c})})
    decEq _ y | (Left (Refl, _)) = Yes Refl
    decEq x y | (Right (x≠y, _)) = No x≠y


export
ThereCanOnlyBeOneTail : Container a c => (x: a) -> (0 x≠【】:  Not ([x]=[] {c})) -> Tail [x] x≠【】 = ([] {c})
ThereCanOnlyBeOneTail x x≠【】 =
  ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】 (
    injective (
      sym ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=>
        cong (size @{ContainerSized}) (HeadTail _ x≠【】) \=>
          ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=>
            (cong S ⋕⎨【】⎬≐0)
    )
  )


export
ThereCanOnlyBeOneHead : Container a c => (x: a) -> (0 x≠【】:  Not ([x]=[] {c})) -> Head [x] x≠【】 = x
ThereCanOnlyBeOneHead x x≠【】 = case decEq @{DecEqElement {c}} (Head [x] x≠【】) x of
  (Yes prf) => prf
  (No contra) => void $ SIsNotZ (
      ConsAddsOne
      \=> (cong (Head [x] x≠【】 .#.) $ HeadTail _ x≠【】)
      \=> sym (ConsKeepsRest {xs=([] {c})} contra) \=> ∀x‥x⋕【】≐0
    )

export
CongCons : Container a c => {x, y: a} -> {xs, ys: c} -> (x .#. xs = x .#. ys) -> x .#. (y::xs) = x .#. (y::ys)
CongCons x⋕xs≐x⋕ys with (decEq @{DecEqElement {a} {c}} x y)
  CongCons x⋕xs≐x⋕ys | (Yes Refl) = sym (ConsAddsOne) \=> cong S x⋕xs≐x⋕ys \=> ConsAddsOne
  CongCons x⋕xs≐x⋕ys | (No x≠y) = sym (ConsKeepsRest x≠y) \=> x⋕xs≐x⋕ys \=> (ConsKeepsRest x≠y)

export
Remove: Container a c => (x: a) -> (xs: c) -> Subset c (
  \ys => (
    x .#. ys = 0,
    ((y: a) -> Not (y=x) -> y .#. xs = y .#. ys),
    size @{ContainerSized} xs = x .#. xs + size @{ContainerSized} ys
    )
  )
Remove x xs with (sizeAccessible @{ContainerSized} xs)
  Remove x xs | acc with (IsNil xs)
    Remove x _ | acc | (Yes Refl) = Element Nil (∀x‥x⋕【】≐0, \_ => \_ => Refl, cong (+ size @{ContainerSized} (Nil {c})) (sym ∀x‥x⋕【】≐0 ))
    Remove x xs | acc | (No xs≠【】) with (HeadTail xs xs≠【】)
      Remove x xs | Access acc | No xs≠【】 | (headXs∷TailXs≐xs) =
        let
          -- Element tailXs⧷⎨x⎬ prf = (Remove x (Tail _ xs≠【】) | acc _ $ eqLTE $ sym $ rewrite sym headXs∷TailXs≐xs in rewrite sym headXs∷TailXs≐xs in ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ {x=Head _ xs≠【】})
          Element tailXs⧷⎨x⎬ prf = (Remove x (Tail _ xs≠【】) | acc _ $ eqLTE $ TailIsShorter _ xs≠【】)
          0 x∉TailXs⧷⎨x⎬ = fst prf
          0 prf = snd prf
          0 prover = fst prf
          0 otherer = snd prf
        in case decEq @{DecEqElement {a} {c}} x (Head _ xs≠【】) of
          (Yes Refl) => Element tailXs⧷⎨x⎬ (
              x∉TailXs⧷⎨x⎬,
              \z => \z≠HeadXs => rewrite sym headXs∷TailXs≐xs in ((sym (ConsKeepsRest z≠HeadXs)) \=> prover z z≠HeadXs),
              sym (cong (size @{ContainerSized {c}}) headXs∷TailXs≐xs)
                \=> (∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ {x=Head xs xs≠【】} {xs=Tail xs xs≠【】})
                \=> cong S otherer \=> (cong (+ size @{ContainerSized} tailXs⧷⎨x⎬) ConsAddsOne)
                \=> (cong (\arg => (Head xs xs≠【】 .#. arg) + (size @{ContainerSized {c}} tailXs⧷⎨x⎬)) headXs∷TailXs≐xs)
            )
          (No x≠HeadXs) => Element ((Head xs xs≠【】)::tailXs⧷⎨x⎬) (rewrite sym headXs∷TailXs≐xs in (
              sym (ConsKeepsRest x≠HeadXs) \=> x∉TailXs⧷⎨x⎬,
              \y => \y≠x => CongCons (prover y y≠x),
              ((∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ {x=Head xs xs≠【】} {xs=Tail xs xs≠【】})
                \=> cong S otherer
                \=> (plusSuccRightSucc _ _)
                \=> cong2 (+) (ConsKeepsRest x≠HeadXs) (sym $ ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ {x=Head xs xs≠【】}))
            ))

-- interface Unit a where
--   Singleton: a
--   Universal: forall b . (0 f: b -> a) -> (0 x: b) -> f x = Singleton

-- ||| Any subset of a container type that preserves Nil is a container
-- Container a c => (Unit (p (Nil {c}))) =>  Container a (Subset c p) where

--     x .#. (Element xs _) = x .#. xs

--     Nil = Element Nil Singleton

--     IsNil (Element xs pxs) = case IsNil xs of
--       Yes Refl => Yes (case (Universal {a=p (Nil {c})} {b=p (Nil {c})} id pxs) of
--           Refl => Refl
--         )
        
--       No xs≠【】 => No (\Refl => xs≠【】 Refl)

--     ∀x‥x⋕【】≐0 = ∀x‥x⋕【】≐0 {c}

--     x :: Element xs pxs = Element (x :: xs) ?h5

--     Cons = ?h6

--     ConsBisurjective = ?h7

--     (++) = ?h8

--     ConcAddsCounts = ?h9
    
--     ContainerSized = ?h10

--     ⋕⎨【】⎬≐0 = ?h11

--     ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ = ?h12

--     ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】 = ?h13


-- snot : Not (x=x') -> Not (x'=x)
-- snot f Refl = f Refl

-- export
-- 0 ConsBiinjectiveWhenSingleton : Container a c => {x, y: a} -> {xs: c} -> DecEq a => (x :: xs = [y]) -> (x=y, xs=(Nil {c}))
-- ConsBiinjectiveWhenSingleton x∷xs≐【y】 with (decEq x y)
--   ConsBiinjectiveWhenSingleton x∷xs≐【x】 | Yes Refl = (Refl, (NilIsUnique x'_not_in_xs)) where
--     x'_not_in_xs : forall x'. x' .#. xs = 0
--     x'_not_in_xs with (decEq x x')
--       x'_not_in_xs | Yes Refl = injective (ConsAddsOne {x} {xs} \=> cong (x .#.) x∷xs≐【x】 \=> sym (ConsAddsOne {x} {xs=(Nil {c})})) \=> ∀x‥x⋕【】≐0 
--       x'_not_in_xs | No x≠x' = ConsKeepsRest {x} {xs} (snot x≠x') \=> cong (x' .#.) x∷xs≐【x】 \=> sym (ConsKeepsRest {x} {xs=(Nil {c})} (snot x≠x')) \=> ∀x‥x⋕【】≐0
--   ConsBiinjectiveWhenSingleton x∷xs≐【y】 | No x≠y = void $ SIsNotZ (ConsAddsOne \=> cong (x .#.) x∷xs≐【y】\=> sym (ConsKeepsRest x≠y) \=> ∀x‥x⋕【】≐0)


-- export
-- 0 MatchBiinjectiveWhenSingleton : Container a c => Sequence a c => {y: a} -> DecEq a => forall prf【y】≠【】. (Iterate {c} [y] prf【y】≠【】).fst = (y, Nil)
-- MatchBiinjectiveWhenSingleton with (Iter {c} [y])
--   MatchBiinjectiveWhenSingleton | (Left let【y】≐【】) = void $ SIsNotZ $ ConsAddsOne \=> cong (y .#.) let【y】≐【】 \=> ∀x‥x⋕【】≐0
--   MatchBiinjectiveWhenSingleton | (Right (Element (x, xs) x∷xs≐【y】)) with (ConsBiinjectiveWhenSingleton x∷xs≐【y】)
--     MatchBiinjectiveWhenSingleton | (Right (Element (x, _) Refl)) | (Refl, Refl) = Evidence Refl Refl

||| Decidable.Equality.Core.decEqSelfIsYes
export
yes : DecEq a => (x: a) -> decEq x x = Yes Refl
yes x with (decEq x x)
  yes x | (Yes Refl) = Refl
  yes x | (No xNEqX) = void $ xNEqX Refl

||| Decidable.Equality.Core.decEqContraIsNo
export
no : DecEq a => {x, x': a} -> (x≠x': Not (x=x')) -> Subset (Not (x=x')) (\ctra => decEq x x' = No {prop=(x=x')} ctra)
no x≠x' with (decEq x x')
  no x'NEqX' | (Yes Refl) = void $ x'NEqX' Refl
  no _ | (No x≠x') = Element x≠x' Refl

-- export
-- 0 Next : {x: a} -> {xs: c} -> Container a c => {n: Nat} -> x .#. xs = n -> x .#. (Container.(::) x xs) = 1+n
-- Next prf = sym ConsAddsOne \=> (cong S prf)

-- export
-- 0 conLeftCons : Container a c => (x: a) -> {0 xs, ys, zs: c} -> xs ++ ys = zs -> (x::xs) ++ ys = x::zs
-- conLeftCons x prf = ConcReduces \=> (cong (x::) prf)

-- export
-- 0 findFirst : DecEq a => Container a c => (x: a) -> (xs: c) -> Either (x .#. xs = 0) (Subset (c, c) (\(l, r) => (x .#. l = 0, l ++ x::r = xs)))
-- findFirst x xs with (sizeAccessible @{ContainerSized} xs)
--   findFirst x xxs | acc with (Iter xxs)
--     findFirst x _ | acc | (Left Refl) = Left (∀x‥x⋕【】≐0)
--     findFirst x _ | acc | (Right (Element (x', xs) Refl)) with (decEq x x')
--       findFirst x _ | acc | (Right (Element (_, xs) Refl)) | (Yes Refl) = Right (Element (Nil, xs) (∀x‥x⋕【】≐0, ConcNilLeftNeutral))
--       findFirst x _ | Access acc | (Right (Element (x', xs) Refl)) | (No x≠x') =
--         case (findFirst x xs | acc _ (replace {p = LTE (S (size @{ContainerSized} xs))} (sym $ SizedCons) reflexive)) of
--           (Left x∉xs) => Left ((sym $ ConsKeepsRest x≠x') \=> x∉xs)
--           (Right (Element (l, r) (x∉l, Refl))) =>
--             Right (Element (x'::l, r) ((sym $ ConsKeepsRest x≠x') \=> x∉l, ConcReduces))
