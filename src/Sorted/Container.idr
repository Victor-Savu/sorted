module Sorted.Container

import public Control.Relation
import public Control.WellFounded
import Data.Void
import Data.Nat
import Data.Vect
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
%hide Prelude.Stream.(::)
%hide Prelude.Nil


export
ford : (0 _: a = b) -> a -> b
ford Refl = id

public export
record Biexists {0 first_type : Type} {0 second_type: Type} this where
  constructor Bievidence
  first : first_type
  second : second_type
  0 biexists : this first second

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
    IsNil: (xs: c) -> Dec (xs = [])
    ||| No element occurs in the empty container
    ∀x‥x⋕【】≐0 : {x: a} -> x .#. [] = 0

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
    ||| If a container is not empty, then there exists at least one way of obtaining it through cons-ing an element to some container
    ConsBisurjective: {x∷xs: c} -> Not (x∷xs=[]) -> Biexists (\x => \xs => x :: xs = x∷xs)

    ||| Concatenation
    (++) : (xs: c) -> (ys: c) -> c
    ||| An element occurs in the concatenation of two containers the total number of times it occurs in each container
    ConcAddsCounts : {x: a} -> {xs, ys: c} -> x .#. (xs ++ ys) = x .#. xs + x .#. ys
    
    ||| Containers are sized
    ContainerSized : Sized c
    ||| For the implementation of size, the size of te empty container is 0
    ⋕⎨【】⎬≐0: size @{ContainerSized} [] = 0
    ||| Cons-ing an element to a container increases the size by exactly 1
    ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬: {x: a} -> {xs: c} -> size @{ContainerSized} (x::xs) = S (size @{ContainerSized} xs)
    ||| Only the empty container has size 0
    ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】: {xs: c} -> (size @{ContainerSized} xs = 0) -> xs = []

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
NilIsUnique : Container a c => {xs: c} -> ((x: a) -> (x .#. xs) {c} = 0) -> xs = []
NilIsUnique x∉xs with (IsNil xs)
  NilIsUnique x∉xs | (Yes Refl) = Refl
  NilIsUnique x∉xs | (No xs≠【】) with (ConsBisurjective xs≠【】)
    NilIsUnique x∉xs | (No xs≠【】) | (Bievidence x' xs' x'∷xs'≐xs) =
      rewrite sym x'∷xs'≐xs in
        void $ SIsNotZ (ConsAddsOne {c} {xs=xs'} \=> cong (x' .#.) x'∷xs'≐xs \=> x∉xs _)


export
[uninhabitedConsIsNil] {x: a} -> {xs: c} -> Container a c => Uninhabited (x::xs = ([] {c})) where
    uninhabited x∷xs≐【】 = absurdity $ ConsAddsOne \=> (cong (x .#.) x∷xs≐【】) \=>  (∀x‥x⋕【】≐0)

export
[DecEqElement] Container a c => DecEq a where
  decEq x y with (Cons {x=y} {x'=x} {xs=([] {c})})
    decEq _ y | (Left (Refl, _)) = Yes Refl
    decEq x y | (Right (x≠y, _)) = No x≠y

||| There is only one way to write a container of one element as the cons of an element with a container:
|||  the element cons'd with the nil container
export
ThereCanOnlyBeOne : Container a c => (x: a) -> (know【x】≠【】: Not ([x]=[] {c})) -> let cbs = ConsBisurjective know【x】≠【】 in (cbs.first = x, cbs.second = [])
ThereCanOnlyBeOne x know【x】≠【】 with (ConsBisurjective know【x】≠【】)
  ThereCanOnlyBeOne x know【x】≠【】 | (Bievidence y ys y∷ys≐【x】) with (Cons {x=y} {x'=x} {xs=ys})
    ThereCanOnlyBeOne x know【x】≠【】 | (Bievidence _ ys y∷ys≐【x】) | (Left (Refl, ysz)) = (Refl, NilIsUnique noElementsInYs) where
      noElementsInYs : (p : a) -> p .#. ys = 0
      noElementsInYs p with (decEq @{DecEqElement {c}} x p)
        noElementsInYs _ | (Yes Refl) = injective (ysz \=> cong (x .#.) y∷ys≐【x】 \=> sym (ConsAddsOne {x=x} {xs = ([] {c})})) \=> ∀x‥x⋕【】≐0
        noElementsInYs p | (No x≠p) = ?NilIsUnique_arg_0_rhs_rhss_1
    ThereCanOnlyBeOne x know【x】≠【】 | (Bievidence y ys y∷ys≐【x】) | (Right (x≠y, x⋕ys≐x⋕❪y∷ys❫)) =
      let
        x⋕ys≐x⋕【x】 = x⋕ys≐x⋕❪y∷ys❫ \=> cong (x .#. ) y∷ys≐【x】
        x⋕ys≐1 = x⋕ys≐x⋕【x】 \=> sym ConsAddsOne \=> cong S ∀x‥x⋕【】≐0
        ⋕⎨y∷ys⎬≐⋕⎨【x】⎬ = cong (size @{ContainerSized}) y∷ys≐【x】
        S⋕⎨ys⎬≐⋕⎨【x】⎬ = sym ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=> ⋕⎨y∷ys⎬≐⋕⎨【x】⎬ 
        ⋕⎨【x】⎬≐1 = ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ {x} {c} \=> cong S ⋕⎨【】⎬≐0
        S⋕⎨ys⎬≐1 = S⋕⎨ys⎬≐⋕⎨【x】⎬ \=> ⋕⎨【x】⎬≐1 
        ⋕⎨ys⎬≐0 = injective S⋕⎨ys⎬≐1
        ys≐【】 = ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】 ⋕⎨ys⎬≐0
        x⋕ys≐0 = cong (x .#.) ys≐【】 \=> ∀x‥x⋕【】≐0
        ‥1≐0 = sym x⋕ys≐1 \=> x⋕ys≐0
      in absurdity ‥1≐0




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
    Remove x _ | acc | (Yes Refl) = Element [] (∀x‥x⋕【】≐0, \_ => \_ => Refl, cong (+ size @{ContainerSized} ([] {c})) (sym ∀x‥x⋕【】≐0 ))
    Remove x xs | acc | (No xs≠【】) with (ConsBisurjective xs≠【】)
      Remove x xs | Access acc | No _ | (Bievidence y ys y∷ys≐xs) =
        let
          Element ys⧷⎨x⎬ prf = (Remove x ys | acc _ $ eqLTE $ sym $ rewrite sym y∷ys≐xs in ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ {x=y})
          0 x∉ys⧷⎨x⎬ = fst prf
          0 prf = snd prf
          0 prover = fst prf
          0 otherer = snd prf
        in case decEq @{DecEqElement {a} {c}} x y of
          Yes Refl => Element ys⧷⎨x⎬ (rewrite sym y∷ys≐xs in (
            x∉ys⧷⎨x⎬,
            \z => \z≠y => (sym (ConsKeepsRest z≠y) \=> prover z z≠y),
            ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=> cong S otherer \=> cong (+ size @{ContainerSized} ys⧷⎨x⎬) ConsAddsOne
            ))
          No x≠y => Element (y::ys⧷⎨x⎬) (rewrite sym y∷ys≐xs in (
            sym (ConsKeepsRest x≠y) \=> x∉ys⧷⎨x⎬,
            \z => \z≠x => CongCons (prover z z≠x),
            ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=> cong S otherer \=> (plusSuccRightSucc _ _) \=> cong2 (+) (ConsKeepsRest x≠y) (sym ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬)
            ))

export
interface Container a c => Sequence a c | c where
    ||| Given a container (xss) that is not empty,
    ||| return an element from that container (x) and the container without the element (xs).
    |||
    ||| Post-conditions:
    ||| - There is one fewer x in xs than there were in xss
    ||| - Any other x' (that is not x) occurs just as many times in xs as in xss
    Next : (xss: c) -> {auto 0 xss≠【】: Not (xss = [])} ->
        (
            Subset (a, c) (
                    \(x, xs) => (
                            x .#. xss = S (x .#. xs),
                            (x': _) -> (Not (x'=x)) -> x' .#. xs = x' .#. xss
                        )
                )
        )
    NextIndifferent: (xss: c) -> (p0: Not (xss = [])) -> (p1: Not (xss = [])) -> (Next xss {xss≠【】=p0}).fst = (Next xss {xss≠【】=p1}).fst

0 ContainerEq: Container a c => c -> c -> Type
ContainerEq xs ys = (x: a) -> x .#. xs = x .#. ys

export
0 ConcNilLeftNeutral : {0 xs: c} -> Container a c => ContainerEq ([] ++ xs) xs
ConcNilLeftNeutral {xs} = \x => ConcAddsCounts \=> cong (+ x .#. xs) ∀x‥x⋕【】≐0

export
0 ConcNilRightNeutral : {0 xs: c} -> Container a c => ContainerEq (xs ++ []) xs
ConcNilRightNeutral = \x => ConcAddsCounts \=> cong (x .#. xs +) ∀x‥x⋕【】≐0 \=> plusZeroRightNeutral _

0 EqualContainersHaveSameSize': Container a c => {xs, ys: c} -> SizeAccessible @{ContainerSized} xs -> ContainerEq xs ys -> size @{ContainerSized} xs = size @{ContainerSized} ys
EqualContainersHaveSameSize' (Access acc) xs≐ys = case (IsNil xs) of
  (Yes Refl) => cong (size @{ContainerSized}) (sym $ NilIsUnique (\x => sym (xs≐ys x) \=> ∀x‥x⋕【】≐0))
  (No xs≠【】) => case (ConsBisurjective xs≠【】) of
    (Bievidence x xs' x∷xs'≐xs) => case (Remove x xs, Remove x ys) of
      (Element xs'' (x∉xs'', xcdsa, o‥⋕⎨xs⎬≐x⋵xs∔⋕⎨xs''⎬), Element ys'' (x∉ys'', ycdsa, o‥⋕⎨ys⎬≐x⋵ys∔⋕⎨ys''⎬)) =>
        let
          xs''≐ys'': (x'': a) -> (x'' .#. xs'' = x'' .#. ys'')
          xs''≐ys'' x'' = case (decEq @{DecEqElement {a} {c}} x'' x) of
            (Yes Refl) => x∉xs'' \=> sym x∉ys''
            (No x''≠x) =>
              let
                x''⋵xs≐x''⋵xs'' = xcdsa x'' x''≠x
                x''⋵ys≐x''⋵ys'' = ycdsa x'' x''≠x
              in
                sym x''⋵xs≐x''⋵xs'' \=> xs≐ys x'' \=> x''⋵ys≐x''⋵ys''
          
          ⒈∔⋕⎨xs''⎬≤⋕⎨xs⎬ : LTE (S (size @{ContainerSized} xs'')) (size @{ContainerSized} xs)
          ⒈∔⋕⎨xs''⎬≤⋕⎨xs⎬ =
            let
              x⋵x∷xs'≐x⋵xs = cong (x .#.) x∷xs'≐xs
              ⒈∔x⋵xs'≐x⋵xs = ConsAddsOne \=> x⋵x∷xs'≐x⋵xs
              ⒈∔x⋵xs'∔⋕⎨xs''⎬≐x⋵xs∔⋕⎨xs''⎬ = cong (+ size @{ContainerSized} xs'') ⒈∔x⋵xs'≐x⋵xs
              ⒈∔x⋵xs'∔⋕⎨xs''⎬≐⋕⎨xs⎬ = ⒈∔x⋵xs'∔⋕⎨xs''⎬≐x⋵xs∔⋕⎨xs''⎬ \=> sym o‥⋕⎨xs⎬≐x⋵xs∔⋕⎨xs''⎬

              ⋕⎨xs''⎬≤⋕⎨xs''⎬∔x⋵xs': (LTE (size @{ContainerSized} xs'') (plus (size @{ContainerSized} xs'') (x .#. xs')))
              ⋕⎨xs''⎬≤⋕⎨xs''⎬∔x⋵xs' = lteAddRight (size @{ContainerSized} xs'') {m=x .#. xs'}

              ⋕⎨xs''⎬≤x⋵xs'∔⋕⎨xs''⎬≐⋕⎨xs''⎬≤⋕⎨xs''⎬∔x⋵xs': ((LTE (size @{ContainerSized} xs'') (plus (x .#. xs') (size @{ContainerSized} xs''))) = (LTE (size @{ContainerSized} xs'') (plus (size @{ContainerSized} xs'') (x .#. xs'))))
              ⋕⎨xs''⎬≤x⋵xs'∔⋕⎨xs''⎬≐⋕⎨xs''⎬≤⋕⎨xs''⎬∔x⋵xs' = cong (LTE (size @{ContainerSized} xs'')) $ plusCommutative (x .#. xs') (size @{ContainerSized} xs'')

              ⋕⎨xs''⎬≤x⋵xs'∔⋕⎨xs''⎬: (LTE (size @{ContainerSized} xs'') (plus (x .#. xs') (size @{ContainerSized} xs'')))
              ⋕⎨xs''⎬≤x⋵xs'∔⋕⎨xs''⎬ = rewrite ⋕⎨xs''⎬≤x⋵xs'∔⋕⎨xs''⎬≐⋕⎨xs''⎬≤⋕⎨xs''⎬∔x⋵xs' in ⋕⎨xs''⎬≤⋕⎨xs''⎬∔x⋵xs'

              ⒈∔⋕⎨xs''⎬≤⒈∔x⋵xs'∔⋕⎨xs''⎬ : LTE (S (size @{ContainerSized} xs'')) (S ((x .#. xs') + (size @{ContainerSized} xs'')))
              ⒈∔⋕⎨xs''⎬≤⒈∔x⋵xs'∔⋕⎨xs''⎬ = LTESucc ⋕⎨xs''⎬≤x⋵xs'∔⋕⎨xs''⎬
            in
              rewrite sym ⒈∔x⋵xs'∔⋕⎨xs''⎬≐⋕⎨xs⎬ in ⒈∔⋕⎨xs''⎬≤⒈∔x⋵xs'∔⋕⎨xs''⎬

          ⋕⎨xs''⎬≐⋕⎨ys''⎬: size @{ContainerSized} xs'' = size @{ContainerSized} ys''
          ⋕⎨xs''⎬≐⋕⎨ys''⎬ = EqualContainersHaveSameSize' (acc xs'' ⒈∔⋕⎨xs''⎬≤⋕⎨xs⎬) xs''≐ys''

        in o‥⋕⎨xs⎬≐x⋵xs∔⋕⎨xs''⎬ \=> cong2 (+) (xs≐ys x) ⋕⎨xs''⎬≐⋕⎨ys''⎬ \=> sym o‥⋕⎨ys⎬≐x⋵ys∔⋕⎨ys''⎬

0 EqualContainersHaveSameSize: Container a c => {xs, ys: c} -> ContainerEq xs ys -> size @{ContainerSized} xs = size @{ContainerSized} ys
EqualContainersHaveSameSize {xs} {ys} = EqualContainersHaveSameSize' {xs} {ys} (sizeAccessible @{ContainerSized} xs) where

0 ConcAddsSizes' : Container a c => {xs, ys: c} -> SizeAccessible @{ContainerSized} xs -> size @{ContainerSized} (xs ++ ys) = size @{ContainerSized} xs + size @{ContainerSized} ys
ConcAddsSizes' (Access acc) = case (IsNil xs) of
  (Yes Refl) =>
      EqualContainersHaveSameSize ConcNilLeftNeutral \=> cong (+ size @{ContainerSized} ys) (sym ⋕⎨【】⎬≐0)
  (No xs≠【】) => case (ConsBisurjective xs≠【】) of
    (Bievidence x xs' x∷xs'≐xs) =>
        let
          o‥⋕⎨xs'⧺ys'⎬≐⋕⎨xs'⎬∔⋕⎨ys⎬ = ConcAddsSizes' (acc ?alp ?malp) {xs=xs'} {ys}
        in
          ?help_1_rhs1_2

export
0 ConcAddsSizes : Container a c => {xs, ys: c} -> size @{ContainerSized} (xs ++ ys) = size @{ContainerSized} xs + size @{ContainerSized} ys
ConcAddsSizes = ConcAddsSizes' (sizeAccessible @{ContainerSized} xs) 

-- snot : Not (x=x') -> Not (x'=x)
-- snot f Refl = f Refl

-- export
-- 0 ConsBiinjectiveWhenSingleton : Container a c => {x, y: a} -> {xs: c} -> DecEq a => (x :: xs = [y]) -> (x=y, xs=([] {c}))
-- ConsBiinjectiveWhenSingleton x∷xs≐【y】 with (decEq x y)
--   ConsBiinjectiveWhenSingleton x∷xs≐【x】 | Yes Refl = (Refl, (NilIsUnique x'_not_in_xs)) where
--     x'_not_in_xs : forall x'. x' .#. xs = 0
--     x'_not_in_xs with (decEq x x')
--       x'_not_in_xs | Yes Refl = injective (ConsAddsOne {x} {xs} \=> cong (x .#.) x∷xs≐【x】 \=> sym (ConsAddsOne {x} {xs=([] {c})})) \=> ∀x‥x⋕【】≐0 
--       x'_not_in_xs | No x≠x' = ConsKeepsRest {x} {xs} (snot x≠x') \=> cong (x' .#.) x∷xs≐【x】 \=> sym (ConsKeepsRest {x} {xs=([] {c})} (snot x≠x')) \=> ∀x‥x⋕【】≐0
--   ConsBiinjectiveWhenSingleton x∷xs≐【y】 | No x≠y = void $ SIsNotZ (ConsAddsOne \=> cong (x .#.) x∷xs≐【y】\=> sym (ConsKeepsRest x≠y) \=> ∀x‥x⋕【】≐0)


-- export
-- 0 MatchBiinjectiveWhenSingleton : Container a c => Sequence a c => {y: a} -> DecEq a => forall prf【y】≠【】. (Iterate {c} [y] prf【y】≠【】).fst = (y, [])
-- MatchBiinjectiveWhenSingleton with (Iter {c} [y])
--   MatchBiinjectiveWhenSingleton | (Left let【y】≐【】) = void $ SIsNotZ $ ConsAddsOne \=> cong (y .#.) let【y】≐【】 \=> ∀x‥x⋕【】≐0
--   MatchBiinjectiveWhenSingleton | (Right (Element (x, xs) x∷xs≐【y】)) with (ConsBiinjectiveWhenSingleton x∷xs≐【y】)
--     MatchBiinjectiveWhenSingleton | (Right (Element (x, _) Refl)) | (Refl, Refl) = Evidence Refl Refl

export
yes : DecEq a => (x: a) -> decEq x x = Yes Refl
yes x with (decEq x x)
  yes x | (Yes Refl) = Refl
  yes x | (No xNEqX) = void $ xNEqX Refl

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
--       findFirst x _ | acc | (Right (Element (_, xs) Refl)) | (Yes Refl) = Right (Element ([], xs) (∀x‥x⋕【】≐0, ConcNilLeftNeutral))
--       findFirst x _ | Access acc | (Right (Element (x', xs) Refl)) | (No x≠x') =
--         case (findFirst x xs | acc _ (replace {p = LTE (S (size @{ContainerSized} xs))} (sym $ SizedCons) reflexive)) of
--           (Left x∉xs) => Left ((sym $ ConsKeepsRest x≠x') \=> x∉xs)
--           (Right (Element (l, r) (x∉l, Refl))) =>
--             Right (Element (x'::l, r) ((sym $ ConsKeepsRest x≠x') \=> x∉l, ConcReduces))
