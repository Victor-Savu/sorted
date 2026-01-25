module Sorted.IsPermutationOf

import public Control.Relation
import Control.WellFounded
import Data.Nat
import Data.Void
import Decidable.Equality

import public Sorted.Container

%default total


export infixr 4 ~@~

%hide Prelude.(::)
%hide Prelude.Stream.(::)
%hide Prelude.Nil

namespace IsPermutationOf
  public export
  data IsPermutationOf: Container a c => Rel c where
    Ipo : ((e :a) -> ((e .#. original) @{ct} = (e .#. permutation) @{ct})) -> IsPermutationOf @{ct} original permutation

public export
(~@~) : Container a c => Rel c
original ~@~ permutation = IsPermutationOf original permutation

export
[uninhabitedIsPermutationOfConsNil] {0 x: a} -> {0 xs: c} -> Container a c => Uninhabited (x::xs ~@~ []) where
    uninhabited (Ipo occ) = void $ SIsNotZ (ConsAddsOne \=> occ x \=> ∀x‥x⋕【】≐0)

export
[uninhabitedIsPermutationOfNilCons] {0 x: a} -> {0 xs: c} -> Container a c => Uninhabited ([] ~@~ x::xs) where
    uninhabited (Ipo occ) = uninhabited @{uninhabitedIsPermutationOfConsNil {a} {c}} (Ipo $ \e => sym $ occ e)

export
[reflexiveIsPermutationOf] Container a c => Reflexive c (~@~) where
    reflexive = Ipo (\_ => Refl)

export
[transitiveIsPermutationOf]
Container a c => Transitive c (~@~) where
    transitive (Ipo occ) (Ipo occ') = Ipo (\e => (occ e) \=> (occ' e))

export
[symmetricIsPermutationOf]
Container a c => Symmetric c (~@~) where
  symmetric (Ipo occ) = Ipo (\eInY => sym $ occ eInY)

export
PermutationOfCons : {x: a} -> {xs, ys: c} -> Container a c => x::xs ~@~ x::ys -> xs ~@~ ys
PermutationOfCons (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. xs = e .#. ys
    occ' e with (decEq @{DecEqElement {c}} e x)
      occ' _ | (Yes Refl) = injective $ (ConsAddsOne \=> occ x) \=> (sym $ ConsAddsOne)
      occ' e | (No e≠x) = (ConsKeepsRest e≠x \=> occ e) \=> (sym $ ConsKeepsRest e≠x)

export
AdditionOfPermutationsCommutes : {xs, ys, p: c} -> Container a c => p ~@~ (xs++ys) -> p ~@~ (ys++xs)
AdditionOfPermutationsCommutes (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. p = e .#. (ys ++ xs)
    occ' e = occ e \=> ConcAddsCounts \=> plusCommutative _ _ \=> sym (ConcAddsCounts)

export
(++) : {x, y, z, t: c} -> Container a c => x ~@~ y -> z ~@~ t -> (x++z) ~@~ (y++t)
(++) (Ipo occ_x_y) (Ipo occ_z_t) = Ipo occ_xz_yt where
    occ_xz_yt : (e : a) -> e .#. (x ++ z) = e .#. (y ++ t)


-- namespace Permutation
--   export
--   PNil : Container a c => IsPermutationOf {c} [] []
--   PNil = Ipo (\_ => Refl)

--   export
--   (::) : {xs, ys: c} -> (x: a) -> Container a c => xs ~@~ ys -> x::xs ~@~ x::ys
--   (::) x (Ipo occ) = Ipo occ' where
--       occ': (e : a) -> e .#. (x :: xs) = e .#. (x :: ys)
--       occ' e with (decEq @{DecEqElement {c}} e x)
--         occ' _ | (Yes Refl) = (sym ConsAddsOne \=> cong S (occ x)) \=> ConsAddsOne
--         occ' e | (No e≠x) = (sym (ConsKeepsRest e≠x) \=> occ e) \=> ConsKeepsRest e≠x

export
PermutationOfNilIsNil : Container a c => {xs: c} -> IsPermutationOf [] xs -> xs = []
PermutationOfNilIsNil (Ipo occ) = NilIsUnique (\x => sym (occ x) \=> ∀x‥x⋕【】≐0)

export
tail : {x: a} -> {xs, ys: c} -> Container a c => x::xs ~@~ x::ys -> xs ~@~ ys
tail (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. xs = e .#. ys
    occ' e with (decEq @{DecEqElement {c}} e x)
      occ' _ | (Yes Refl) = injective $ (ConsAddsOne \=> occ x) \=> sym ConsAddsOne
      occ' e | (No e≠x) = (ConsKeepsRest e≠x \=> occ e) \=> (sym $ ConsKeepsRest e≠x)

-- export
-- pong : Container a c => {0 p: c -> c} -> (f: xs ~@~ ys -> p xs ~@~ p ys) ->  xs ~@~ ys -> p xs ~@~ p ys
-- pong f g = f g

export
swapIsPermutation : {x,y: a} -> Container a c => (e: a) -> e .#. ([x, y] {c}) = e .#. ([y, x] {c})
swapIsPermutation e with (decEq @{DecEqElement {c}} e x, decEq @{DecEqElement {c}} e y)
  swapIsPermutation e | ((Yes Refl), Yes Refl) = Refl
  swapIsPermutation e | ((Yes Refl), No e≠y) = sym ((cong S $ ConsKeepsRest e≠y) \=> ConsAddsOne) \=> ConsAddsOne \=> (ConsKeepsRest e≠y)
  swapIsPermutation e | ((No e≠x), Yes Refl) = sym (ConsKeepsRest e≠x) \=> sym ConsAddsOne \=> (cong S (ConsKeepsRest e≠x)) \=> ConsAddsOne
  swapIsPermutation e | ((No e≠x), No e≠y) = sym (ConsKeepsRest e≠y \=> ConsKeepsRest e≠x) \=> ConsKeepsRest e≠x \=> ConsKeepsRest e≠y

export
shiftPermutation : {y: a} -> {xs, ys, ys': c} -> Container a c => IsPermutationOf {c} {a} ys (y::ys') -> IsPermutationOf {c} {a} (xs++ys) (y::(xs++ys'))
shiftPermutation (Ipo occ) = Ipo occ' where
  occ' : (e : a) -> e .#. (xs ++ ys) = e .#. (y :: (xs ++ ys'))
  occ' e with (decEq @{DecEqElement {c}} e y)
    occ' _ | (Yes Refl) = ConcAddsCounts \=> cong (y .#. xs +) (occ y \=> sym (ConsAddsOne {c})) \=> sym (plusSuccRightSucc _ _) \=> cong S (sym ConcAddsCounts)  \=> ConsAddsOne {c}
    occ' e | (No e≠y) = ConcAddsCounts \=> cong (e .#. xs +) (occ e \=> sym (ConsKeepsRest e≠y)) \=> sym ConcAddsCounts \=> ConsKeepsRest e≠y

-- RemoveEqInjective : Container a c => {xs, ys: c} -> IsPermutationOf xs ys -> {x: a} -> IsPermutationOf (let Element xs⧷⎨x⎬ xs⧷⎨x⎬_prf = Remove x xs in xs⧷⎨x⎬) (let Element ys⧷⎨x⎬ ys⧷⎨x⎬_prf = Remove x ys in ys⧷⎨x⎬)
-- RemoveEqInjective xs≎ys {x} with (Remove x xs, Remove x ys)
--   RemoveEqInjective xs≎ys {x = x} | (Element xs⧷⎨x⎬ xs⧷⎨x⎬_prf, Element ys⧷⎨x⎬ ys⧷⎨x⎬_prf) = Ipo occ where
--     occ: (e : a) -> e .#. xs⧷⎨x⎬ = e .#. ys⧷⎨x⎬

lteAdd : (p: Nat) -> LTE m n -> LTE (m+p) (n+p)
lteAdd 0 m≤n = rewrite (plusZeroRightNeutral m) in rewrite (plusZeroRightNeutral n) in m≤n
lteAdd (S k) m≤n =
  let
    succ❪m❫≤succ❪n❫ = LTESucc m≤n
    succ❪m⨢k❫≤succ❪n⨢k❫ = lteAdd k succ❪m❫≤succ❪n❫
  in
    rewrite sym (plusSuccRightSucc n k) in
    rewrite sym (plusSuccRightSucc m k) in 
      succ❪m⨢k❫≤succ❪n⨢k❫

export
0 PermutationHasSameSize : Container a c => {xs, ys: c} -> xs ~@~ ys -> size @{ContainerSized} xs = size @{ContainerSized} ys
PermutationHasSameSize xs≎ys with (sizeAccessible @{ContainerSized} ys)
  PermutationHasSameSize xs≎ys | acc with (IsNil ys)
    PermutationHasSameSize xs≎ys | acc | (Yes Refl) with (PermutationOfNilIsNil (symmetric @{symmetricIsPermutationOf} xs≎ys))
      PermutationHasSameSize xs≎ys | acc | (Yes Refl) | Refl = Refl
    PermutationHasSameSize (Ipo xs≎ys) | Access acc | (No ys≠【】) =
        let
          Element xs⧷⎨y⎬ (y∉❪xs⧷⎨y⎬❫, e→e≠y→e⋕xs⋕≐e❪xs⧷⎨y⎬❫, size❪xs❫≐❪y⋕xs❫∔size❪xs⧷⎨y⎬❫) = Remove (Head ys ys≠【】) xs
          Element ys⧷⎨y⎬ (y∉❪ys⧷⎨y⎬❫, e→e≠y→e⋕ys⋕≐e❪ys⧷⎨y⎬❫, size❪ys❫≐❪y⋕ys❫∔size❪ys⧷⎨y⎬❫) = Remove (Head ys ys≠【】) ys
          xs⧷⎨y⎬≎ys⧷⎨y⎬ : xs⧷⎨y⎬ ~@~ ys⧷⎨y⎬ =
            Ipo (\e => case decEq @{DecEqElement {c}} e (Head ys ys≠【】) of
                          (Yes Refl) => y∉❪xs⧷⎨y⎬❫ \=> sym y∉❪ys⧷⎨y⎬❫
                          (No e≠y) => sym (e→e≠y→e⋕xs⋕≐e❪xs⧷⎨y⎬❫ e e≠y) \=> xs≎ys e \=> e→e≠y→e⋕ys⋕≐e❪ys⧷⎨y⎬❫ e e≠y)
          s0≤y⋕ys : LTE 1 ((Head ys ys≠【】) .#. ys) =
            rewrite sym (cong ((Head ys ys≠【】) .#. ) (HeadTail ys ys≠【】)) in
            rewrite sym (ConsAddsOne {x=Head ys ys≠【】} {xs=Tail ys ys≠【】}) in
              LTESucc LTEZero
          succ❪size❪ys⧷⎨y⎬❫≤y⋕ys∔size❪ys⧷⎨y⎬❫ = lteAdd (size @{ContainerSized} ys⧷⎨y⎬) s0≤y⋕ys
          succ❪size❪ys⧷⎨y⎬❫≤size❪ys⧷⎨y⎬❫ =
            rewrite cong (LTE (S (size @{ContainerSized} ys⧷⎨y⎬))) (size❪ys❫≐❪y⋕ys❫∔size❪ys⧷⎨y⎬❫ ) in
              succ❪size❪ys⧷⎨y⎬❫≤y⋕ys∔size❪ys⧷⎨y⎬❫
          size❪xs⧷⎨y⎬❫≐size❪ys⧷⎨y⎬❫ = (PermutationHasSameSize xs⧷⎨y⎬≎ys⧷⎨y⎬ | acc _ succ❪size❪ys⧷⎨y⎬❫≤size❪ys⧷⎨y⎬❫) 
        in
          size❪xs❫≐❪y⋕xs❫∔size❪xs⧷⎨y⎬❫ \=> cong2 (+) (xs≎ys (Head ys ys≠【】)) size❪xs⧷⎨y⎬❫≐size❪ys⧷⎨y⎬❫ \=> sym size❪ys❫≐❪y⋕ys❫∔size❪ys⧷⎨y⎬❫

export
0 ConcNilLeftNeutral : {0 xs: c} -> Container a c => ([] ++ xs) ~@~ xs
ConcNilLeftNeutral {xs} = Ipo (\x => ConcAddsCounts \=> cong (+ x .#. xs) ∀x‥x⋕【】≐0)

export
0 ConcNilRightNeutral : {0 xs: c} -> Container a c => (xs ++ []) ~@~ xs
ConcNilRightNeutral = Ipo (\x => ConcAddsCounts \=> cong (x .#. xs +) ∀x‥x⋕【】≐0 \=> plusZeroRightNeutral _)

0 x∷xs⧺ys≐x∷⎨xs⧺ys⎬: {x: a} -> {xs, ys: c} -> Container a c => ((x::xs) ++ ys) ~@~ (x :: (xs ++ ys))
x∷xs⧺ys≐x∷⎨xs⧺ys⎬ = Ipo (\x' => ConcAddsCounts \=> case decEq @{DecEqElement {c}} x' x of
      Yes Refl => cong (+ (x .#. ys)) (sym (ConsAddsOne {c})) \=> cong S (sym (ConcAddsCounts {c})) \=> ConsAddsOne
      No x'≠x => cong (+ (x' .#. ys)) (sym (ConsKeepsRest x'≠x)) \=> sym (ConcAddsCounts {c}) \=> ConsKeepsRest x'≠x
  )

export
0 ConcAddsSizes' : Container a c => {xs, ys: c} -> SizeAccessible @{ContainerSized} xs -> size @{ContainerSized} (xs ++ ys) = size @{ContainerSized} xs + size @{ContainerSized} ys
ConcAddsSizes' (Access acc) = case (IsNil xs) of
  (Yes Refl) =>
      PermutationHasSameSize ConcNilLeftNeutral \=> cong (+ size @{ContainerSized} ys) (sym ⋕⎨【】⎬≐0)
  (No xs≠【】) => 
    let
      ⋕⎨xs⎬≐⒈∔⋕⎨xs'⎬: (size @{ContainerSized} xs = S (size @{ContainerSized} (Tail xs xs≠【】))) = cong (size @{ContainerSized {c}}) (sym $ HeadTail xs xs≠【】) \=> ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬
      ⒈∔⋕⎨xs'⎬∔⋕⎨ys⎬≐⋕⎨xs⎬∔⋕⎨ys⎬ = sym (cong (+ (size @{ContainerSized} ys)) ⋕⎨xs⎬≐⒈∔⋕⎨xs'⎬)

      ⋕⎨xs'⧺ys⎬≐⋕⎨xs'⎬∔⋕⎨ys⎬ = ConcAddsSizes' (acc _ (rewrite ⋕⎨xs⎬≐⒈∔⋕⎨xs'⎬ in reflexive)) {xs=Tail xs xs≠【】} {ys}
      ⋕⎨x∷xs'⧺ys⎬≐⋕⎨x∷⎨xs'⧺ys⎬⎬ = PermutationHasSameSize (x∷xs⧺ys≐x∷⎨xs⧺ys⎬ {xs=Tail xs xs≠【】} {ys} {x=Head xs xs≠【】})
    in
      cong (\arg => size @{ContainerSized} (arg ++ ys)) (sym $ HeadTail xs xs≠【】) \=> ⋕⎨x∷xs'⧺ys⎬≐⋕⎨x∷⎨xs'⧺ys⎬⎬ \=> ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=> cong S ⋕⎨xs'⧺ys⎬≐⋕⎨xs'⎬∔⋕⎨ys⎬ \=> ⒈∔⋕⎨xs'⎬∔⋕⎨ys⎬≐⋕⎨xs⎬∔⋕⎨ys⎬

export
0 ConcAddsSizes : Container a c => {xs, ys: c} -> size @{ContainerSized} (xs ++ ys) = size @{ContainerSized} xs + size @{ContainerSized} ys
ConcAddsSizes = ConcAddsSizes' (sizeAccessible @{ContainerSized} xs) 
