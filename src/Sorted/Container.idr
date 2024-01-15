module Sorted.Container

import public Control.Relation
import Control.WellFounded
import Data.Void
import Data.Nat
import Decidable.Equality

import public Sorted.Prop

infixr 9 .#.

%default total

%hide Prelude.(::)
%hide Prelude.Stream.(::)
%hide Prelude.Nil

||| A container is a type that
||| a. has an element representing the empty container
||| b. has a way to add an element to an existing container such that the resulting container contains exactly one more instance of that new element
|||    and just as many instances of any other element of the original container
|||
||| The container interface is satisfied by:
||| - the type a representing the type of elements in the container
||| - the type construtor c: Type -> Type which constructs the type of the container: c a
||| if it can:
||| 1. provide a counting function (.#.): a -> c a -> Nat which counts the number of occurrences of a value of type a in the container of type c a
||| 1. produce an "empty" container from thin air (using Nil). The empty container is a specific instance of c a (call it xs) which must satisfy the
|||    property that any value of type a occurs 0 times in xs according to the counting function. Basically, a container is empty if nothing occurs in it.
||| 2. produce an "inhabited" container by applying (::) to an element of type a (call it x) and another container of type c a (call it xs). The
|||    "inhabited" container is a specific instance of c a (call it xxs) which must satisfy two properties:
|||    1. As counted by (.#.), x occurs in xxs one time more than it occurs in xs (showing that x was inserted exactly once by (::))
|||    2. Given any other element of a (call it x'), that element will occur the same number of times in xs as it does in xxs (showing that no other
|||       element of xs was duplicated or removed by (::))
public export
interface Container a (0 c: Type -> Type) | c where
    constructor MkContainer

    (.#.) : a -> c a -> Nat

    Nil : c a
    0 NilIsEmpty : (x: a) -> x .#. [] = 0
    0 NilIsUnique : (xs: c a) -> ({m: Nat} -> (x': a) -> x' .#. xs = m -> m = 0) -> xs = []

    (::) : a -> c a -> c a
    0 ConsAddsOne : (x: a) -> (xs : c a) -> (1 + x .#. xs) = x .#. (x :: xs)
    0 ConsKeepsRest : (x: a) -> (xs : c a) -> (x': a) -> (ne: Not (x'=x)) -> x' .#. xs =  x' .#. (x::xs)
    0 ConsBiinjective : Biinjective (::)
    -- 0 ConsSize : Sized (c a) => (x : a) -> (xs: c a) -> LTE (S (size xs)) (size (x::xs))

    (++) : (xs: c a) -> (ys: c a) -> c a
    0 ConcNilLeftNeutral : (xs: c a) -> [] ++ xs = xs
    0 ConcReduces : (x: a) -> (xs, ys: c a) -> (x::xs) ++ ys = x :: (xs ++ ys)

    Match : (xs: c a) -> Either (xs = []) ((a, c a) # \q => (fst q)::(snd q) = xs)

export
[uninhabitedConsIsNil] {0 x: a} -> {0 xs: c a} -> Container a c => Uninhabited (x::xs = []) where
   uninhabited xXsIsNil = absurdity $ transitive (ConsAddsOne x xs) $ transitive (cong (x .#.) xXsIsNil) (NilIsEmpty x)

public export
data DominatedBottom = MkDominatedBottom

public export
data Dominated : Container a c => c a -> c a -> Type where
    Dom : (x: a) -> (xs, ys: c a) -> (dom: S ((x .#. xs) @{ct}) = (x .#. ys) @{ct}) -> (dom': (y: a) -> (y .#. xs) @{ct} `LTE` (y .#. ys) @{ct} ) -> Dominated @{ct} {c} ((x::xs) @{ct}) ((x::ys) @{ct})

public export
DominatedAccessible : Container a c => c a -> Type
DominatedAccessible = Accessible Dominated

pureDominatedAccessible : Container a c => (zs: c a) -> (zs = []) -> Accessible Dominated zs
pureDominatedAccessible zs zsEqNil = Access $ acc zs zsEqNil where
    acc : (zs: c a) -> (zs = []) -> (ys : c a) -> Dominated ys zs -> Accessible Dominated ys
    acc (y :: zs') pf (y :: ys') (Dom y ys' zs' dom dom') = absurdity @{uninhabitedConsIsNil} pf

public export
dominatesAccessible : Container a c => (ys: c a) -> DominatedAccessible ys
dominatesAccessible ys with (Match ys)
  dominatesAccessible _ | (Left Refl) = pureDominatedAccessible [] Refl
  dominatesAccessible ys | (Right ((y, ys') # yYs'EqYs)) = Access $ acc (y .#. ys) y ys' ys Refl yYs'EqYs where
    acc : (yInYs: Nat) -> (y: a) -> (ys', ys: c a) -> (0 yInYsPrf: y .#. ys = yInYs) -> (0 yYs'EqYs: y::ys' = ys) -> (xs : c a) -> Dominated xs ys -> Accessible Dominated xs
    acc 0 y ys' (x::ys'') yInYsPrf yYs'EqYs (x :: xs) (Dom x xs ys'' dom dom') = void $ SIsNotZ $ (((ConsAddsOne y ys') `transitive` (cong (y .#.) yYs'EqYs)) `transitive` yInYsPrf)
    acc (S k) y ys' (x::ys'') yInYsPrf yYs'EqYs (x :: xs) (Dom x xs ys'' dom dom') =  Access (\ws => \domWsXXs => let
            0 bimbim = biinjective @{ConsBiinjective} yYs'EqYs
            0 fuga = ((sym (ConsAddsOne x xs) `transitive` dom) `transitive` (cong (.#. ys'') $ sym (fst bimbim))) `transitive` (injective (ConsAddsOne y ys'' `transitive` ((cong (\q => y .#. (q :: ys'')) $ fst bimbim) `transitive` yInYsPrf)))
            chomasd = acc k x xs (x::xs) fuga Refl ws domWsXXs
        in chomasd)

public export
[containerSize] Container a c => Sized (c a) where
    size xs with (Match xs)
      size _ | (Left Refl) = 0
      size xxs | (Right ((x, xs) # xXsEqXxs)) = ?size_0_rhse_1 where
        perf : (x': a) -> (xs', xXs': c a) -> (x'::xs') = xXs' -> S (size xs') = size xXs'
        perf x' xs' xXs' prf with (Match xs')
          perf x' _ xXs' prf | (Left Refl) = ?perf_rhs_rhss_0
          perf x' xs' xXs' prf | (Right y) = ?perf_rhs_rhss_1



-- covering
-- public export
-- 0 ConcNilRightNeutral : (xs: c a) -> Sized (c a) => DecEq a => Container a c => xs ++ [] = xs
-- ConcNilRightNeutral xs with (sizeAccessible xs)
--   ConcNilRightNeutral xs | acc with (Match xs)
--     ConcNilRightNeutral _ | acc | Left Refl = ConcNilLeftNeutral []
--     ConcNilRightNeutral _ | acc | Right ((x, xs') # Refl) =
--       let
--         sa = (ConcNilRightNeutral xs' | ?helps)
--       in ConcReduces x xs' [] `transitive` (cong (x ::) sa)

-- covering
-- public export
-- 0 ConcMerges : (xs: c a) -> (ys: c a) -> (x: a) -> DecEq a => Container a c => x .#. (xs ++ ys) = x .#. xs + x .#. ys
-- ConcMerges xs ys x with (Match xs)
--   ConcMerges _ ys x | (Left Refl) = cong2 (+) (sym (NilIsEmpty {c} x)) (cong (x .#.) $ ConcNilLeftNeutral ys)
--   ConcMerges _ ys x | (Right ((x', xs') # Refl)) with (decEq x x')
--     ConcMerges _ ys x | (Right ((x, xs') # Refl)) | (Yes Refl) = (((cong (x .#.) (ConcReduces x xs' ys)) `transitive` (sym $ ConsAddsOne x (xs' ++ ys))) `transitive` (cong S (ConcMerges xs' ys x))) `transitive` (cong (+ (x .#. ys)) $ ConsAddsOne x xs')
--     ConcMerges _ ys x | (Right ((x', xs') # Refl)) | (No xNEqX') = (((cong (x .#.) (ConcReduces x' xs' ys)) `transitive` (sym $ ConsKeepsRest x' (xs' ++ ys) x xNEqX')) `transitive` (ConcMerges xs' ys x)) `transitive` (cong (+ (x .#. ys)) $ ConsKeepsRest x' xs' x xNEqX')


-- -- Implementation for List

-- public export
-- yes : DecEq a => (x: a) -> decEq x x = Yes Refl
-- yes x with (decEq x x)
--   yes x | (Yes Refl) = Refl
--   yes x | (No xNEqX) = void $ xNEqX Refl

-- public export
-- no : DecEq a => {x, x': a} -> (xNEqX': Not (x=x')) -> Not (x=x') # (\ctra => decEq x x' = No {prop=(x=x')} ctra)
-- no xNEqX' with (decEq x x')
--   no x'NEqX' | (Yes Refl) = void $ x'NEqX' Refl
--   no _ | (No xNEqX') = xNEqX' # Refl


-- 0 Next : {x: a} -> {xs: c a} -> Container a c => {n: Nat} -> x .#. xs = n -> x .#. (Container.(::) x xs) = 1+n
-- Next prf = (sym $ ConsAddsOne x xs) `transitive` (cong S prf)

-- public export
-- ford : (0 _: a = b) -> a -> b
-- ford Refl = id
