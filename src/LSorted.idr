module LSorted

import Data.Linear.LMaybe
import Data.Linear.LNat
import Data.Linear.Notation
import Data.Nat
import Data.Nat.Views
import Data.Linear.LList
import Data.Linear.LEither

import Sorted.Prop
import Sorted.Vect

%default total

--------------------
-- Help with proofs

-- linear implication: if f = g and x = y then f x = g y
limpl: {x, y: a} -> {f, g: (1 _:a) -> b} -> (f = g) -> (x = y) -> (f x = g y)
limpl Refl Refl = Refl

-- linear implication: if f = g then f x = f x
limpl': {x: a} -> {f, g: (1 _:a) -> b} -> (f = g) -> (f x = g x)
limpl' Refl = Refl

-- linear implication: if x = y then f x = f y
limpl'': {x, y: a} -> {f: (1 _:a) -> b}-> (x = y) -> (f x = f y)
limpl'' Refl = Refl

------------------

||| Sets equipped with a single binary operation that is associative.  Must
||| satisfy the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
public export
interface LSemigroup ty (0 op: (1 _: ty) -> (1 _: ty) -> ty) | op where
  constructor MkLSemigroup
  assoc: (a: ty) -> (b: ty) -> (c: ty) -> (op a (op b c)) = (op (op a  b) c)

-- Proving this required functional extensionality, which Idris lacks:
-- see Control.Function.FunExt
pointwiseEquality: {f, g: a->b} -> ((x: a) -> (f x = g x)) -> ((\x => f x) = (\x => g x))
pointwiseEquality pwe = ?functionEquality_0

public export
LSemigroup ty op => LSemigroup (t->ty) (\f => \g => \x => op (f x) (g x)) where
  assoc a b c = let helper = \x => assoc {op=op} (a x) (b x) (c x) in ?help

||| + Neutral for `<+>`:
|||     forall a, a <+> neutral == a
|||     forall a, neutral <+> a == a
public export
interface LSemigroup ty op => LMonoid (0 ty: Type) (0 op: (1 _: ty) -> (1 _: ty) -> ty) where
  constructor MkLMonoid
  neutral : ty
  rightNeutral : (a: ty) -> op a neutral = a
  leftNeutral : (a: ty) -> op neutral a = a


public export
Monoid b => Monoid (a -> b) where
  neutral _ = neutral

-- Application for the natural group of LNat

public export
summy : (1 _: LNat) -> (1 _: LNat) -> LNat
summy Zero j = j
summy (Succ k) j = Succ (summy k j)

LSemigroup LNat LSorted.summy where
    assoc Zero  Zero x = Refl
    assoc Zero  (Succ x) c = Refl
    assoc (Succ x)  b c = limpl'' {f=Succ} (assoc {op=LSorted.summy} x b c)

LMonoid LNat LSorted.summy where
    neutral = Zero
    leftNeutral a = Refl
    rightNeutral Zero = Refl
    rightNeutral (Succ x) = limpl'' {f=Succ} (rightNeutral {op=LSorted.summy} x)

-- data ExtractSides 
--     Extract = {0 x1, x2: a} -> Dec (x1 = x2) -> LPair a a

||| Decision procedures for propositional equality
public export
interface LDecEq t where
  ||| Decide whether two elements of `t` are propositionally equal
  decEq : (1 _: t) -> (1 _: t) -> Res (Dec (x1 = x2)) (\de => Dec (x1 = x2))

-- Control.Relation

||| A relation is reflexive if x ~ x for every x.
public export
interface LReflexive ty rel | rel where
  constructor MkLReflexive
  reflexive : {1 x : ty} -> rel x x


||| A relation is transitive if x ~ z when x ~ y and y ~ z.
public export
interface LTransitive ty rel | rel where
  constructor MkLTransitive
  transitive : {1 x, y, z : ty} -> rel x y -> rel y z -> rel x z


||| A relation is antisymmetric if no two distinct elements bear the relation to each other.
public export
interface LAntisymmetric ty rel | rel where
  constructor MkLAntisymmetric
  antisymmetric : {1 x, y : ty} -> rel x y -> rel y x -> x = y

-- Control.Order


||| A preorder is reflexive and transitive.
public export
interface (LReflexive ty rel, LTransitive ty rel) => LPreorder ty rel where

||| A partial order is an antisymmetrics preorder.
public export
interface (LPreorder ty rel, LAntisymmetric ty rel) => LPartialOrder ty rel where

||| A relation is connex if for any two distinct x and y, either x ~ y or y ~ x.
|||
||| This can also be stated as a trichotomy: x ~ y or x = y or y ~ x.
public export
interface LConnex ty rel where
  connex : {1 x, y : ty} -> Not (x = y) -> LEither (rel x y) (rel y x)

sortTwo : (LDecEq a) => (LConnex a rel) => (1 x: a) -> (1 y: a) -> ((LPair a a) ## \(x # y) => rel x y )
-- sortTwo x y = case decEq x y of
--     (Yes xEqy) #  => ?sortTwo_0

||| A linear order is a connex partial order.
public export
interface (LPartialOrder ty rel, LConnex ty rel) => LLinearOrder ty rel where

-- Actual sorting

public export
data Sorted: (0 lo: LLinearOrder a rel) => (LList a) -> Type where
    NilIsSorted: Sorted @{lo} Nil
    SingletonIsSorted : Sorted @{lo} [x]
    SeveralAreSorted: (LLinearOrder a rel) => (0 _: rel x y) -> (0 _: Sorted @{lo} (y::ys)) -> Sorted @{lo} (x::y::ys)

public export
0 sortedTail : (0 lo: LLinearOrder a rel) => Sorted @{lo} (x::xs) -> Sorted @{lo} xs
sortedTail SingletonIsSorted = NilIsSorted
sortedTail (SeveralAreSorted z w) = w

public export
split : LList a -@ LPair (LList a) (LList a)
split [] = ([] # [])
split [x] = ([] # [x])
split (x::y::tail) = let (xs # ys) = LSorted.split tail in ((x::xs) # (y::ys))

covering
public export
merge: (LDecEq a) => (lo: LLinearOrder a rel) => (1 xs: (LList a) ## (Sorted @{lo})) -> (1 ys: (LList a) ## (Sorted @{lo}))
    -> ((LList a) ## (Sorted @{lo})) ## \merged => (forall j . (Sorted @{lo} (j::lsubject xs)) -> (Sorted @{lo} (j::lsubject ys)) -> Sorted @{lo} (j::(lsubject merged)))
merge ([] ## _)  y =  y ## (\_ => \a => a)
merge x ([] ## _) = (x ## (\w => \_ => w))
merge ((x::xs) ## px) ((y::ys) ## py) =
    let
        xrely: LEither (rel x y) (rel y x) = case decEq x y of
            (squirm # (Yes xEqy)) => ?merge_0 -- Left (rewrite xEqy in reflexive)
            (squirm # (No xNEqy)) => ?merge_1 -- connex xNEqy
    in
        case xrely of
            Left vrel =>
                let
                    (xsz ## pxz) ## f = merge (xs ## (sortedTail px)) (y::ys ## py)
                in
                    ((x :: xsz) # (f px (SeveralAreSorted @{lo} vrel py))) # (
                        \(SeveralAreSorted xxa xxb) => \(SeveralAreSorted yya yyb) => (SeveralAreSorted xxa $ f xxb $ SeveralAreSorted vrel yyb))
            Right vrel =>
                let
                    ((ysz # pxz) # f) = merge (x::xs # px) (ys # (sortedTail py))
                in
                    (((y :: ysz) # (f (SeveralAreSorted vrel px) py)) # (
                        \(SeveralAreSorted xxa xxb) => \(SeveralAreSorted yya yyb) => (SeveralAreSorted yya $ f (SeveralAreSorted vrel xxb) yyb)))
covering
public export
mergeSort : (LDecEq a) => (lo: LLinearOrder a rel) => (1 _: LList a) -> (LList a) ## (Sorted @{lo})
mergeSort [] = [] ## NilIsSorted
mergeSort [x] = [x] ## SingletonIsSorted
mergeSort (x::y::tail) =
    let
        (l # r) = LSorted.split tail
        l' = mergeSort (assert_smaller (x::y::tail) (x::l))
        r' = mergeSort (assert_smaller (x::y::tail) (y::r))
        (res # _) = merge  l' r'
    in
        res
