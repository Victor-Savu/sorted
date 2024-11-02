module Sorted.Container.Heap

import Algebra.Solver.Semiring
import Control.Order
import Control.Relation
import Data.Fin
import Data.List.Views
import Data.Nat
import Data.Void
import Syntax.PreorderReasoning

import Sorted.IsPermutationOf
import Sorted.IsSortingOf
import Sorted.Prop
import Sorted.Relates
import Sorted.Sorted

%default total

export
Maybe' : Nat -> Type -> Type
Maybe' 0 _ = ()
Maybe' (S _) ty = ty


data Heap : LinearOrder a rel => (n: Nat) -> (h: Maybe' n a) -> Type where
    Nil : Heap @{lo} 0 _
    Singleton: (h: a) -> Heap @{lo} {a} 1 h
    Prick : (h: a) -> (s: a) -> (0 h≤s: rel h s) -> Heap @{lo} {rel} 2 h
    Balanced : (h: a) -> (0 h≤l: rel h l) -> (0 h≤r: rel h r) -> (left: Heap @{lo} (1+m) l) -> (right: Heap @{lo} (1+m) r) -> Heap @{lo} {rel} (3+m+m) h
    Imbalanced : (h: a) -> (0 h≤l: rel h l) -> (0 h≤r: rel h r) -> (left: Heap @{lo} (2 + m) l) -> (right: Heap @{lo} (1+m) r) -> Heap @{lo} {rel} (4+m+m) h

export
length : LinearOrder a rel => Heap {rel} n h -> Nat
length [] = 0
length (Singleton h) = 1
length (Prick h s h≤s) = 2
length (Balanced h h≤l h≤r left right) = 1 + 2 * length right
length (Imbalanced h h≤l h≤r left right) = 2 + 2 * length right


actualMin :  DecEq a => LinearOrder a rel => a -> a -> a
actualMin x y with (decEq x y)
  actualMin x x | (Yes Refl) = x
  actualMin x y | (No x≠y) with (connex {rel} x≠y)
    actualMin x y | (No x≠y) | Left x≤y = x
    actualMin x y | (No x≠y) | Right y≤x = y


min' : DecEq a => LinearOrder a rel => {n: Nat} -> a -> Maybe' n a -> a
min' {n = 0} x _ = x
min' {n = (S k)} x y = actualMin {rel} x y


max' : DecEq a => LinearOrder a rel => a -> a -> a
max' x y with (decEq x y)
  max' x x | (Yes Refl) = x
  max' x y | (No x≠y) with (connex {rel} x≠y)
    max' x y | (No x≠y) | (Left x≤y) = y
    max' x y | (No x≠y) | (Right y≤x) = x

-- minLeft : DecEq a => LinearOrder a rel => {x, y: a} -> rel x y -> min' {rel} {n=1+n} x y = x
-- minLeft x≤y with (leanLeft {rel} x y)
--   minLeft x≤y | (Left _) = Refl
--   minLeft x≤y | (Right y≤x) with (decEq x y)
--     minLeft x≤y | (Right y≤x) | (Yes Refl) = Refl
--     minLeft x≤y | (Right y≤x) | (No x≠y) = void $ x≠y $ antisymmetric x≤y y≤x

-- minRight : DecEq a => LinearOrder a rel => {x, y: a} -> rel y x -> min' {rel} {n=1+n} x y = y
-- minRight y≤x with (leanLeft {rel} x y)
--   minRight y≤x | (Left x≤y) with (decEq x y)
--     minRight y≤x | (Left x≤y) | (Yes Refl) = Refl
--     minRight y≤x | (Left x≤y) | (No x≠y) = void $ x≠y $ antisymmetric x≤y y≤x
--   minRight y≤x | (Right _) = Refl


min'' : DecEq a => LinearOrder a rel => {m, n: Nat} -> Maybe' m a -> Maybe' n a -> Maybe' (m+n) a
min'' {m = 0} _ x = rewrite plusZeroLeftNeutral n in x
min'' {m = (S k)} x y = min' {rel} x y

cong2' : {0 p: t1 -> Type} -> {0 c: p a} -> {0 d: p b} -> (0 f : ((v: t1) -> p v -> u)) -> (0 _ : a = b) -> (0 _ : c = d) -> f a c = f b d
cong2' f Refl Refl = Refl

smallerLessThanMin : DecEq a => LinearOrder a rel => {h, h', l: a} -> (h≤l: rel h l) -> (h≤h': rel h h') -> rel h (actualMin {rel} h' l)
smallerLessThanMin h≤l h≤h' with (decEq h' l)
  smallerLessThanMin h≤l h≤h' | (Yes Refl) = h≤l
  smallerLessThanMin h≤l h≤h' | (No h'≠l) with (connex {rel} h'≠l)
    smallerLessThanMin h≤l h≤h' | (No h'≠l) | (Left h'≤l) = h≤h'
    smallerLessThanMin h≤l h≤h' | (No h'≠l) | (Right l≤h') = h≤l

minLessThanGreater : DecEq a => LinearOrder a rel => {h, h', l: a} -> (h≤l: rel h l) -> rel (actualMin {rel} h h') l
minLessThanGreater h≤l with (decEq h h')
  minLessThanGreater h≤l | (Yes Refl) = h≤l
  minLessThanGreater h≤l | (No h≠h') with (connex {rel} h≠h')
    minLessThanGreater h≤l | (No h≠h') | (Left h≤h') = h≤l
    minLessThanGreater h≤l | (No h≠h') | (Right h'≤h) = (h'≤h \=> h≤l)

congMin : DecEq a => LinearOrder a rel => {h, h', l, l': a} -> (h≤l: rel h l) -> (h'≤l': rel h' l') -> rel (actualMin {rel} h h') (actualMin {rel} l l')
congMin h≤l h'≤l' with (decEq h h')
  congMin h≤l h≤l' | (Yes Refl) = smallerLessThanMin {rel} h≤l' h≤l
  congMin h≤l h'≤l' | (No h≠h') with (connex {rel} h≠h')
    congMin h≤l h'≤l' | (No h≠h') | (Left h≤h') = smallerLessThanMin {rel} (h≤h' \=> h'≤l') h≤l
    congMin h≤l h'≤l' | (No h≠h') | (Right h'≤h) = smallerLessThanMin {rel} h'≤l' (h'≤h \=> h≤l)

min≤max : DecEq a => LinearOrder a rel => {h, h': a} -> rel (actualMin {rel} h h') (max' {rel} h h')
min≤max with (decEq h h')
  min≤max | (Yes Refl) = reflexive
  min≤max | (No h≠h') with (connex {rel} h≠h')
    min≤max | (No h≠h') | (Left h≤h') = h≤h'
    min≤max | (No h≠h') | (Right h'≤h) = h'≤h

minCommutes : DecEq a => LinearOrder a rel => {h, h': a} -> rel (actualMin {rel} h h') (actualMin {rel} h' h)
minCommutes with (decEq h h')
  minCommutes | (Yes Refl) = rewrite decEqSelfIsYes {x=h'} in reflexive
  minCommutes | (No h≠h') with (connex {rel} h≠h')
    minCommutes | (No h≠h') | (Left h≤h') = (smallerLessThanMin {rel} reflexive h≤h')
    minCommutes | (No h≠h') | (Right h'≤h) = (smallerLessThanMin {rel} h'≤h reflexive)

-- decEqPrf : DecEq a => {x, y: a} -> (x≠y: Not (x=y)) -> No x≠y = decEq x y
-- decEqPrf x≠y with (decEq x y)
--   decEqPrf x≠y | (Yes Refl) = void $ x≠y Refl
--   decEqPrf _ | (No x≠'y) = ?decEqPrf_rhs_rhss_1

minCom : DecEq a => LinearOrder a rel => {x, y: a} -> actualMin {rel} x y = actualMin {rel} y x
minCom with (decEq x y)
  minCom | (Yes Refl) = rewrite decEqSelfIsYes {x=y} in Refl
  minCom | (No x≠y) with (connex {rel} x≠y)
    minCom | (No x≠y) | (Left x≤y) with (decEq y x)
      minCom | (No x≠y) | (Left x≤y) | (Yes Refl) = Refl
      minCom | (No x≠y) | (Left x≤y) | (No y≠x) with (connex {rel} y≠x)
        minCom | (No x≠y) | (Left x≤y) | (No y≠x) | (Left y≤x) = void $ x≠y (antisymmetric x≤y y≤x)
        minCom | (No x≠y) | (Left x≤y) | (No y≠x) | (Right _) = Refl
    minCom | (No x≠y) | (Right y≤x) with (decEq y x)
      minCom | (No x≠y) | (Right y≤x) | (Yes Refl) = Refl
      minCom | (No x≠y) | (Right y≤x) | (No y≠x) with (connex {rel} y≠x)
        minCom | (No x≠y) | (Right y≤x) | (No y≠x) | (Left _) = Refl
        minCom | (No x≠y) | (Right y≤x) | (No y≠x) | (Right x≤y) = void $ x≠y (antisymmetric x≤y y≤x)

plusSuccLeftSucc : (a, b: Nat) ->  plus (S a) b = S (plus a b)
plusSuccLeftSucc _ _ = Refl

0 connexLeft : DecEq a => LinearOrder a rel => rel x y -> (rel x y) # (\x≤y => connex {rel} x≠y = Left x≤y)
connexLeft x≤y with (connex {rel} x≠y)
  connexLeft _ | (Left x≤y) = x≤y # Refl
  connexLeft x≤y | (Right y≤x) = void $ x≠y (antisymmetric x≤y y≤x)

0 connexRight : DecEq a => LinearOrder a rel => rel y x -> (rel y x) # (\h≤x => connex {rel} x≠y = Right h≤x)
connexRight y≤x with (connex {rel} x≠y)
  connexRight y≤x | (Left x≤y) = void $ x≠y (antisymmetric x≤y y≤x)
  connexRight _ | (Right y≤x) = y≤x # Refl

0 aminLeft : DecEq a => LinearOrder a rel => rel x y -> actualMin {rel} x y = x
aminLeft x≤y with (decEq x y)
  aminLeft x≤y | (Yes Refl) = Refl
  aminLeft x≤y | (No x≠y) with (connex {rel} x≠y)
    aminLeft _ | (No x≠y) | (Left x≤y) = Refl
    aminLeft x≤y | (No x≠y) | (Right y≤x) = void $ x≠y (antisymmetric x≤y y≤x)

0 aminRight : DecEq a => LinearOrder a rel => rel y x -> Not (x = y) -> actualMin {rel} x y = y
aminRight y≤x x≠y with (decEq x y)
  aminRight y≤x x≠y | (Yes Refl) = Refl
  aminRight y≤x x≠y | (No x≠'y) with (connex {rel} x≠'y)
    aminRight y≤x x≠y | (No x≠'y) | (Left x≤y) = void $ x≠'y (antisymmetric x≤y y≤x)
    aminRight _ x≠y | (No x≠'y) | (Right y≤x) = Refl

0 maxLeft : DecEq a => LinearOrder a rel => rel x y -> max' {rel} x y = y
maxLeft x≤y with (decEq x y)
  maxLeft x≤y | (Yes Refl) = Refl
  maxLeft x≤y | (No x≠y) with (connex {rel} x≠y)
    maxLeft _ | (No x≠y) | (Left x≤y) = Refl
    maxLeft x≤y | (No x≠y) | (Right y≤x) = void $ x≠y (antisymmetric x≤y y≤x)

0 maxRight : DecEq a => LinearOrder a rel => rel y x -> Not (x = y) -> max' {rel} x y = x
maxRight y≤x x≠y with (decEq x y)
  maxRight y≤x x≠y | (Yes Refl) = Refl
  maxRight y≤x _ | (No x≠y) with (connex {rel} x≠y)
    maxRight y≤x _ | (No x≠y) | (Left x≤y) = void $ x≠y (antisymmetric x≤y y≤x)
    maxRight _ _ | (No x≠y) | (Right y≤x) = Refl


(::) : DecEq a => LinearOrder a rel => (x: a) -> Heap {a} {rel} n h -> Heap {a} {rel} (1+n) (min' {n} {rel} x h)
(::) x [] = Singleton x
(::) x (Singleton h) = Prick (actualMin {rel} x h) (max' {rel} x h) (min≤max {rel})
(::) x (Prick h s h≤s) =
  Balanced
    (actualMin {rel} x h)
    (min≤max {rel})
    (minCommutes {rel} \=> minLessThanGreater {rel} h≤s)
    (Singleton (max' {rel} x h))
    (Singleton s)
(::) x (Balanced {l} {r} h h≤l h≤r left right) =
  Imbalanced
    (actualMin {rel} x h)
    (smallerLessThanMin {rel} (minCommutes {rel} \=> minLessThanGreater {rel} h≤l) (min≤max {rel}))
    (minCommutes {rel} \=> minLessThanGreater {rel} h≤r)
    ((max' {rel} x h) :: left)
    right
(::) {n=4+m+m} x (Imbalanced {r} h h≤l h≤r left right) =
  rewrite plusSuccRightSucc m m in (
    Balanced
      (actualMin {rel} x h)
      (minCommutes {rel} \=> minLessThanGreater {rel} h≤l)
      (smallerLessThanMin {rel} (minCommutes {rel} \=> minLessThanGreater {rel} h≤r) (min≤max {rel}))
      left
      (max' {rel} x h :: right)
    )

-- %ambiguity_depth 6

-- (++) : DecEq a => LinearOrder a rel => Heap {a} {rel} m h -> Heap {a} {rel} n h' -> Heap {a} {rel} (m+n) (min'' {rel} {m} {n} h h')
-- (++) [] y = y
-- (++) (Singleton h) y = h::y
-- (++) (Prick h s h≤s) [] = Prick h s h≤s
-- (++) (Prick h s h≤s) (Singleton h') =
--       Balanced
--         (actualMin {rel} h h')
--         (min≤max {rel})
--         (minLessThanGreater {rel} h≤s)
--         (Singleton (max' {rel} h h'))
--         (Singleton s)
-- (++) (Prick h s h≤s) (Prick h' s' h'≤s') =
--       Imbalanced
--         (actualMin {rel} h h')
--         ((congMin {rel} h≤s h'≤s'))
--         (min≤max {rel})
--         (Prick (actualMin {rel} s s') (max' {rel} s s') (min≤max {rel}))
--         (Singleton (max' {rel} h h'))
-- (++) {n = ((3 + n) + n)} (Prick h s h≤s) (Balanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
--       rewrite solveNat [n] (1 + ((0 +. n) +. n)) ((0 +. n) + (0 + (1 +. n))) in
--         (Balanced
--           (actualMin {rel} h h')
--           (smallerLessThanMin {rel} (minCommutes {rel} \=> (minLessThanGreater {rel} h'≤l')) (min≤max {rel}))
--           (congMin {rel} h≤s h'≤r')
--           (max' {rel} h h' :: left')
--           (s :: right')
--         )
-- (++) {n = ((4 + n) + n)} (Prick h s h≤s) (Imbalanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
--       rewrite solveNat [n] (1 + ((0 +. n) +. n)) ((0 +. n) + (0 + (1 +. n))) in
--         (Imbalanced
--           (actualMin {rel} h h')
--           (smallerLessThanMin {rel} (minCommutes {rel} \=> (minLessThanGreater {rel} h'≤l')) (min≤max {rel}))
--           (congMin {rel} h≤s h'≤r')
--           (max' {rel} h h' :: left')
--           (s :: right')
--         )
-- (++) {m=3+(m+m)} L@(Balanced h h≤l h≤r left right) [] = rewrite solveNat [m] (((0 +. m) +. m) + 0) ((0 +. m) +. m) in L
-- (++) {m=3+(m+m)} (Balanced {l} {r} h h≤l h≤r left right) (Singleton h') =
--       rewrite solveNat [m] (3 + ((0 + (m .+. m)) + 1)) (4 + (0 + (m .+. m))) in
--         (Imbalanced
--           (actualMin {rel} h h')
--           (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤l) (min≤max {rel}))
--           (minLessThanGreater {rel} h≤r)
--           (max' {rel} h h' :: left)
--           right
--         )
-- (++) {m=3+(m+m)} (Balanced {l} {r} h h≤l h≤r left right) (Prick h' s' h'≤s') =
--       rewrite solveNat [m] (3 + ((m .+. m) + 2)) (4 + (m .+ (1 +. m))) in
--         (Balanced
--           (actualMin {rel} h h')
--           (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤l) (min≤max {rel}))
--           (congMin {rel} h≤r h'≤s' \=> minCommutes {rel})
--           (max' {rel} h h' :: left)
--           (s' :: right)
--         )
-- (++) {m=3+(m+m)} {n=3+(m'+m')} (Balanced {l} {r} h h≤l h≤r left right) (Balanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
--       rewrite solveNat [m,m'] (3 + ((m .+. m) + (3 + (m' .+. m')))) (4 + ( (m .+ (1 +. m')) + (m .+ (1 +. m')))) in
--         (Imbalanced
--           (actualMin {rel} h h')
--           (smallerLessThanMin {rel} (congMin {rel} h≤l h'≤l') (min≤max {rel}))
--           (congMin {rel} h≤r h'≤r')
--           (max' {rel} h h' :: (left ++ left'))
--           (right ++ right')
--         )
-- (++) {m=3+(m+m)} {n=4+(m'+m')} (Balanced {l} {r} h h≤l h≤r left right) (Imbalanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
--       rewrite solveNat [m,m'] (3 + ((m .+. m) + (4 + (m' .+. m')))) (4 + ( (m .+ (1 +. m')) + (1 + (m .+ (1 +. m'))))) in
--         (Balanced
--           (actualMin {rel} h h')
--           (congMin {rel} h≤l h'≤l')
--           (smallerLessThanMin {rel} (congMin {rel} h≤r h'≤r') (min≤max {rel}))
--           (rewrite solveNat [m,m'] (1 + ((0 +. m) + (1 +. m'))) ((0 +. m) + (2 +. m')) in left++left')
--           (max' {rel} h h' :: (right ++ right'))
--         )
-- (++) {m=4+m+m} L@(Imbalanced h h≤l h≤r left right) [] = rewrite (plusZeroLeftNeutral m) in rewrite (plusZeroRightNeutral (m+m)) in L
-- (++) {m=4+m+m} (Imbalanced h h≤l h≤r left right) (Singleton h') =
--       rewrite solveNat [m] (((0 +. m) +. m) + 1) ((0 +. m) + (1 +. m)) in
--         (Balanced
--           (actualMin {rel} h h')
--           (minLessThanGreater {rel} h≤l)
--           (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤r) (min≤max {rel}))
--           left
--           (max' {rel} h h' :: right)
--         )
-- (++) {m=4+m+m} (Imbalanced h h≤l h≤r left right) (Prick h' s' h'≤s') =
--       rewrite solveNat [m] (((0 +. m) +. m) + 2) (1 + ((0 +. m) + (0 + (1 +. m)))) in
--         (Imbalanced
--           (actualMin {rel} h h')
--           (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤l) (min≤max {rel}))
--           (minCommutes {rel} \=> congMin {rel} h'≤s' h≤r)
--           (max' {rel} h h' :: left)
--           (s' :: right)
--         )
-- (++) {m=4+m+m} {n=3+m'+m'} (Imbalanced h h≤l h≤r left right) (Balanced h' h'≤l' h'≤r' left' right') =
--       rewrite solveNat [m,m'] (4 + ((m .+. m) + (3 + (m' .+. m')))) (4 + ( (m .+ (1 +. m')) + (1 + (m .+ (1 +. m'))))) in
--         (Balanced
--           (actualMin {rel} h h')
--           (congMin {rel} h≤l h'≤l')
--           (smallerLessThanMin {rel} (congMin {rel} h≤r h'≤r') (min≤max {rel}))
--           (left ++ left')
--           (max' {rel} h h' :: (right ++ right'))
--         )
-- (++) {m=4+m+m} {n=4+m'+m'} (Imbalanced h h≤l h≤r left right) (Imbalanced h' h'≤l' h'≤r' left' right') =
--       rewrite solveNat [m,m'] (((0 +. m) +. m) + (1 + ((3 +. m') +. m'))) (1 + (((0 +. m) + (1 +. m')) + ((1 +. m) + (1 +. m')))) in
--         (Imbalanced
--             (actualMin {rel} h h')
--             (congMin {rel} h≤l h'≤l')
--             (smallerLessThanMin {rel} (congMin {rel} h≤r h'≤r') (min≤max {rel}))
--             (rewrite solveNat [m,m'] (1 + ((0 +. m) + (1 +. m'))) ((0 +. m) + (2 +. m')) in left ++ left')
--             (max' {rel} h h' :: right ++ right')
--           )

cnt : DecEq a => LinearOrder a rel => (x: a) -> (xs: Heap {rel} n h) -> Nat
cnt x [] = 0
cnt x (Singleton h) with (decEq x h)
  cnt x (Singleton x) | (Yes Refl) = 1
  cnt x (Singleton h) | (No _) = 0
cnt x (Prick h s hs) with (decEq x h)
  cnt x (Prick x s hs) | (Yes Refl) with (decEq x s)
    cnt x (Prick x x hs) | (Yes Refl) | (Yes Refl) = 2
    cnt x (Prick x s hs) | (Yes Refl) | (No _) = 1
  cnt x (Prick h s hs) | (No _) with (decEq x s)
    cnt x (Prick h x hs) | (No _) | (Yes Refl) = 1
    cnt x (Prick h s hs) | (No _) | (No _) = 0
cnt x (Balanced h {l} {r} hl hr left right) with (decEq x h)
  cnt x (Balanced x {l} {r} x≤l x≤r left right) | (Yes Refl) = 1 + cnt x left + cnt x right
  cnt x (Balanced h {l} {r} h≤l h≤r left right) | (No x≠h) with (connex {rel} x≠h)
    cnt x (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Left x≤h) = 0
    cnt x (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) = cnt x left + cnt x right
cnt x (Imbalanced h hl hr left right)  with (decEq x h)
  cnt x (Imbalanced x x≤l x≤r left right) | (Yes Refl) = 1 + cnt x left + cnt x right
  cnt x (Imbalanced h hl hr left right) | (No x≠h) with (connex {rel} x≠h)
    cnt x (Imbalanced h hl hr left right) | (No x≠h) | (Left _) = 0
    cnt x (Imbalanced h hl hr left right) | (No x≠h) | (Right _) = cnt x left + cnt x right

0 strict : DecEq a => LinearOrder a rel  => (x≠h: (x=h -> Void)) -> (x≤h: rel x h) -> (h≤s: rel h s) -> x=s -> Void
strict x≠h x≤h h≤s Refl = void $ x≠h (antisymmetric x≤h h≤s)

0 cntTooSmall : DecEq a => LinearOrder a rel => (x: a) -> (x≠h: (x=h -> Void)) -> (x≤h: rel x h) -> (xs: Heap {rel} (S n) h) -> cnt x xs = 0
cntTooSmall x x≠h x≤h (Singleton h) = rewrite snd $ decEqContraIsNo x≠h in Refl
cntTooSmall x x≠h x≤h (Prick h s h≤s) =
  rewrite snd $ decEqContraIsNo x≠h in
  rewrite snd $ decEqContraIsNo (strict {rel} x≠h x≤h h≤s) in
  Refl
cntTooSmall x x≠h x≤h (Balanced h h≤l h≤r left right) with (decEq x h)
  cntTooSmall h h≠h h≤h (Balanced h h≤l h≤r left right) | (Yes Refl) = void $ h≠h Refl
  cntTooSmall x _ x≤h (Balanced h h≤l h≤r left right) | (No x≠h) with (connex {rel} x≠h)
    cntTooSmall x _ _ (Balanced h h≤l h≤r left right) | (No x≠h) | (Left x≤h) = Refl
    cntTooSmall x _ x≤h (Balanced h h≤l h≤r left right) | (No x≠h) | (Right h≤x) = void $ x≠h $ antisymmetric x≤h h≤x
cntTooSmall x x≠h x≤h (Imbalanced h h≤l h≤r left right) with (decEq x h)
  cntTooSmall h h≠h h≤h (Imbalanced h h≤l h≤r left right) | (Yes Refl) = void $ h≠h Refl
  cntTooSmall x _ x≤h (Imbalanced h h≤l h≤r left right) | (No x≠h) with (connex {rel} x≠h)
    cntTooSmall x _ _ (Imbalanced h h≤l h≤r left right) | (No x≠h) | (Left x≤h) = Refl
    cntTooSmall x _ x≤h (Imbalanced h h≤l h≤r left right) | (No x≠h) | (Right h≤x) = void $ x≠h $ antisymmetric x≤h h≤x
  
-- [ui] DecEq a => LinearOrder a rel => (xs: Heap {rel} (S n) h) => Uninhabited (forall x . cnt {rel} {n=S n} x xs = 0) where
--     uninhabited {xs = (Singleton h)} absrd = SIsNotZ $ ((rewrite decEqSelfIsYes {x=h} in Refl) \=> absrd {x=h})
--     uninhabited {xs = (Prick h s h≤s)} absrd with (decEq h s)
--       uninhabited {xs = (Prick h h h≤s)} absrd | (Yes Refl) = SIsNotZ $ ((rewrite decEqSelfIsYes {x=h} in rewrite decEqSelfIsYes {x=h} in Refl) \=> absrd {x=h})
--       uninhabited {xs = (Prick h s h≤s)} absrd | (No h≠s) = SIsNotZ $ ((rewrite decEqSelfIsYes {x=h} in let _ # p = no h≠s in rewrite p in Refl) \=> absrd {x=h})
--     uninhabited {xs = (Balanced h h≤l h≤r left right)} absrd = SIsNotZ $ ((rewrite decEqSelfIsYes {x=h} in Refl) \=> absrd {x=h})
--     uninhabited {xs = (Imbalanced h h≤l h≤r left right)} absrd = SIsNotZ $ ((rewrite decEqSelfIsYes {x=h} in Refl) \=> absrd {x=h})

0 ConsAddsOne : DecEq a => LinearOrder a rel => (xs: Heap n h) -> forall x. (1 + cnt {rel} {n} x xs) = cnt {rel} {n=S n} x (Heap.(::) {rel} x xs)
ConsAddsOne [] = rewrite decEqSelfIsYes {x} in Refl
ConsAddsOne (Singleton h) with (decEq x h)
  ConsAddsOne (Singleton h) | (Yes Refl) = rewrite decEqSelfIsYes {x=h} in rewrite decEqSelfIsYes {x=h} in Refl
  ConsAddsOne (Singleton h) | (No x≠h) with (connex {rel} x≠h)
    ConsAddsOne (Singleton h) | (No x≠h) | (Left x≤h) = rewrite decEqSelfIsYes {x} in let _ # p = no x≠h in rewrite p in Refl
    ConsAddsOne (Singleton h) | (No x≠h) | (Right h≤x) = let _ # p = no x≠h in rewrite p in rewrite decEqSelfIsYes {x} in Refl
ConsAddsOne (Prick h s h≤s) with (decEq x h)
  ConsAddsOne (Prick h s h≤s) | (Yes Refl) with (decEq h s)
    ConsAddsOne (Prick s s h≤s) | (Yes Refl) | (Yes Refl) = rewrite decEqSelfIsYes {x=s} in rewrite decEqSelfIsYes {x=s} in Refl
    ConsAddsOne (Prick h s h≤s) | (Yes Refl) | (No h≠s) = rewrite decEqSelfIsYes {x=h} in rewrite decEqSelfIsYes {x=h} in let _ # p = no h≠s in rewrite p in Refl
  ConsAddsOne (Prick h s h≤s) | (No x≠h) with (decEq x s)
    ConsAddsOne (Prick h s h≤s) | (No s≠h) | (Yes Refl) with (connex {rel} s≠h)
      ConsAddsOne (Prick h s h≤s) | (No s≠h) | (Yes Refl) | (Left s≤h) = void $ s≠h (antisymmetric s≤h h≤s)
      ConsAddsOne (Prick h s h≤s) | (No s≠h) | (Yes Refl) | (Right h≤'s) with (decEq h s)
        ConsAddsOne (Prick h h h≤h) | (No h≠h) | (Yes Refl) | (Right h≤'h) | (Yes Refl) = void $ h≠h Refl
        ConsAddsOne (Prick h s h≤s) | (No s≠h) | (Yes Refl) | (Right h≤'s) | (No h≠s) with (connex {rel} h≠s)
          ConsAddsOne (Prick h s h≤s) | (No s≠h) | (Yes Refl) | (Right h≤'s) | (No h≠s) | (Left h≤''s) with (decEq s h)
            ConsAddsOne (Prick h h h≤s) | (No h≠h) | (Yes Refl) | (Right h≤'h) | (No h≠'h) | (Left h≤''h) | (Yes Refl) = void $ h≠h Refl
            ConsAddsOne (Prick h s h≤s) | (No s≠h) | (Yes Refl) | (Right h≤'s) | (No h≠s) | (Left h≤''s) | (No s≠'h) with (connex {rel} s≠'h)
              ConsAddsOne (Prick h s h≤s) | (No s≠h) | (Yes Refl) | (Right h≤'s) | (No h≠s) | (Left h≤''s) | (No s≠'h) | (Left s≤h) = void $ s≠h (antisymmetric s≤h h≤s)
              ConsAddsOne (Prick h s h≤s) | (No s≠h) | (Yes Refl) | (Right h≤'s) | (No h≠s) | (Left h≤''s) | (No s≠'h) | (Right h≤'''s) = rewrite decEqSelfIsYes {x=s} in Refl
          ConsAddsOne (Prick h s h≤s) | (No s≠h) | (Yes Refl) | (Right h≤'s) | (No h≠s) | (Right s≤h) = void $ s≠h (antisymmetric s≤h h≤s)
    ConsAddsOne (Prick h s h≤s) | (No x≠h) | (No x≠s) with (connex {rel} x≠h)
      ConsAddsOne (Prick h s h≤s) | (No x≠h) | (No x≠s) | (Left x≤h) = rewrite decEqSelfIsYes {x} in let _ # p = no x≠h in rewrite p in let _ # p = no x≠s in rewrite p in Refl
      ConsAddsOne (Prick h s h≤s) | (No x≠h) | (No x≠s) | (Right h≤x) with (decEq h x)
        ConsAddsOne (Prick h s h≤s) | (No h≠h) | (No h≠s) | (Right h≤h) | (Yes Refl) = void $ h≠h Refl
        ConsAddsOne (Prick h s h≤s) | (No x≠h) | (No x≠s) | (Right h≤x) | (No h≠x) with (decEq x h)
          ConsAddsOne (Prick h s h≤s) | (No x≠h) | (No x≠s) | (Right h≤x) | (No h≠x) | (Yes Refl) = void $ x≠h Refl
          ConsAddsOne (Prick h s h≤s) | (No x≠h) | (No x≠s) | (Right h≤x) | (No h≠x) | (No x≠'h) with (connex {rel} h≠x)
            ConsAddsOne (Prick h s h≤s) | (No x≠h) | (No x≠s) | (Right h≤x) | (No h≠x) | (No x≠'h) | (Left h≤'x) with (connex {rel} x≠'h)
              ConsAddsOne (Prick h s h≤s) | (No x≠h) | (No x≠s) | (Right h≤x) | (No h≠x) | (No x≠'h) | (Left h≤'x) | (Left x≤h) = void $ x≠h (antisymmetric x≤h h≤x)
              ConsAddsOne (Prick h s h≤s) | (No x≠h) | (No x≠s) | (Right h≤x) | (No h≠x) | (No x≠'h) | (Left h≤'x) | (Right h≤''x) =
                rewrite decEqSelfIsYes {x} in let _ # p = no x≠s in rewrite p in Refl
            ConsAddsOne (Prick h s h≤s) | (No x≠h) | (No x≠s) | (Right h≤x) | (No h≠x) | (No x≠'h) | (Right x≤h) = void $ x≠h (antisymmetric x≤h h≤x)
ConsAddsOne (Balanced h {l} {r} h≤l h≤r left right) with (decEq x h)
  ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (Yes Refl) = rewrite decEqSelfIsYes {x=h} in cong (\l => S(l + cnt h right)) (ConsAddsOne {x=h} left)
  ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) with (connex {rel} x≠h)
    ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Left x≤h) =
      rewrite decEqSelfIsYes {x} in
        cong S (sym (cong2 (+)
          (cntTooSmall {rel} x (\x_minhl => x≠h (x_minhl \=> (aminLeft h≤l))) (smallerLessThanMin {rel} (x≤h \=> h≤l) x≤h) _)
          (cntTooSmall {rel} x (strict x≠h x≤h h≤r) (x≤h \=> h≤r) _)
        ))
    ConsAddsOne (Balanced h {l} {r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) with (decEq h x)
      ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (Yes Refl) = void $ x≠h Refl
      ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) with (connex {rel} h≠x)
        ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) with (decEq x l)
          ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (Yes Refl) with (decEq l h)
            ConsAddsOne (Balanced l {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (Yes Refl) | (Yes Refl) = void $ x≠h Refl
            ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (Yes Refl) | (No l≠h) with (connex {rel} x≠h)
              ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (Yes Refl) | (No l≠h) | (Left x≤h) = void $ x≠h (antisymmetric x≤h h≤x)
              ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (Yes Refl) | (No l≠h) | (Right h≤''x) with (connex {rel} l≠h)
                ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (Yes Refl) | (No l≠h) | (Right h≤''x) | (Left l≤h) = void $ l≠h (antisymmetric l≤h h≤l)
                ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (Yes Refl) | (No l≠h) | (Right h≤''x) | (Right h≤'l) = cong (+ cnt l right) $ ConsAddsOne {x=l} left
          ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) with (connex {rel} x≠l)
            ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) | (Left x≤l) with (decEq x h)
              ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) | (Left x≤l) | (Yes Refl) = void $ x≠h Refl
              ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) | (Left x≤l) | (No x≠'h) with (connex {rel} x≠'h)
                ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) | (Left x≤l) | (No x≠'h) | (Left x≤h) = void $ x≠h (antisymmetric x≤h h≤x)
                ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) | (Left x≤l) | (No x≠'h) | (Right h≤''x) =
                  cong (+ cnt x right) $ ConsAddsOne {x} left
            ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) | (Right l≤x) with (decEq x h)
              ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) | (Right l≤x) | (Yes Refl) = void $ x≠h Refl
              ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) | (Right l≤x) | (No x≠'h) with (connex {rel} x≠'h)
                ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) | (Right l≤x) | (No x≠'h) | (Left x≤h) = void $ x≠h (antisymmetric x≤h h≤x)
                ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Left h≤'x) | (No x≠l) | (Right l≤x) | (No x≠'h) | (Right h≤''x) = cong (+ cnt x right) $ ConsAddsOne {x} left
        ConsAddsOne (Balanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Right x≤h) = void $ x≠h (antisymmetric x≤h h≤x)
ConsAddsOne (Imbalanced h {l} {r} h≤l h≤r left right) with (decEq x h)
  ConsAddsOne (Imbalanced h {l} {r} h≤l h≤r left right) | (Yes Refl) = rewrite decEqSelfIsYes {x=h} in cong S ((plusSuccRightSucc _ _) \=> cong (cnt h left +) (ConsAddsOne right))
  ConsAddsOne (Imbalanced h {l} {r} h≤l h≤r left right) | (No x≠h) with (connex {rel} x≠h)
    ConsAddsOne (Imbalanced h {l} {r} h≤l h≤r left right) | (No x≠h) | (Left x≤h) =
      rewrite decEqSelfIsYes {x} in
        cong S (
          cong2 (+)
            (sym $ cntTooSmall {rel} x (strict x≠h x≤h h≤l) (x≤h \=> h≤l) left)
            (sym $ cntTooSmall {rel} x (strict {rel} x≠h x≤h (smallerLessThanMin {rel} h≤r reflexive)) (smallerLessThanMin {rel} (x≤h \=> h≤r) x≤h) (h::right))
          )
    ConsAddsOne (Imbalanced h {l} {r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) with (decEq h x)
      ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No h≠h) | (Right h≤h) | (Yes Refl) = void $ h≠h Refl
      ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) with (connex {rel} h≠x)
        ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right _) | (No h≠x) | (Left h≤x) with (decEq x r)
          ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No r≠h) | (Right _) | (No h≠r) | (Left h≤x) | (Yes Refl) with (decEq r h)
            ConsAddsOne (Imbalanced h {l = l} {r = h} h≤l h≤r left right) | (No r≠h) | (Right _) | (No h≠h) | (Left h≤x) | (Yes Refl) | (Yes Refl) = void $ h≠h Refl
            ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No _) | (Right _) | (No h≠r) | (Left h≤x) | (Yes Refl) | (No r≠h) with (connex {rel} r≠h)
              ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No _) | (Right _) | (No h≠r) | (Left h≤x) | (Yes Refl) | (No r≠h) | (Left r≤h) = void $ h≠r $ antisymmetric h≤r r≤h
              ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l _ left right) | (No _) | (Right _) | (No h≠r) | (Left h≤x) | (Yes Refl) | (No r≠h) | (Right h≤r) = plusSuccRightSucc _ _ \=> cong (cnt r left +) (ConsAddsOne {x=r} right)
          ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right _) | (No h≠x) | (Left h≤x) | (No x≠r) with (decEq x h)
            ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No _) | (Right _) | (No h≠h) | (Left h≤h) | (No h≠r) | (Yes Refl) = void $ h≠h Refl 
            ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No _) | (Right _) | (No h≠x) | (Left h≤x) | (No x≠r) | (No x≠h) with (connex {rel} x≠h)
              ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No _) | (Right _) | (No h≠x) | (Left h≤x) | (No x≠r) | (No x≠h) | (Left x≤h) = void $ h≠x $ antisymmetric h≤x x≤h
              ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No _) | (Right _) | (No h≠x) | (Left _) | (No x≠r) | (No x≠h) | (Right h≤x) =
                plusSuccRightSucc _ _ \=> cong (cnt x left +) (ConsAddsOne {x} right)
        ConsAddsOne (Imbalanced h {l = l} {r = r} h≤l h≤r left right) | (No x≠h) | (Right h≤x) | (No h≠x) | (Right x≤h) = void $ x≠h $ antisymmetric x≤h h≤x

-- export
-- data HeapFamily : LinearOrder a rel => Type -> Type where
--     MkHeapFamily : Heap @{lo} {a} {rel} n h -> HeapFamily @{lo} {rel} a

-- export
-- DecEq a => LinearOrder a rel => Container a (HeapFamily {rel} a) where
--     x .#. (MkHeapFamily xs) = cnt x xs
    
--     Nil = MkHeapFamily []
--     NilIsEmpty = Refl

--     NilIsUnique {xs = (MkHeapFamily {n=0} {h=()} [])} uniq = Refl
--     NilIsUnique {xs = (MkHeapFamily {n=S m} {h} xs)} uniq = absurdity @{ui {xs=xs} {n=m} {h}} uniq

--     x :: (MkHeapFamily xs) = MkHeapFamily ((x::xs) {rel})

--     ConsAddsOne {xs = (MkHeapFamily xs)} = ConsAddsOne xs

--     ConsKeepsRest {xs=MkHeapFamily []} x'≠x = let _ # p = no x'≠x in rewrite p in Refl
--     ConsKeepsRest {xs=MkHeapFamily (Singleton h)} x'≠x = ?ckr_1
--     ConsKeepsRest {xs=MkHeapFamily (Prick h s h≤s)} x'≠x = ?ckr_2
--     ConsKeepsRest {xs=MkHeapFamily (Balanced h h≤l h≤r left right)} x'≠x = ?ckr_3
--     ConsKeepsRest {xs=MkHeapFamily (Imbalanced h h≤l h≤r left right)} x'≠x = ?ckr_4

--     ConsBiinjective = MkBiinjective impl where
--         impl : {x: a} -> {xs, ys: HeapFamily {rel} a} -> Container.(::) x xs = Container.(::) y ys -> (x = y, xs = ys)

--     (MkHeapFamily xs) ++ (MkHeapFamily ys) = MkHeapFamily (xs++ys)
--     ConcNilLeftNeutral {xs=MkHeapFamily xs} = Refl
--     ConcReduces {xs=MkHeapFamily xs} {ys=MkHeapFamily ys} = ?cr

--     ContainerSized = MkSized (\(MkHeapFamily xs) => length xs)
--     SizedNil = Refl
--     SizedCons {xs=MkHeapFamily xs} = ?sc

--     Match (MkHeapFamily {rel} {n} xs) = ?match
--     Match xs = ?Match_rhs

-- export
-- fromList : (xs: List a) -> List a # HeapOf lo xs
-- fromList [] = [] # ([], reflexive @{reflexiveIsPermutationOf})
-- fromList (x :: xs) = x :: fromList xs


-- covering
-- export
-- heapSort : (as: List a) ->  DecEq a => (lo: LinearOrder a rel) => (List a) # (IsSortingOf lo as)
-- heapSort x = toList $ fromList x
