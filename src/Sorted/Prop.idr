module Sorted.Prop

import Data.Nat
import Data.Nat.Views

%default total

namespace Prop
    ||| Prop is a dependent pair where the dependent has quantity 0. The dependent can be thought of as a compile-time property of the first element.
    public export
    data Prop: (a: Type) -> (a -> Type) -> Type where
        (#): (f: a) -> (0 prf: p f) -> Prop a p

public export
arg : Prop a p -> a
arg (x # _) = x

||| An alternative notation for Prop
public export
(#) : (a: Type) -> (a-> Type) -> Type
(#) a f = Prop a f

export
propMap : (f: Prop a p) -> (0 m: let (x # px) = f in p x -> q x) -> (Prop a q # (\(x' # _) => let (x # _) = f in x'=x))
propMap (x # px) m = (x # m px) # Refl
