module Main

import Sorted.MergeSort
import Sorted.Prop
import Sorted.Perm
import Sorted.Occurs
import Data.Vect
import Data.Nat
import Decidable.Equality

main : IO ()
main = do
    putStrLn $ show $ let (v # _) = mergeSort {rel=LTE} [7, 2, 3, 8, 5] in v
