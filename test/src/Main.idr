module Main

import Sorted.MergeSort
import Data.Nat

main : IO ()
main = do
    putStrLn $ show $ let (v # _) = mergeSort {rel=LTE} [7, 2, 3, 8, 5] in v
