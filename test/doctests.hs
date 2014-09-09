module Main where

import Test.DocTest

main :: IO ()
main = doctest [ "src/Control/CPFD.hs"
               , "src/Control/CPFD/Internal/Queue.hs"
               , "src/Control/CPFD/Example/Example.hs"
               , "src/Control/CPFD/Example/Sudoku.hs" ]
