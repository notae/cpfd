module Main where

import Test.DocTest

main :: IO ()
main = doctest [ "src/Control/CPFD.hs"
               , "src/Control/CPFD/Example/Example.hs" ]
