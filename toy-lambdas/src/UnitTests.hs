module UnitTests
  ( Test (..)
  , Result (..)
  , Results (..)
  , runTest
  , runTests) where

import Control.Monad (foldM)

data Test a = Test { expected :: a, actual :: a, message :: String }
  deriving Show

data Result a = Result { test :: (Test a)
                       , pass :: Bool
                       } deriving Show

data Results a = Results { results :: [Result a]
                         , failed :: Int
                         } deriving Show

runTest :: (Eq a, Show a) => Test a -> Result a
runTest t = Result t $ (expected t) == (actual t)

testResults :: (Eq a, Show a) => [Test a] -> Results a
testResults [] = Results [] 0
testResults (t : ts) = let r  = runTest t
                           rs = testResults ts
                     in Results (r : results rs) ((failed rs) + (if pass r then 0 else 1))


printResults :: (Show a) => Results a -> IO ()
printResults rs = let total = length (results rs)
                      fail = failed rs
                      passed = total - fail
                      perc = 100.0 * (fromIntegral passed) / (fromIntegral total)
                      printResult x r =
                        if not (pass r) then let exp = show $ expected (test r)
                                                 act = show $ actual (test r)
                                                 msg = message (test r)
                                             in do putStrLn $ "[-] " ++ msg
                                                   putStrLn $ "    Expected: " ++ exp ++ "\n    Actual:   " ++ act
                                        else return x
                   in do putStrLn $ "Passed " ++ (show passed) ++ " / " ++ (show total) ++ " tests (" ++ show perc ++ "%)."
                         putStrLn $ "Failed " ++ (show fail) ++ " tests."
                         foldM printResult () (results rs)

runTests :: (Eq a, Show a) => [Test a] -> IO()
runTests = printResults . testResults
