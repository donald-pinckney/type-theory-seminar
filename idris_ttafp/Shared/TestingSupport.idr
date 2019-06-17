module TestingSupport

import Result

infixl 4 ===
infixl 4 /==

infixl 4 ===?
infixl 4 /==?

export
(===) : (Show a, Eq a) => (given : a) -> (expected : a) -> Either String ()
(===) g e = if g == e
    then Right ()
    else Left $ "expected " ++ (show g) ++ " == " ++ (show e)

export
(/==) : (Show a, Eq a) => (given : a) -> (expected : a) -> Either String ()
(/==) g e = if g /= e
    then Right ()
    else Left $ "expected " ++ (show g) ++ " /= " ++ (show e)

export
(===?) : (Show a, Eq a) => (given : Result a) -> (expected : a) -> Either String ()
(===?) (Right g) e = if g == e
    then Right ()
    else Left $ "expected " ++ (show g) ++ " == " ++ (show e)
(===?) (Left err) e = Left $ "Error: " ++ err


export
(/==?) : (Show a, Eq a) => (given : Result a) -> (expected : a) -> Either String ()
(/==?) (Right g) e = if g /= e
    then Right ()
    else Left $ "expected " ++ (show g) ++ " /= " ++ (show e)
(/==?) (Left err) e = Left $ "Error: " ++ err


-- export

%access public export

-- syntax [expr] "===?" [expected] = eq_test_try_impl "expr" expr expected

export
expectFail : Show a => Result a -> Either String ()
expectFail input =
    case input of
        Right output => Left $ "Unexpected success: " ++ show output
        Left err => Right ()

runTests : List (Either String ()) -> IO (Nat)
runTests [] = pure Z
runTests (Left str :: ts) = do
    putStrLn $ "Test failed: " ++ str
    n <- runTests ts
    pure $ S n
runTests (Right () :: ts) = runTests ts

export
makeTest : List (Either String ()) -> IO ()
makeTest tests = do
    putStrLn "\nRunning tests..."
    let numTests = length tests
    numFail <- runTests tests
    let numCorrect = numTests `minus` numFail
    putStrLn $ "===============\n" ++ (show numCorrect) ++ " / " ++ (show numTests) ++ " tests passed"
