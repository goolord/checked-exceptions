# checked-exceptins

A monad transformer that allows you to throw and catch a restricted set of exceptions, tracked at the type level

Consider the following example:

```haskell
type TestExceptions = '[(), Int, Bool, String]

testCE :: CheckedExceptT TestExceptions IO ()
testCE = CheckedExcept.do
  () <- testCE1 :: CheckedExceptT '[()] IO ()
  () <- testCE2 :: CheckedExceptT '[Int] IO ()
  () <- testCE3 :: CheckedExceptT '[Bool] IO ()
  () <- testCE4 :: CheckedExceptT '[String] IO ()
  -- () <- testCE5 :: CheckedExceptT '[Char] IO () -- doesn't compile
  pure ()

test :: CheckedExcept TestExceptions () -> IO ()
test ce = case runCheckedExcept ce of
  Left e -> do 
    applyAll (putStrLn . encodeException) e
    -- or
    withOneOf @() e $ \() -> putStrLn "()"
    withOneOf @Int e $ \n -> print $ n + 1
    withOneOf @Bool e $ \_ -> pure ()
    -- or
    caseException e
      (  (\() -> putStrLn "()")
      <: (\n -> print $ n + 1)
      <: CaseAny (\x -> putStrLn $ encodeException x)
      -- <: (\b -> putStrLn "bool")
      -- <: (\s -> putStrLn "string")
      -- <: CaseEnd
      )
  Right () -> putStrLn "Right"
```

The facilities this library provides will alert you when you have, intentionally or unintentionally, introduced a new possible exception in your code that is presently unaccounted for.
Since we enforce at the type level what kinds of exceptions are permissible, you can safely trust the exceptions set in the type signature to do something like generate OpenAPI documenation for an HTTP handler's error responses.

When catching an exception, we provide the `CaseException` type to allow coverage checking with a case-like api `caseException`, or you can use methods provided by the `CheckedException` typeclass to perform common operations on exceptions without inspecting the type of the exception.
