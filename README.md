# checked-exceptions

A monad transformer that allows you to throw and catch a restricted set of exceptions, tracked at the type level.

Requires GHC 9.8+ for the core library. The type-checker plugin (`checked-exceptions:plugin`) requires GHC 9.10+ with a matching `ghc` package.

## Example

```cabal
build-depends:
    checked-exceptions
  , checked-exceptions:plugin

ghc-options: -fplugin Control.Monad.CheckedExcept.Plugin
```

```haskell
{-# OPTIONS_GHC -fplugin Control.Monad.CheckedExcept.Plugin #-}
{-# LANGUAGE
    TypeApplications
  , DataKinds
  , StandaloneDeriving
  , DerivingVia
  , QualifiedDo
  , FlexibleInstances
#-}

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
    withOneOf @() e $ \() -> putStrLn "()"
    withOneOf @Int e $ \n -> print $ n + 1
    withOneOf @Bool e $ \_ -> pure ()
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

Intentionally or unintentionally, introducing a new possible exception in your code that is presently unaccounted for throws a typ eerror.
Since we enforce at the type level what kinds of exceptions are permissible, you can safely trust the exceptions set in the type signature to do something like generate OpenAPI documentation for an HTTP handler's error responses.

When catching an exception, we provide the `CaseException` type to allow coverage checking with a case-like API (`caseException`), or you can use methods provided by the `CheckedException` typeclass to perform common operations on exceptions without inspecting the type of the exception.

## Membership witnesses

`Elem` and `Contains` are type classes backed by value-level witnesses:

- `ElemIx e es`: index of `e` inside `es` (`Here` / `There`)
- `Subset es1 es2`: every element of `es1` appears in `es2` (`SubRefl`, `SubNil`, `SubCons`)
- `lookupSubset`: translate an `ElemIx` along a `Subset` witness
- `containsRefl`: reflexive `Subset es es` for abstract exception lists

`OneOf` is constructed with `oneOf`, not a data constructor pattern. The internal constructor carries an `ElemIx` witness so subset widening (`weakenOneOf`, `weakenExceptions`) is structurally total.

## Plugin

Required for `QualifiedDo` blocks. See the [Example](#example) for Cabal setup (`checked-exceptions:plugin` in `build-depends` plus `-fplugin`).

The plugin lives in a separate public sublibrary so the core library does not depend on `ghc`.

The plugin proposes default values for ambiguous exception-list metavariables created by `>>=` in `QualifiedDo` blocks (and similar).

GHC verifies each proposal; only a solving assignment is committed. No fiat coercions are emitted

Optional tracing: `-fplugin-opt Control.Monad.CheckedExcept.Plugin:verbose`

`QualifiedDo` `>>=` unions exception sets with `Nub (es1 ++ es2)` in the result type so binds accumulate exceptions without ambiguous metavariables when possible.

## Deriving `CheckedException`

`DerivingVia` with `ShowException` or `ExceptionException` is supported. `fromOneOf` unwraps the newtype correctly when reading bare values from `OneOf`.

Custom `CheckedException` instances should only return `Just` from `fromOneOf` when the payload type matches `e` (same contract as the default `eqT` witness path). `withOneOf` uses that witness path directly and does not depend on a custom `fromOneOf`.
