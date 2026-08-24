# checked-exceptions

A monad transformer that allows you to throw and catch a restricted set of exceptions, tracked at the type level.

Requires GHC 9.14.

## Example

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

The facilities this library provides will alert you when you have, intentionally or unintentionally, introduced a new possible exception in your code that is presently unaccounted for.
Since we enforce at the type level what kinds of exceptions are permissible, you can safely trust the exceptions set in the type signature to do something like generate OpenAPI documentation for an HTTP handler's error responses.

When catching an exception, we provide the `CaseException` type to allow coverage checking with a case-like API (`caseException`), or you can use methods provided by the `CheckedException` typeclass to perform common operations on exceptions without inspecting the type of the exception.

## Membership witnesses

`Elem` and `Contains` are type classes backed by value-level witnesses:

- `ElemIx e es` — index of `e` inside `es` (`Here` / `There`)
- `Subset es1 es2` — every element of `es1` appears in `es2` (`SubRefl`, `SubNil`, `SubCons`)
- `lookupSubset` — translate an `ElemIx` along a `Subset` witness
- `containsRefl` — reflexive `Subset es es` for abstract exception lists

`OneOf` is constructed with `oneOf`, not a data constructor pattern. The internal constructor carries an `ElemIx` witness so subset widening (`weakenOneOf`, `weakenExceptions`) is structurally total.

**Breaking change (0.3):** `Contains es es` is not auto-derived for abstract `es`. Pass an explicit witness:

```haskell
weakenExceptionsWith containsRefl (action :: CheckedExceptT es m a)
  :: CheckedExceptT es m a
```

Use duplicate-free exception lists (or `Nub` at the kind level): duplicate types pick the first `ElemIx` index.

## Plugin

**Required** for `QualifiedDo` blocks: `-fplugin Control.Monad.CheckedExcept.Plugin`.

The plugin proposes default values for ambiguous exception-list metavariables created by `>>=` in `QualifiedDo` blocks (and similar). It walks stuck `Elem e alpha` and `Contains es alpha` constraints (including implication givens in nested contexts) where `alpha` is an unfilled `[Type]` metavariable, and proposes:

1. `alpha := '[]` when there are no lower bounds (covers `lift` / `pure` / `return` in a do block)
2. `alpha := Nub (union of lower bounds)`
3. `alpha := ub` for each concrete upper bound

GHC verifies each proposal; only a solving assignment is committed. No fiat coercions are emitted. The old plugin rewrite/solve path is removed.

Optional tracing: `-fplugin-opt Control.Monad.CheckedExcept.Plugin:verbose`

`QualifiedDo` `>>=` unions exception sets with `Nub (es1 ++ es2)` in the result type so binds accumulate exceptions without ambiguous metavariables when possible.

## Deriving `CheckedException`

`DerivingVia` with `ShowException` or `ExceptionException` is supported. `fromOneOf` unwraps the newtype correctly when reading bare values from `OneOf`.

Custom `CheckedException` instances should only return `Just` from `fromOneOf` when the payload type matches `e` (same contract as the default `eqT` witness path). `withOneOf` uses that witness path directly and does not depend on a custom `fromOneOf`.
