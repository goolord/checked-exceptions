# Revision history for checked-exceptions

## Unreleased

* `QualifiedDo` `>>=` / `>>` check each side with `Contains` instead of requiring the result to equal `Nub (es1 ++ es2)`: declared exceptions may be in any order and may include exceptions that are never thrown.
* `Elem` errors name the full declared list (`Char is not a member of [(), Int, Bool, String]`) instead of `'[]`.
* `Elem`'s tail instance is no longer `INCOHERENT`; the plugin solves constraints instance resolution can't decide (e.g. `Elem (E a) '[E Int]`, `Elem Int (x ': '[Int])`).
* Fix the plugin's defaulting never firing (it compared exception-list kinds against a promoted list type), so e.g. a trailing `pure ()` in a `QualifiedDo` block now type checks.
* `weakenExceptionsWith` forces its `Subset` witness, so a deferred type error in it surfaces when the action runs.

## 0.3.0.0 -- 2026-08-24

* **Breaking:** `Control.Monad.CheckedExcept.Plugin` moved to the `checked-exceptions:plugin` sublibrary; add `checked-exceptions:plugin` to `build-depends`.
* Support GHC 9.8+ for the core library (`base >= 4.16`). Plugin sublibrary requires GHC 9.10+ with matching `ghc` (9.10 / 9.12 / 9.14; not `ghc-lib`).
* `OneOf`: hide data constructor; construct with `oneOf`. Payload carries an `ElemIx` witness.
* `Elem` and `Contains` are now classes producing `ElemIx` / `Subset` witnesses instead of vacuous type families.
* `Contains es es` is no longer auto-derived for abstract `es`; use `containsRefl` or `weakenExceptionsWith`.
* Export `ElemIx`, `Subset`, `lookupSubset`, `containsRefl`, `weakenExceptionsWith`, `weakenOneOfWith`.
* Fix `QualifiedDo` `>>=` so the continuation can return a different type (`b` not `a`).
* Replace the type-checker plugin's fiat coercions with a `defaultingPlugin` that proposes exception-set metavariable defaults.
* Remove `unsafeCoerceConstraint` / unsound `proveElem` widening.
* Drop `ghc-tcplugins-extra` dependency.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
