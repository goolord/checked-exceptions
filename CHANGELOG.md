# Revision history for checked-exceptions

## 0.3.0.0 -- 2026-08-24

* Target GHC 9.14 only (`base >= 4.22`, `ghc >= 9.14`).
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
