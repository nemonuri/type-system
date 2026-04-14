/-!

# Design

## Goal

1. Extend .NET type system (System F) to System Fω
2. Enable consumers to express Fω `forall` Type Scheme

-/

inductive Kind where
  | star : Kind
  | arrow : Kind → Kind → Kind

/-- Canon Fω Type -/
inductive Canon : Kind → Type 0 where
  | star : String → Canon .star
  | arrow : (pk: Kind) → (pnk: Canon pk) → (qk: Kind) → (qnk: Canon qk) → Canon (.arrow pk qk)

/-- Surface Fω Type -/
inductive Surface : (k: Kind) → Canon k → Type 0 where
  | star : (s: String) → Surface (Kind.star) (Canon.star s)
  | arrow :
      (pk: Kind) → (pnk: Canon pk) →
      (qk: Kind) → (qnk: Canon qk) →
      (arrow: Canon pk → Surface qk qnk) →
      Surface (Kind.arrow pk qk) (Canon.arrow pk pnk qk qnk)

set_option linter.unusedVariables false
def toCanon {k: Kind} {canon: Canon k} (st: Surface k canon) : Canon k := canon
set_option linter.unusedVariables true

inductive App
  (pk: Kind) (pnk: Canon pk) (qk: Kind) (qnk: Canon qk)
  (fn: Surface (Kind.arrow pk qk) (Canon.arrow pk pnk qk qnk))
  (arg: Surface pk pnk)
where
  | mk : App pk pnk qk qnk fn arg


def eval {pk pnk qk qnk fn arg} (app: App pk pnk qk qnk fn arg) : Surface qk qnk :=
  match fn with
  | .arrow _ _ _ _ arrow => arrow (toCanon arg)


/-!

## Reference

- [Typechecker Zoo](https://sdiehl.github.io/typechecker-zoo/system-f-omega/language-design.html)

-/
