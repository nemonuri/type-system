/-!

# Design

## Goal

1. Extend .NET type system (System F) to System Fω
2. Enable consumers to express Fω `forall` Type Scheme

-/

inductive Kind where
  | star : Kind
  | arrow : Kind → Kind → Kind
  deriving Repr, DecidableEq, BEq

/-- Canon Fω Type -/
inductive Canon : Kind → Type 0 where
  | star : String → Canon .star
  | arrow : (pk: Kind) → (pc: Canon pk) → (qk: Kind) → (qc: Canon qk) → Canon (.arrow pk qk)
  deriving Repr, DecidableEq, BEq

/-- Surface Fω Type -/
inductive Surface : (k: Kind) → Canon k → Type 0 where
  | star : (s: String) → Surface (Kind.star) (Canon.star s)
  | arrow :
      (pk: Kind) → (pc: Canon pk) →
      (qk: Kind) → (qc: Canon qk) →
      (apply: Canon pk → Surface qk qc) →
      Surface (Kind.arrow pk qk) (Canon.arrow pk pc qk qc)

set_option linter.unusedVariables false
def toCanon {k: Kind} {canon: Canon k} (st: Surface k canon) : Canon k := canon
set_option linter.unusedVariables true

inductive App
  (pk: Kind) (pc: Canon pk) (qk: Kind) (qc: Canon qk)
  (fn: Surface (Kind.arrow pk qk) (Canon.arrow pk pc qk qc))
  (arg: Surface pk pc)
where
  | mk : App pk pc qk qc fn arg


def eval {pk pc qk qc fn arg} (app: App pk pc qk qc fn arg) : Surface qk qc :=
  match fn with
  | .arrow _ _ _ _ apply => apply (toCanon arg)


/-!

## Reference

- [Typechecker Zoo](https://sdiehl.github.io/typechecker-zoo/system-f-omega/language-design.html)

-/
