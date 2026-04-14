/-!

# Design

## Goal

1. Extend .NET type system (System F) to System Fω
2. Enable consumers to express Fω `forall` Type Scheme

-/

inductive Kind where
  | star : Kind
  | arrow : Kind → Kind → Kind

inductive NamedKind : Kind → Type 0 where
  | star : String → NamedKind .star
  | arrow : (pk: Kind) → (pnk: NamedKind pk) → (qk: Kind) → (qnk: NamedKind qk) → NamedKind (.arrow pk qk)

inductive CanonType : Kind → Type 0 where
  | var : String → CanonType .star
  | lam : (pk: Kind) → (qk: Kind) → (lct: CanonType pk) → (qct: CanonType qk) → CanonType (.arrow pk qk)

inductive App (pk: Kind) (qk: Kind) (lct: CanonType (.arrow pk qk)) (pct: CanonType pk) where
  | mk : App pk qk lct pct

def eval
  (pk: Kind) (qk: Kind) (lct: CanonType (.arrow pk qk)) (pct: CanonType pk)
  (app: App pk qk lct pct)
  : CanonType qk :=
  sorry


/-!

## Reference

- [Typechecker Zoo](https://sdiehl.github.io/typechecker-zoo/system-f-omega/language-design.html)

-/
