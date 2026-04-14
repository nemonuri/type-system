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
      (lct: Canon pk → Surface qk qnk) →
      Surface (Kind.arrow pk qk) (Canon.arrow pk pnk qk qnk)



/-
inductive App (pk: Kind) (qk: Kind) (lct: CanonType (.arrow pk qk)) (pct: CanonType pk) where
  | mk : App pk qk lct pct

def eval
  (pk: Kind) (qk: Kind) (lct: CanonType (.arrow pk qk)) (pct: CanonType pk)
  (app: App pk qk lct pct)
  : CanonType qk :=
  sorry
-/

/-!

## Reference

- [Typechecker Zoo](https://sdiehl.github.io/typechecker-zoo/system-f-omega/language-design.html)

-/
