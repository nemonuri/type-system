/-!

# Design

## Goal

1. Extend .NET type system (System F) to System Fω
2. Enable consumers to express Fω `forall` Type Scheme

-/

inductive FωType where
  | var : Nat → FωType
  | con : String → FωType
  | arrow : FωType → FωType → FωType
  | app : FωType → FωType → FωType

def isArrow (fw: FωType) : Bool :=
  match fw with
  | .arrow _ _ => .true
  | _ => .false

/-!

## Reference

- [Typechecker Zoo](https://sdiehl.github.io/typechecker-zoo/system-f-omega/language-design.html)

-/
