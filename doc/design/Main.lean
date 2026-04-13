/-!

# Design

## Goal

1. Extend .NET type system (System F) to System Fω
2. Enable consumers to express Fω `forall` Type Scheme

-/


inductive FωType : (rank: Nat) → Type 0 where
  | star : Nat → FωType 0
  | arrow :
      ( leftRank: Nat ) → ( lhs: FωType leftRank )
    → ( rightRank: Nat ) → ( rhs: FωType rightRank )
    → FωType (rightRank + 1)
  | app :
      ( funcRank: Nat ) → ( funcRank > 0 ) → ( func: FωType funcRank )
    → ( argRank: Nat ) → ( arg: FωType argRank )
    → FωType (funcRank - 1)






/-
inductive FωStar where
  | mk : Nat → FωStar

mutual

  inductive FωArrow where
    | mk : FωType → FωType → FωArrow

  inductive FωType where
    | star : FωStar → FωType
    | arrow : FωArrow → FωType
    | app : FωArrow → FωType → FωType


end
-/

/-!

## Reference

- [Typechecker Zoo](https://sdiehl.github.io/typechecker-zoo/system-f-omega/language-design.html)

-/
