module

namespace DotNet

structure TypeDef where
  name : String
  arity : Nat
  deriving BEq, Hashable

abbrev Pos := { x : Nat // 0 < x }

mutual
  inductive TypeCon : Nat → Type 0 where
    | init : (typeDef: TypeDef) → TypeCon typeDef.arity
    | app : {arity: Pos} → (prev: TypeCon arity) → (typeSpec: TypeSpec) → TypeCon (arity-1)

  inductive TypeSpec where
    | var : TypeSpec
    | con : (TypeCon 0) → TypeSpec

end


/-
inductive TypeSpecRaw where
  | var : TypeSpecRaw
  | app : (typeDef: TypeDef) → (args: List TypeSpecRaw) → TypeSpecRaw


def TypeSpecRaw.isValid (tsr: TypeSpecRaw) : Bool :=
  match tsr with
  | var => .true
  | app td args =>
      if args.length != td.arity then .false else
      List.all args TypeSpecRaw.isValid
-/

end DotNet
