module

namespace DotNet

structure TypeDef where
  name : String
  arity : Nat
  deriving DecidableEq


inductive TypeSpec where
  | var : TypeSpec
  | app : (typeDef: TypeDef) → (args: List TypeSpec) → TypeSpec

end DotNet
