module

namespace DotNet

structure TypeDef where
  name : String
  arity : Nat
  deriving BEq, Hashable, DecidableEq

end DotNet
