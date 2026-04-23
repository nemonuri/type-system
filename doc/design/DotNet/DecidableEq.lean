module

public import DotNet.Basic

public section

namespace DotNet

mutual

  def TypeCon.beq
    {arity1: Nat} (typeCon1: TypeCon arity1)
    {arity2: Nat} (typeCon2: TypeCon arity2)
    : Bool :=
    open TypeCon in
    match typeCon1, typeCon2 with
    | .init td1, .init td2 => td1 == td2
    | .app pred1 last1, .app pred2 last2 =>
      TypeSpec.beq last1 last2 &&
      TypeCon.beq pred1 pred2
    | _, _ => false

  def TypeSpec.beq
    (typeSpec1 typeSpec2: TypeSpec)
    : Bool :=
    match typeSpec1, typeSpec2 with
    | .var, .var => .true
    | .con tc1, .con tc2 => TypeCon.beq tc1 tc2
    | _, _ => .false

end

mutual

  def TypeCon.hash
    {arity: Nat} (typeCon: TypeCon arity)
    : UInt64 :=
    open TypeCon in
    match typeCon with
    | .init td => Hashable.hash td
    | .app pred last => mixHash (TypeSpec.hash last) (TypeCon.hash pred)

  def TypeSpec.hash
    (typeSpec: TypeSpec)
    : UInt64 :=
    match typeSpec with
    | .var => 0
    | .con tc => TypeCon.hash tc

end

instance {arity: Nat} : BEq (TypeCon arity) where
  beq tc1 tc2 := TypeCon.beq tc1 tc2

instance : BEq TypeSpec where
  beq := TypeSpec.beq

instance {arity: Nat} : Hashable (TypeCon arity) where
  hash tc := TypeCon.hash tc

instance : Hashable TypeSpec where
  hash := TypeSpec.hash

end DotNet

end -- public section
