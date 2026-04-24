module

public import DotNet.Basic

public section

namespace DotNet


instance : BEq Pos where
  beq p1 p2 := p1.val == p2.val

instance : Hashable Pos where
  hash p := hash p.val

instance : LawfulHashable Pos where
  hash_eq p1 p2 h := show hash p1 = hash p2 by
    simp at h
    have lemma1 (n: Nat) (p: Pos) (prf: p.val = n) : hash p = hash n := by
      have lemma1_1 : hash p = hash p.val := by rfl
      rw [lemma1_1]
      rw [prf]
    have lemma2 (p: Pos) := lemma1 p.val p (by rfl)
    rw [lemma2 p1, lemma2 p2]
    rw [h]

instance : ReflBEq Pos where rfl := by simp

instance : PartialEquivBEq Pos where
  symm h := by simp_all
  trans h1 h2 := by simp_all

instance : EquivBEq Pos := EquivBEq.mk




--namespace TypeStack.DecidableEq

--private def motive1 (rc: Nat) (_: TypeStack rc) := TypeStack rc
--theorem decon_type_eq


--end TypeStack.DecidableEq


mutual

  def TypeStack.beq
    {rc: Nat} (tst1 tst2: TypeStack rc)
    : Bool :=
    open TypeStack in
    match
      (motive := TypeStack rc → TypeStack rc → Bool)
      tst1, tst2
    with
    | .alloc td1, .alloc td2 => td1 == td2
    | .push prc1 pred1 last1, .push prc2' pred2' last2 =>
      TypeSpec.beq last1 last2 &&
      TypeStack.beq pred1 (cast (h := by sorry) pred2')
    |  _, _ => false

  def TypeSpec.beq
    (typeSpec1 typeSpec2: TypeSpec)
    : Bool :=
    match typeSpec1, typeSpec2 with
    | .var, .var => .true
    | .con tc1, .con tc2 => TypeStack.beq tc1 tc2
    | _, _ => .false

end

mutual

  def TypeStack.hash
    {arity: Nat} (typeCon: TypeStack arity)
    : UInt64 :=
    open TypeStack in
    match typeCon with
    | .init td => Hashable.hash td
    | .app pred last => mixHash (TypeSpec.hash last) (TypeStack.hash pred)

  def TypeSpec.hash
    (typeSpec: TypeSpec)
    : UInt64 :=
    match typeSpec with
    | .var => 0TypeStack
    | .con tc => TypeStack.hash tc

end

instance {arity: Nat} : BEq (TypeStack arity) where
  beq tc1 tc2 := TypeStack.beq tc1 tTypeStack

instance : BEq TypeSpec where
  beq := TypeSpec.beq

instance {arity: Nat} : Hashable (TypeStack arity) where
  hash tc := TypeStack.hash tc

instance : Hashable TypeSpec where
  hash := TypeSpec.hash

mutual

  theorem TypeStack.hashEq
    {arity: Nat} (typeCon1: TypeStack arity1)
    {arity2: Nat} (typeCon2: TypeStack arity2)
    : (typeCon1 == typeCon2) = true → hash a = hash b :=
    open TypeStack in
    match typeCon1, typeCon2 with
    | .init td1, .init td2 => td1 == td2
    | .app pred1 last1, .app pred2 last2 =>
      TypeSpec.beq last1 last2 &&
      TypeStack.beq pred1 pred2
    | _, _ => false

  theorem TypeSpec.hashEq
    (typeSpec1 typeSpec2: TypeSpec)
    : Bool :=
    match typeSpec1, typeSpec2 with
    | .var, .var => .true
    | .con tc1, .con tc2 => TypeStack.beq tc1 tc2
    | _, _ => .false


end


end DotNet

end -- public section
