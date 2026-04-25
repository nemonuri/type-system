module

public import DotNet.Basic

public section

namespace DotNet

section Pos

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

end Pos


section TypeDef

--instance : LawfulBEq


end TypeDef

mutual

  private def TypeStack.beqAux
    {rc1: Nat} (tst1: TypeStack rc1) {rc2: Nat} (tst2: TypeStack rc2) : Bool :=
    match tst1 with
    | .alloc td1 =>
      match tst2 with
      | .alloc td2 => td1 == td2
      | _ => .false
    | .push prc1 pred1 item1 =>
      match tst2 with
      | .alloc _ => .false
      | .push prc2 pred2 item2 =>
        TypeSpec.beq item1 item2 && TypeStack.beqAux pred1 pred2

  def TypeStack.beq {rc: Nat} (tst1 tst2: TypeStack rc) := TypeStack.beqAux tst1 tst2

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
    | .alloc td => Hashable.hash td
    | .push _ pred item => mixHash (TypeSpec.hash item) (TypeStack.hash pred)

  def TypeSpec.hash
    (typeSpec: TypeSpec)
    : UInt64 :=
    match typeSpec with
    | .var => 0
    | .con tc => TypeStack.hash tc

end

instance {rc: Nat} : BEq (TypeStack rc) where
  beq tc1 tc2 := TypeStack.beq tc1 tc2

instance : BEq TypeSpec where
  beq := TypeSpec.beq

instance {arity: Nat} : Hashable (TypeStack arity) where
  hash tc := TypeStack.hash tc

instance : Hashable TypeSpec where
  hash := TypeSpec.hash

/-
mutual

  theorem TypeStack.hash_eq
    {rc: Nat} (tst1 tst2: TypeStack rc) (beq_true: (tst1 == tst2) = true)
    : hash tst1 = hash tst2 := by
    let instLhTypeDef := (inferInstance : LawfulHashable TypeDef)
    have lemma1 : (tst1 == tst2) = (TypeStack.beq tst1 tst2) := by rfl
    rewrite [lemma1] at beq_true
    unfold beq beqAux at beq_true
    unfold hash
    split
    next rc₁ tst2₁ typeDef₁ =>
      simp at beq_true
      split
      next rc2₁_₁ tst2₁_₁ typeDef₁_₁ heq₁_₁1 heq₁_₁2 =>
        split at beq_true
        next _ _ typeDef₁_₁_₁ _ heq₁_₁_₁2 =>
          simp_all








  theorem TypeSpec.hash_eq
    (typeSpec1 typeSpec2: TypeSpec)
    : Bool :=
    match typeSpec1, typeSpec2 with
    | .var, .var => .true
    | .con tc1, .con tc2 => TypeStack.beq tc1 tc2
    | _, _ => .false


end
-/


end DotNet

end -- public section
