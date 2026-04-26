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

instance : BEq TypeDef := inferInstance

instance : LawfulBEq TypeDef := inferInstance

instance : LawfulHashable TypeDef := inferInstance

instance : EquivBEq TypeDef := inferInstance

#print instEquivBEqTypeDef

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

private theorem TypeStack.beqAux_rc
  {rc1: Nat} (tst1: TypeStack rc1) {rc2: Nat} (tst2: TypeStack rc2)
  (beqAuxIsTrue: (TypeStack.beqAux tst1 tst2) = true)
  : rc1 = rc2 := by
  sorry


mutual

  def TypeStack.hash
    {rc: Nat} (typeCon: TypeStack rc)
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
    | .con tst => TypeStack.hash tst

end

instance {rc: Nat} : BEq (TypeStack rc) where
  beq tc1 tc2 := TypeStack.beq tc1 tc2

instance : BEq TypeSpec where
  beq := TypeSpec.beq

instance {arity: Nat} : Hashable (TypeStack arity) where
  hash tc := TypeStack.hash tc

instance : Hashable TypeSpec where
  hash := TypeSpec.hash

namespace TypeStack

-- Note: hash 함수의 같음을 비교하기 위해서는, case 별 simp 를 먼저 정의해 두는 것이 편하다.

@[simp]
theorem hash_alloc (td: TypeDef) : (TypeStack.alloc td).hash = Hashable.hash td := by rfl

@[simp]
theorem hash_push {rc: Pos} (pred: TypeStack rc.val) (item: TypeSpec)
  : (pred.pushAuto item).hash = mixHash (TypeSpec.hash item) (TypeStack.hash pred) := by
  rfl

end TypeStack

namespace TypeSpec

@[simp]
theorem hash_var : TypeSpec.var.hash = 0 := by rfl

@[simp]
theorem hash_con (tst: TypeStack.Initialized) : (TypeSpec.con tst).hash = TypeStack.hash tst := by rfl

end TypeSpec

mutual

  theorem TypeStack.hash_eq
    {rc: Nat} (tst1 tst2: TypeStack rc) (beq_true: (tst1 == tst2) = true)
    : hash tst1 = hash tst2 := by
    have lemma_typeStack_beq
      {rc₀: Nat} (tst₀1 tst₀2: TypeStack rc₀)
      : (tst₀1 == tst₀2) = (TypeStack.beqAux tst₀1 tst₀2) := by
      have lemma1 : (tst₀1 == tst₀2) = (TypeStack.beq tst₀1 tst₀2) := by rfl
      unfold TypeStack.beq at lemma1
      exact lemma1
    rewrite [lemma_typeStack_beq tst1 tst2] at beq_true
    have lemma_typeStack_hash {rc₀: Nat} (tst₀ :TypeStack rc₀)
      : hash tst₀ = TypeStack.hash tst₀ := by
      rfl
    have lemma_typeSpec_beq (tsp₀1 tsp₀2: TypeSpec)
      : (tsp₀1 == tsp₀2) = (TypeSpec.beq tsp₀1 tsp₀2) := by
      rfl
    have lemma_typeSpec_hash (tsp₀: TypeSpec) : Hashable.hash tsp₀ = TypeSpec.hash tsp₀ := by rfl
    unfold TypeStack.beqAux at beq_true
    cases tst1 with
    | alloc td1₁ =>
      simp at beq_true
      split at beq_true
      next _ _ td2₁ index_eq₁ heq₁ =>
        simp at beq_true
        rewrite [beq_true.symm] at heq₁
        apply heq₁.symm.elim -- Note: 왜 HEq를 최대한 사용하지 말라는지, 뼈저리게 느꼈다...'꼴 맞추기'가 이렇게나 어려울 줄이야;;
        rfl
      next =>
        contradiction

    | push rc₂ pred₂ item₂ =>
      sorry
      /-
      have lemma1 : Hashable.hash td1 = tst2.hash := by
        match td1.arity, tst2 with
        | _, alloc td2 =>
      -/






/-
    rw [lemma2 tst1, lemma2 tst2]
    unfold TypeStack.hash
    split
    next rc₁ tst2₁ typeDef₁ =>
      simp at beq_true
      split
      next rc2₁_₁ tst2₁_₁ typeDef₁_₁ heq₁_₁1 heq₁_₁2 =>
        split at beq_true
        next _ _ typeDef₁_₁_₁ _ heq₁_₁_₁2 =>
          simp at beq_true
          subst_eqs
          apply TypeStack.noConfusion heq₁_₁1 heq₁_₁2 -- 오호라, noConfusion 을 'apply' 하는 것 만으로, 골칫거리 Heq를 해결할 수 있구나!
          intro typeDefEq
          rw [typeDefEq]
        next => contradiction
      next =>
        split at beq_true
        next =>
          simp_all
          subst_vars
          subst_eqs
-/


  theorem TypeSpec.hash_eq
    (tsp1 tsp2: TypeSpec) (beq_true: (tsp1 == tsp2) = true)
    : hash tsp1 = hash tsp2 := by
    have lemma1 : (tsp1 == tsp2) = (TypeSpec.beq tsp1 tsp2) := by rfl
    rewrite [lemma1] at beq_true
    unfold TypeSpec.beq at beq_true
    match tsp1, tsp2 with
    | .var, .var => simp
    | .con tst1, .con tst2 =>
      have lemma2 := TypeStack.hash_eq tst1 tst2
      have lemma3 (tst: TypeStack.Initialized) : TypeStack.hash tst = tst.hash := by rfl
      have lemma4 (tsp: TypeSpec) : hash tsp = tsp.hash := by rfl
      simp_all
      by_cases ((tst1 == tst2) = true)
      next if_pos =>
        simp_all
      next if_nes =>
        have lemma5 : (tst1 == tst2) = (tst1.beq tst2) := by rfl
        rewrite [lemma5] at if_nes
        contradiction






end



end DotNet

end -- public section
