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


theorem Pos.minus_one_eq_imp_eq (pos1 pos2: Pos) (minus_one_eq: pos1.val - 1 = pos2.val - 1) : pos1 = pos2 := by
  let ⟨v1, p1⟩ := pos1
  let ⟨v2, p2⟩ := pos2
  simp_all
  omega

@[simp]
theorem Pos.minus_one_eq_iff_eq (pos1 pos2: Pos) : (pos1.val - 1 = pos2.val - 1) ↔ (pos1 = pos2) := by
  have lemma_mp := minus_one_eq_imp_eq pos1 pos2
  have lemma_mpr (p: (pos1 = pos2)) : (pos1.val - 1 = pos2.val - 1) := by rw [p]
  have lemma1 := Iff.intro lemma_mp lemma_mpr
  exact lemma1



end Pos


section TypeDef

instance : BEq TypeDef := inferInstance

instance : LawfulBEq TypeDef := inferInstance

instance : LawfulHashable TypeDef := inferInstance

instance : EquivBEq TypeDef := inferInstance

#print instEquivBEqTypeDef

end TypeDef

mutual

  def TypeStack.beq_at
    {rc1 rc2: Nat} (tst1: TypeStack rc1) (tst2: TypeStack rc2) : Bool :=
    match tst1 with
    | .alloc td1 =>
      match tst2 with
      | .alloc td2 => td1 == td2
      | _ => .false
    | .push prc1 pred1 item1 =>
      match tst2 with
      | .alloc _ => .false
      | .push prc2 pred2 item2 =>
        TypeSpec.beq item1 item2 && TypeStack.beq_at pred1 pred2

  def TypeSpec.beq
    (tsp1 tsp2: TypeSpec)
    : Bool :=
    match tsp1, tsp2 with
    | .var, .var => .true
    | .con tst1, .con tst2 => TypeStack.beq_at tst1 tst2
    | _, _ => .false

end

  def TypeStack.beq {rc} (tst1 tst2: TypeStack rc) := TypeStack.beq_at tst1 tst2

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

  theorem TypeStack.rfl_at {rc: Nat} (tst: TypeStack rc) : tst == tst := by
    have lemma_beq : (tst == tst) = (tst.beq tst) := by rfl
    rw [lemma_beq]
    unfold TypeStack.beq TypeStack.beq_at
    cases tst with
    | alloc td₁ => simp
    | push rc₁ pred₁ item₁ =>
      simp
      have lemma_left : item₁.beq item₁ := TypeSpec.rfl_at item₁
      have lemma_right : pred₁.beq pred₁ := TypeStack.rfl_at pred₁
      trivial

  theorem TypeSpec.rfl_at (tsp: TypeSpec) : tsp == tsp := by
    have lemma_beq : (tsp == tsp) = (tsp.beq tsp) := by rfl
    rw [lemma_beq]
    unfold TypeSpec.beq
    cases tsp with
    | var => simp
    | con tst =>
      simp
      have lemma1 : tst.beq tst := TypeStack.rfl_at tst
      exact lemma1

end

theorem TypeStack.rfl {rc} {tst: TypeStack rc} : tst == tst := TypeStack.rfl_at tst

theorem TypeSpec.rfl {tsp: TypeSpec} : tsp == tsp := TypeSpec.rfl_at tsp

instance {rc: Nat} : ReflBEq (TypeStack rc) where rfl := TypeStack.rfl

instance : ReflBEq TypeSpec where rfl := TypeSpec.rfl


mutual

  theorem TypeStack.eq_of_beq_at
    {rc1 rc2: Nat} (tst1: TypeStack rc1) (tst2: TypeStack rc2) (is_beq_at: tst1.beq_at tst2)
    : tst1 ≍ tst2 := by
    have lemma1 := show tst1.beq_at tst2 from is_beq_at
    unfold TypeStack.beq_at at lemma1
    split at lemma1
    next td₁ =>
      split at lemma1
      next td₁_₁ _ heq₁_₁ =>
        simp at lemma1
        rewrite [lemma1]
        rfl
      next =>
        contradiction
    next rc₂ pred₂ item₂ =>
      split at lemma1
      next =>
        contradiction
      next rc₂_₂ pred₂_₂ item₂_₂ =>
        simp at lemma1
        obtain ⟨lemma_item_beq, lemma_pred_beq⟩ := lemma1
        have lemma_item_eq : item₂ = item₂_₂ := TypeSpec.eq_of_beq item₂ item₂_₂ lemma_item_beq
        have lemma_pred_eq : pred₂ ≍ pred₂_₂ := TypeStack.eq_of_beq_at pred₂ pred₂_₂ lemma_pred_beq
        have lemma_rc_eq : rc₂ = rc₂_₂ := by
          have lemma1 := lemma_pred_eq |> type_eq_of_heq
          let ⟨v1, p1⟩ := rc₂
          let ⟨v2, p2⟩ := rc₂_₂
          simp_all


        --have lemma_pred_eq :=


  theorem TypeSpec.eq_of_beq (tsp1 tsp2: TypeSpec) (is_beq: tsp1 == tsp2) : tsp1 = tsp2 := by
    sorry




end





mutual

  theorem TypeStack.hash_eq
    {rc: Nat} (tst1 tst2: TypeStack rc) (beq_true: (tst1 == tst2) = true)
    : hash tst1 = hash tst2 := by
    have lemma_typeStack_beq
      {rc₀: Nat} (tst₀1 tst₀2: TypeStack rc₀)
      : (tst₀1 == tst₀2) = (TypeStack.beq tst₀1 tst₀2) := by
      have lemma1 : (tst₀1 == tst₀2) = (TypeStack.beq tst₀1 tst₀2) := by rfl
      exact lemma1
    rewrite [lemma_typeStack_beq tst1 tst2] at beq_true
    have lemma_typeStack_hash {rc₀: Nat} (tst₀ :TypeStack rc₀)
      : hash tst₀ = TypeStack.hash tst₀ := by
      rfl
    have lemma_typeSpec_beq (tsp₀1 tsp₀2: TypeSpec)
      : (tsp₀1 == tsp₀2) = (TypeSpec.beq tsp₀1 tsp₀2) := by
      rfl
    have lemma_typeSpec_hash (tsp₀: TypeSpec) : Hashable.hash tsp₀ = TypeSpec.hash tsp₀ := by rfl
    unfold TypeStack.beq at beq_true
    cases tst1 with
    | alloc td1₁ =>
      simp at beq_true
      split at beq_true
      next _ _ td2₁_₁ _ heq₁_₁ =>
        simp at beq_true
        rewrite [beq_true.symm] at heq₁_₁
        apply heq₁_₁.symm.elim -- Note: 왜 HEq를 최대한 사용하지 말라는지, 뼈저리게 느꼈다...'꼴 맞추기'가 이렇게나 어려울 줄이야;;
        rfl
      next =>
        contradiction
    | push rc₂ pred₂ item₂ =>
      simp at beq_true
      split at beq_true
      next =>
        contradiction
      next _ rc₂_₂ pred₂_₂ item₂_₂ index_eq₂_₂ heq₂_₂ =>
        have lemma_rc_eq : rc₂_₂ = rc₂ := by
          let ⟨v1, p1⟩ := rc₂_₂
          let ⟨v2, p2⟩ := rc₂
          simp at index_eq₂_₂
          have lemma1 : v1 = v2 := by omega
          rewrite [lemma1] at p1
          simp
          exact lemma1
        suffices goal₂_₂ : TypeStack.push rc₂_₂ pred₂_₂ item₂_₂ ≍ TypeStack.push rc₂ pred₂ item₂ from by
          have lemma1 := HEq.trans heq₂_₂ goal₂_₂ |> HEq.symm
          apply lemma1.elim
          rfl
        subst_eqs
        simp_all
        /-
        goal :=
        item₂.beq item₂_₂ = true ∧ pred₂.beqAux pred₂_₂ = true ⊢ pred₂_₂ = pred₂ ∧ item₂_₂ = item₂

        ...결국 item₂ 과 pred₂ 가, 'LawfulBEq' 라는 것을 증명해야 하네...??
        -/
        sorry



        --have lemma_tsp_hash_eq := TypeSpec.hash_eq item₂ item₂_₂ beq_true.left
        --have lemma_tst_hash_eq
        --have lemma_tst_hash_eq := TypeStack.hash_eq









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
      have lemma3 (tsp: TypeSpec) : hash tsp = tsp.hash := by rfl
      by_cases ((tst1 == tst2) = true)
      next if_pos =>
        simp_all
        exact lemma2
      next if_nes =>
        have lemma4 : (tst1 == tst2) = (tst1.beq tst2) := by rfl
        rewrite [lemma4] at if_nes
        contradiction


end

end DotNet

end -- public section
