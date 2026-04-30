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


instance : BEq TypeDef := inferInstance

instance : LawfulBEq TypeDef := inferInstance

instance : LawfulHashable TypeDef := inferInstance

instance : EquivBEq TypeDef := inferInstance


theorem TypeStack.Indexless.indexed_eq
  (tstI: Indexless)
  : tstI.indexed = (match tstI with | .mk _ tst => tst) := by
  rfl

-- Note: 왜 함수 안에 직접 `sizeOf` 를 사용할 수 없는건데??
@[expose]
def TypeSpec.mapConOrDefault.{u} {α: Sort u}
  (tsp: TypeSpec)
  (mapFunc: TypeStack 0 → α) (fallback: α)
  : α :=
  match tsp with
  | .var => fallback
  | .con tst => mapFunc tst

theorem TypeSpec.mapConOrDefault_eq.{u} {α: Sort u} tsp mapFunc (fallback: α)
  : TypeSpec.mapConOrDefault tsp mapFunc fallback
    = (match tsp with | .var => fallback | .con tst => mapFunc tst) := by
  rfl

section extra_simp

attribute [simp] TypeSpec.mapConOrDefault_eq

mutual

open TypeStack

  def TypeStack.Indexless.beq
    (tstI1: Indexless) (tstI2: Indexless) : Bool :=
    let ⟨rc1, tst1⟩ := tstI1
    let ⟨rc2, tst2⟩ := tstI2
    match tst1 with
    | .alloc td1 =>
      match tst2 with
      | .alloc td2 => td1 == td2
      | _ => .false
    | .push prc1 pred1 item1 =>
      match tst2 with
      | .alloc _ => .false
      | .push prc2 pred2 item2 =>
        TypeSpec.beq item1 item2 &&
        TypeStack.Indexless.beq pred1.toIndexless pred2.toIndexless
  termination_by
    (sizeOf tstI1.indexed, 0)
  decreasing_by
    simp
    next =>
      split
      next =>
        simp
        decreasing_with omega
      next =>
        simp
        decreasing_with omega
    next =>
      unfold TypeStack.toIndexless -- Note: '보이지 않는 Term' 에서 다름이 있었다..!
      decreasing_with omega


  def TypeSpec.beq
    (tsp1 tsp2: TypeSpec)
    : Bool :=
    match tsp1, tsp2 with
    | .var, .var => .true
    | .con tst1, .con tst2 => TypeStack.Indexless.beq tst1.toIndexless tst2.toIndexless
    | _, _ => .false
  termination_by
    (tsp1.mapConOrDefault sizeOf 0, 1)
  decreasing_by
    decreasing_with omega

end

instance : BEq TypeStack.Indexless where
  beq := TypeStack.Indexless.beq

instance : BEq TypeSpec where
  beq := TypeSpec.beq


mutual


open TypeStack

  def TypeStack.Indexless.hash
    (tstI: Indexless)
    : UInt64 :=
    let ⟨_, tst⟩ := tstI
    match tst with
    | .alloc td => Hashable.hash td
    | .push _ pred item => mixHash (TypeSpec.hash item) (TypeStack.Indexless.hash pred.toIndexless)
  termination_by
    (sizeOf tstI.indexed, 0)
  decreasing_by
    simp
    next =>
      split
      next => simp; decreasing_with omega
      next =>
        simp [←Nat.add_assoc]
        decreasing_with omega
    next =>
      simp
      unfold TypeStack.toIndexless
      decreasing_with omega


  def TypeSpec.hash
    (tsp: TypeSpec)
    : UInt64 :=
    match tsp with
    | .var => 0
    | .con tst => TypeStack.Indexless.hash tst.toIndexless
  termination_by
    (tsp.mapConOrDefault sizeOf 0, 1)
  decreasing_by
    simp
    decreasing_with omega

end

instance : Hashable TypeStack.Indexless where
  hash := TypeStack.Indexless.hash

instance : Hashable TypeSpec where
  hash := TypeSpec.hash


mutual

open TypeStack

  theorem TypeStack.Indexless.rfl_at (tstI: Indexless) : tstI == tstI := by
    suffices goal : Indexless.beq tstI tstI from by
      exact goal
    obtain ⟨rc, tst⟩ := tstI
    unfold Indexless.beq
    cases tst with
    | alloc td => simp
    | push rc pred item =>
      simp
      exact And.intro (TypeSpec.rfl_at item) (TypeStack.Indexless.rfl_at pred.toIndexless)
  termination_by
    (sizeOf tstI.indexed, 0)
  decreasing_by
    simp
    next =>
      split
      next =>
        simp
        decreasing_with omega
      next =>
        simp [←Nat.add_assoc]
        decreasing_with omega
    next =>
      simp
      unfold TypeStack.toIndexless
      decreasing_with omega


  theorem TypeSpec.rfl_at (tsp: TypeSpec) : tsp == tsp := by
    suffices goal : tsp.beq tsp from by
      exact goal
    unfold TypeSpec.beq
    cases tsp with
    | var => simp
    | con tst =>
      simp
      have lemma1 := TypeStack.Indexless.rfl_at tst.toIndexless
      exact lemma1
  termination_by
    (tsp.mapConOrDefault sizeOf 0, 1)
  decreasing_by
    simp
    decreasing_with omega

end

instance : ReflBEq TypeStack.Indexless where
  rfl {a} := TypeStack.Indexless.rfl_at a

instance : ReflBEq TypeSpec where
  rfl {a} := TypeSpec.rfl_at a


mutual

open TypeStack

  theorem TypeStack.Indexless.eq_of_beq
    {tst1I tst2I: Indexless} (is_beq: tst1I == tst2I)
    : tst1I = tst2I := by
    rewrite [show type_of% is_beq = Indexless.beq tst1I tst2I by trivial] at is_beq
    unfold Indexless.beq at is_beq
    match meq1_1 : tst1I, meq1_2 : tst2I with
    | Indexless.mk rc1 tst1, Indexless.mk rc2 tst2 =>
    match meq2_1 : tst1, meq2_2 : tst2 with
    | TypeStack.alloc td1, TypeStack.alloc td2 =>
      simp_all
      congr
    | TypeStack.push prc1 pred1 item1, TypeStack.push prc2 pred2 item2 =>
      simp_all
      obtain ⟨tsp_beq, tst_beq⟩ := is_beq
      have lemma1 : item1 == item2 := by exact tsp_beq
      have lm_tsp_eq := TypeSpec.eq_of_beq lemma1
      have lemma2 : pred1.toIndexless == pred2.toIndexless := by exact tst_beq
      have lm_tst_eq : pred1.toIndexless = pred2.toIndexless := TypeStack.Indexless.eq_of_beq lemma2
      unfold TypeStack.toIndexless at lm_tst_eq
      simp at lm_tst_eq
      obtain ⟨prc_val_eq, ptst_eq⟩ := lm_tst_eq
      have prc_eq := Subtype.ext prc_val_eq
      simp_all
      congr
  termination_by
    (sizeOf tst1I.indexed, 0)
  decreasing_by
    next =>
      apply Prod.Lex.left
      simp_all
      subst_eqs
      simp
      match item1 with
      | .var => simp
      | .con tst =>
        simp_all
        simp [←Nat.add_assoc]
    next =>
      apply Prod.Lex.left
      simp_all
      subst_eqs
      simp
      omega

  theorem TypeSpec.eq_of_beq
    {tsp1 tsp2: TypeSpec} (is_beq: tsp1 == tsp2) : tsp1 = tsp2 := by
    rewrite [show type_of% is_beq = TypeSpec.beq tsp1 tsp2 by trivial] at is_beq
    unfold TypeSpec.beq at is_beq
    match meq3_1 : tsp1, meq3_2 : tsp2 with
    | .var, .var => rfl
    | .con tst1, .con tst2 =>
      simp_all
      have lemma1 : tst1.toIndexless == tst2.toIndexless := by exact is_beq
      have lm_tstI_eq := TypeStack.Indexless.eq_of_beq lemma1
      unfold TypeStack.toIndexless at lm_tstI_eq
      simp at lm_tstI_eq
      congr
  termination_by
    (tsp1.mapConOrDefault sizeOf 0, 1)
  decreasing_by
    simp_all
    decreasing_with omega

end

end extra_simp

instance : LawfulBEq TypeStack.Indexless where
  eq_of_beq := TypeStack.Indexless.eq_of_beq

instance : LawfulHashable TypeStack.Indexless := inferInstance

instance : EquivBEq TypeStack.Indexless := inferInstance


instance : LawfulBEq TypeSpec where
  eq_of_beq := TypeSpec.eq_of_beq

instance : LawfulHashable TypeSpec := inferInstance

instance : EquivBEq TypeSpec := inferInstance

set_option pp.proofs true in
#print TypeStack.Indexless.eq_of_beq._mutual

end DotNet

end -- public section
