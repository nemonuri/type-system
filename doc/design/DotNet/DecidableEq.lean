module

public import DotNet.Basic
public import DotNet.Lemmas

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


theorem beq_iff_eq_at.{u} (α: Type u) [BEq α] [LawfulBEq α] {a b : α} : (a == b) ↔ a = b := beq_iff_eq


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
        simp [Nat.add_assoc_symm]
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
        simp [Nat.add_assoc_symm]
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
    --obtain ⟨rc1, tst1⟩ := tst1I
    --obtain ⟨rc2, tst2⟩ := tst2I
    match arg : (tst1I, tst2I) with
    | Prod.mk (Indexless.mk rc1 tst1) (Indexless.mk rc2 tst2) =>
      simp at arg
      obtain ⟨arg1, arg2⟩ := arg
      obtain ⟨rc1i, tst1i⟩ := tst1I
      obtain ⟨rc2i, tst2i⟩ := tst2I
      obtain ⟨rc_eq1, tst_eq1⟩ := arg1
      obtain ⟨rc_eq2, tst_eq2⟩ := arg2
      simp_all
      sorry














/-
      conv at is_beq =>
        arg 1
        rw [arg1, arg2]
        simp
        congr
        next =>
          intro td1
          simp_match
-/



      --obtain ⟨arg1, arg2⟩ := arg
/-
    cases tst1 with
    | alloc td1 =>
      cases tst2 with
      | alloc td2 =>
        simp [*] at *
        congr
      | push _ _ _ =>
        conv at is_beq =>
          arg 1
          rw [lm_clone.symm]
        contradiction
    | push prc1 pred1 item1 =>
      cases tst2 with
      | alloc _ =>
        contradiction
      | push prc2 pred2 item2 =>
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
-/
  termination_by
    (sizeOf tst1I.indexed, 0)
  decreasing_by
    --obtain ⟨rc2, tst2⟩ := tst2I
    --obtain ⟨rc1, tst1⟩ := tst1I
    --unfold Indexless.beq at tst_beq
    --unfold TypeSpec.beq at tsp_beq
    --rewrite [lm_tsp_eq] at *
    rename ((tst2I : Indexless) ×' (tst1I == tst2I) = true) => tst2ISigma
    have lm_tstI_eq (tstI₀1 tstI₀2: Indexless) : (tstI₀1 == tstI₀2) = (tstI₀1.beq tstI₀2) := by rfl
    next =>
      apply Prod.Lex.left
      simp_all
      --subst_eqs
      cases item1 with
      | var => simp; exact tst1I.indexed.sizeOf_gt_zero
      | con tst1 =>
        obtain ⟨rc2ᵢ, tst2ᵢ⟩ := tst2I
        obtain ⟨rc1ᵢ, tst1ᵢ⟩ := tst1I
        simp [lm_tstI_eq] at is_beq
        simp [lm_tstI_eq] at tst2ISigma
        obtain ⟨tst2ISigma_l, is_beq_s⟩ := tst2ISigma
        obtain ⟨rc2ᵢs, tst2ᵢs⟩ := tst2ISigma_l
        simp_all
        unfold Indexless.beq at tst_beq
        simp [*] at tst_beq





    next =>
      sorry

/-
    cases tst1 with
    | alloc td1 =>
      -- contradiction - unreachable
      have lemma1 : tst1 ≍ TypeStack.alloc td1 := by trivial
      simp_all
      subst_eqs
-/



/-
      cases tst2 with
      | alloc td2 =>
        -- contradiction - unreachable
        simp_all
        subst_eqs
        rename_i cont _ _ _ _

        cases item1 with
        | var =>
          apply Prod.Lex.left
          simp
          omega
        | con tst1₁ =>
          --contradiction
          simp_all
          subst_eqs
          rename_i is_beq1 _ _ _ _ _
          have lm_tstI_eq (tstI₀1 tstI₀2: Indexless) : (tstI₀1 == tstI₀2) = (tstI₀1.beq tstI₀2) := by rfl
          have lm_td_eq : td1 = td2 := by
            simp [lm_tstI_eq] at is_beq1
            unfold Indexless.beq at is_beq1
            simp at is_beq1
            exact is_beq1
          skip

          cases item2 with
          | var => contradiction
          | con tst2₁ =>
            apply Prod.Lex.left
            simp_all
            subst_eqs
            rename_i is_beq4 _ _ is_beq3 is_beq2 is_beq1
            have lm_td_eq : td1 = td2 := by
              have lemma1 (tstI₀1 tstI₀2: Indexless) : (tstI₀1 == tstI₀2) = (tstI₀1.beq tstI₀2) := by rfl
              simp [lemma1] at is_beq4
              unfold Indexless.beq at is_beq4
              simp at is_beq4
              exact is_beq4
            simp_all
            unfold Indexless.beq at tsp_beq
            conv at is_beq =>
              lhs
            --rewrite [show type_of% is_beq4 = ((TypeStack.alloc td1).toIndexless.beq (TypeStack.alloc td2).toIndexless) by trivial] at is_beq4
            --rename ((TypeSpec.con tst1₁).beq (TypeSpec.con tst2₁) = true ∧ pred1.toIndexless.beq pred2.toIndexless = true) => is_beq₁
            --obtain ⟨pred_beq, tst₁_con_beq⟩ := is_beq₁
-/



/-

    cases item1 with
    | var =>
      apply Prod.Lex.left
      simp
      exact tst1I.indexed.sizeOf_gt_zero
    | con tst1 =>
      apply Prod.Lex.left
      simp
      cases item2 with
      | var =>
        contradiction
      | con tst2 =>
        simp
    --rewrite [show type_of% is_beq = Indexless.beq tst1I tst2I by trivial] at is_beq
    --unfold Indexless.beq at is_beq

    obtain ⟨rc1, tst1⟩ := tst1I

    obtain ⟨rc2, tst2⟩ := tst2I


    cases tst1 with
    | alloc td1 =>
      cases tst2 with
      | alloc td2 =>
        apply Prod.Lex.left
        simp
        cases item1 with
        | var =>
          simp
          omega
        | con tst1₁ =>
          simp_all
          subst_vars
          cases item2 with
          | var =>
            skip
-/
/-
    cases tst1 with
    | alloc td1 =>
      simp only [TypeSpec.mapConOrDefault_eq]

    next =>
      sorry
-/



/-
    match tst1I with
    | ⟨_, .alloc td1⟩ =>
      simp_all
      sorry
    | ⟨_, .push prc1 pred1 item1⟩ =>
      sorry
-/



  theorem TypeSpec.eq_of_beq
    {tsp1 tsp2: TypeSpec} (is_beq: tsp1 == tsp2) : tsp1 = tsp2 := by
    rewrite [show type_of% is_beq = TypeSpec.beq tsp1 tsp2 by trivial] at is_beq
    unfold TypeSpec.beq at is_beq
    cases tsp1 with
    | var =>
      cases tsp2 with
      | var => rfl
      | con _ => contradiction
    | con tst1 =>
      cases tsp2 with
      | var => contradiction
      | con tst2 =>
        simp at is_beq
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


end DotNet

end -- public section
