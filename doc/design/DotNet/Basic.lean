module

import Mathlib.Logic.Basic

public section

namespace DotNet

structure TypeDef where
  name : String
  arity : Nat
  deriving DecidableEq, Hashable

abbrev Pos := { x : Nat // 0 < x }

namespace Pos

def mk (x: Nat) (p: 0 < x) : Pos := ⟨x, p⟩

end Pos


namespace Api

def System_Tuple : TypeDef := TypeDef.mk "System.Tuple" 0

def System_Tuple' (arity: Pos) : TypeDef :=
  let name := "System.Tuple`" ++ (toString arity.val)
  TypeDef.mk name arity.val

end Api

instance : Inhabited TypeDef where
  default := Api.System_Tuple

mutual
  inductive TypeStack : (remainedCount: Nat) → Type 0 where
    | alloc : (typeDef: TypeDef) → TypeStack typeDef.arity
    | push :
        (remainingCount: Pos) →
        (predecessor: TypeStack remainingCount.val) →
        (item: TypeSpec) →
        TypeStack (remainingCount.val - 1)

  inductive TypeSpec where
    | var : TypeSpec
    | con : (TypeStack 0) → TypeSpec
end

namespace TypeStack

def default (rc: Nat) : TypeStack rc :=
  let rc_pos := rc > 0
  Decidable.byCases
    (fun h1: rc_pos =>
      TypeStack.alloc (Api.System_Tuple' (Pos.mk rc h1)))
    (fun h2: ¬rc_pos =>
      have lemma1 : Api.System_Tuple.arity = rc := by
        calc
          Api.System_Tuple.arity = 0 := by rfl
          0 = rc := by omega
      have lemma2 := congrArg TypeStack lemma1
      TypeStack.alloc Api.System_Tuple
      |> cast lemma2)




abbrev Indexless := Sigma TypeStack

namespace Indexless

def ofIndexed {rc: Nat} (tst: TypeStack rc) : Indexless := Sigma.mk rc tst

def remainedCount (tst: Indexless) : Nat := tst.fst

def toIndexed (tst: Indexless) : TypeStack tst.remainedCount := tst.snd

def default (rc: Nat) : Indexless := TypeStack.default rc |> ofIndexed

@[simp]
theorem default_eq_sigma (rc: Nat) : default rc = Sigma.mk rc (TypeStack.default rc) := by rfl

@[simp]
theorem default_eq_imp_rc_eq
  {rc1 rc2: Nat}
  (default_eq: (default rc1) = (default rc2))
  : rc1 = rc2 := by
  simp at default_eq
  exact default_eq.left

theorem default_congr (rc: Nat)
  : (default rc).toIndexed ≍ (TypeStack.default rc) := by
  rfl

end Indexless

/-
theorem default_heq_imp_rc_eq
  {rc1 rc2: Nat}
  (default_eq: (default rc1) ≍ (default rc2))
  : rc1 = rc2 := by
  induction rc1 with
  | zero =>
    induction rc2 with
    | zero => rfl
    | succ n₁_₂ ih₁_₂ =>
      unfold default cast Pos.mk Decidable.byCases at default_eq
      simp at default_eq
      unfold Nat.decLt Nat.decLe at default_eq
      simp at default_eq
      unfold Api.System_Tuple Api.System_Tuple' at default_eq
      simp at default_eq
-/












--def heq_rec {rc1 rc2: Nat} := (HEq (TypeStack rc1) (TypeStack rc2)).rec



/-
theorem heq_imp_rc_eq
  {rc1 rc2: Nat} {tst1: TypeStack rc1} {tst2:TypeStack rc2}
  (is_heq: tst1 ≍ tst2)
  : rc1 = rc2 := by
  have lemma1 := is_heq |> type_eq_of_heq
  match rc1, rc2 with
  | 0, n + 1 =>
  --have heq_motive {rc₀} (tst₀: TypeStack rc₀) (heq₀: tst1 ≍ tst₀) : rc1 = rc₀ := by
-/







/-
  let lhs := TypeStack.default rc1
  let rhs := TypeStack.default rc2
  have default_heq₁ : lhs ≍ rhs := default_heq
  unfold lhs at default_heq₁
  unfold TypeStack.default at default_heq₁
  unfold Decidable.byCases at default_heq₁
  simp_all
  split at default_heq₁
  next rc1_pos _ =>
    unfold rhs TypeStack.default Decidable.byCases at default_heq₁
    simp_all
    split at default_heq₁
-/


end TypeStack









instance {rc: Nat} : Inhabited (TypeStack rc) where
  default := TypeStack.default rc

namespace TypeStack

def toIndex {rc} (_: TypeStack rc) := rc

def ofIndex (rc: Nat) : TypeStack rc := Inhabited.default

theorem ofIndex_toIndex (rc: Nat) : (ofIndex rc).toIndex = rc := by rfl

def remainedCount {rc: Nat} (tst: TypeStack rc) : { x : Nat // x = rc } :=
  match tst with
  | .alloc td =>
    Subtype.mk td.arity (by rfl)
  | .push rc₂ _ _ =>
    Subtype.mk (rc₂.val - 1) (by rfl)

theorem remainedCount_typeStack_eq {rc: Nat} (tst: TypeStack rc) : rc = tst.remainedCount.val := by
  unfold remainedCount
  split
  next => simp
  next => simp

@[expose]
abbrev pushAuto {rc: Pos} (tst: TypeStack rc) (tsp: TypeSpec) : TypeStack (rc.val - 1) :=
  TypeStack.push rc tst tsp

def typeDef {rc: Nat} (tst: TypeStack rc) : TypeDef :=
  match tst with
  | .alloc td => td
  | .push _ pred _ => pred.typeDef

@[simp]
theorem typeDef_is_invariant {rc: Pos} (tst: TypeStack rc) (tsp: TypeSpec)
  : (tst.pushAuto tsp).typeDef = tst.typeDef := by
  rfl

def capacity {rc: Nat} (tst: TypeStack rc) : Nat := tst.typeDef.arity


  --conv at lemma4 =>
  --  lhs
  --have lemma5 := HEq.subst is_heq lemma4
  --have lemma5 : tst1.remainedCount.val = tst2.remainedCount.val := by
  --conv at lemma4 =>
    --lhs


/-
  have lemma_eq1 {rc₀} (tst₀: TypeStack rc₀) := tst₀.remainedCount_typeStack_eq
  rw [lemma_eq1 tst1, lemma_eq1 tst2]
  let lemma_eq2 {rc₀} (tst₀: TypeStack rc₀) := lemma_eq1 tst₀ |> congrArg TypeStack
  let cast_self {rc₀} (tst₀: TypeStack rc₀) := tst₀ |> cast (lemma_eq2 tst₀)
  have lemma_cast_self_heq {rc₀} (tst₀: TypeStack rc₀) : tst₀ ≍ cast_self tst₀ := by
    unfold cast_self
    have lemma1 := cast_heq (lemma_eq2 tst₀) tst₀
    exact lemma1.symm
  have lemma1 : cast_self tst1 ≍ cast_self tst2 :=
    is_heq.trans (lemma_cast_self_heq tst2) |> HEq.trans (lemma_cast_self_heq tst1).symm
  --obtain ⟨v1, p1⟩ := tst1.remainedCount
  obtain ⟨v2, p2⟩ := tst2.remainedCount
  have type_eq := type_eq_of_heq lemma1
-/


/-
  let tsrc1 := TypeStack.remainedCount (rc := rc1)
  let tsrc2 := TypeStack.remainedCount (rc := rc2)
  have lemma_trsc_heq : tsrc1 ≍ tsrc2 := by
    unfold tsrc1 tsrc2
    unfold TypeStack.remainedCount
-/
  --have lemma1 (rc_heq: tst1.remainedCount ≍ tst2.remainedCount) : (tst1.remainedCount.val = rc1) ↔ (tst2.remainedCount.val = rc2) := by
  --  subst_eqs


  --suffices lemma1 : (tst1.remainedCount.val = rc1) ↔ (tst2.remainedCount.val = rc2) from by
    --obtain ⟨mp, mpr⟩ := lemma1
    --have lemma2 := is_heq.elim tst1.remainedCount.property
/-
    unfold remainedCount at lemma1
    split at lemma1
    next =>
      simp at lemma1
      split at lemma1
      next =>





      next => simp at lemma1; exact lemma1
    next =>
      simp at lemma1
      split at lemma1
      next => simp at lemma1; exact lemma1
      next => simp at lemma1; exact lemma1
-/
  --congr

set_option pp.proofs true in
#print HEq.rec

theorem teststset
  (tycon: Nat → Type 0)
  (n1 n2: Nat)
  (inst1: tycon n1) (inst2: tycon n2)
  --(toIndex: (n: Nat) → (inst: tycon n) → Nat)
  --(toIndex_is_bij: ∀ (n: Nat) (inst: tycon n), toIndex n inst = n)
  (inst_heq: inst1 ≍ inst2)
  : (n1 = n2) :=
  let heq_α :=



theorem type_eq_imp_rc_eq {rc1 rc2: Nat} (type_eq: TypeStack rc1 = TypeStack rc2) : (rc1 = rc2) := by
  let getRc {rc₀: Nat} (tst₀: TypeStack rc₀) : Nat := rc₀
  sorry

  --let invTyApp {rc₀} (t₀: { x: Type 0 // x = TypeStack rc₀ }) := rc₀
  --have lemma1 := congrArg invTyApp type_eq




/-
  have lemma1 := ofIndex_toIndex rc1
  have lemma2 := ofIndex_toIndex rc2
  unfold TypeStack.ofIndex at lemma1 lemma2
-/



-- Note: (tst: TypeStack rc) 가 Data로서 존재한다는 명제만으로는, (rc: Nat) 이 Data로서 존재한다는 명제를 증명할 수 없다!





@[simp]
theorem capacity_is_invariant {rc: Pos} (tst: TypeStack rc) (tsp: TypeSpec)
  : (tst.pushAuto tsp).capacity = tst.capacity := by
  rfl

def length {rc: Nat} (tst: TypeStack rc) : Nat :=
  match tst with
  | .alloc _ => 0
  | .push _ pred _ => pred.length + 1

@[simp]
theorem length_alloc (td: TypeDef) : (TypeStack.alloc td).length = 0 := by rfl

@[simp]
theorem length_app {rc: Pos} (tst: TypeStack rc) (tsp: TypeSpec)
  : (tst.pushAuto tsp).length = tst.length + 1 := by
  rfl

@[expose]
def remainedCountPlusLength {rc: Nat} (tst: TypeStack rc) : Nat := rc + tst.length

@[simp]
theorem remainedCountPlusLength_is_invariant
  {rc: Pos} (tst : TypeStack rc) (tsp: TypeSpec)
  : (tst.pushAuto tsp).remainedCountPlusLength = tst.remainedCountPlusLength := by
  unfold remainedCountPlusLength
  simp
  omega

theorem remainedCountPlusLength_alloc_eq_capacity
  {rc: Nat} (tst: TypeStack rc) (alloc: tst matches alloc _)
  : tst.remainedCountPlusLength = tst.capacity := by
  cases tst with
  | push _ _ _ => contradiction
  | alloc td =>
      unfold remainedCountPlusLength
      unfold capacity
      simp
      rfl

@[simp]
theorem remainedCountPlusLength_eq_capacity
  {rc: Nat} (tst: TypeStack rc)
  : tst.remainedCountPlusLength = tst.capacity := by
  cases tst with
  | alloc td => simp [remainedCountPlusLength_alloc_eq_capacity]
  | push _ pred _ =>
      simp
      have lemma1 : pred.remainedCountPlusLength = pred.capacity := pred.remainedCountPlusLength_eq_capacity
      exact lemma1

theorem capacity_eq_remainedCount_plus_length
  {rc: Nat} (tst: TypeStack rc)
  : tst.capacity = rc + tst.length := by
  rw [tst.remainedCountPlusLength_eq_capacity |> Eq.symm]
  rfl

theorem remainedCount_le_capacity
  {rc: Nat} (tst: TypeStack rc)
  : rc ≤ tst.capacity := by
  have lemma1 := tst.remainedCountPlusLength_eq_capacity
  unfold remainedCountPlusLength at lemma1
  omega

theorem length_le_capacity
  {rc: Nat} (tst: TypeStack rc)
  : tst.length ≤ tst.capacity := by
  have lemma1 := tst.remainedCountPlusLength_eq_capacity
  unfold remainedCountPlusLength at lemma1
  omega

def getLast
  {rc: Nat} (tst: TypeStack rc) (i: Fin tst.length)
  : TypeSpec :=
  let .push prc pred last := tst
  let .mk index isLt := i
  match index with
  | 0 => last
  | i2 + 1 =>
      have lemma1 : i2 < pred.length := by
        simp at isLt
        exact isLt
      pred.getLast (Fin.mk i2 lemma1)


abbrev Initialized := TypeStack 0

namespace Initialized

@[simp]
theorem length_eq_capacity (tst: Initialized) : tst.length = tst.capacity := by
  simp [capacity_eq_remainedCount_plus_length]

def get (tst: Initialized) (i: Fin tst.capacity) : TypeSpec :=
  let .mk index isLt := i
  have lemma1 : tst.capacity > 0 := by omega
  let revIndex := tst.capacity - 1 - index
  have lemma2 : revIndex < tst.length := by
    simp
    omega
  tst.getLast (Fin.mk revIndex lemma2)

end Initialized

abbrev NonGeneric (rc: Nat) := { tst: TypeStack rc // tst.capacity = 0 }

namespace NonGeneric

def split {rc: Nat} (tst: TypeStack rc)
  : Sum (NonGeneric rc) { tc: TypeStack rc // tc.capacity ≠ 0 } :=
  let p := tst.capacity = 0
  Decidable.byCases
    (fun h1: p => Sum.inl ⟨tst, h1⟩)
    (fun h2: ¬p => Sum.inr ⟨tst, h2⟩)

@[simp]
theorem remainedCount_eq_zero
  {rc: Nat} (tst: NonGeneric rc)
  : rc = 0 := by
  have lemma1 := tst.val.remainedCount_le_capacity
  omega

@[simp]
theorem is_Initialized
  {rc: Nat} (tst: NonGeneric rc)
  : NonGeneric rc = NonGeneric 0 := by
  rw [tst.remainedCount_eq_zero]

def toInitialized {rc: Nat} (tst: NonGeneric rc) : NonGeneric 0 :=
  cast tst.is_Initialized tst

@[simp]
theorem length_eq_zero (tst: NonGeneric 0) : tst.val.length = 0 := by
  simp [Initialized.length_eq_capacity]
  exact tst.property

theorem not_app {rc: Nat} (tst: NonGeneric rc) : ¬(tst.val matches push ..) := by
  have lemma1 := tst.remainedCount_eq_zero
  let .mk typeStack isNonGeneric := tst
  cases typeStack with
  | alloc td => simp
  | push pred p last =>
      simp only [capacity_eq_remainedCount_plus_length] at isNonGeneric
      simp only [lemma1] at isNonGeneric
      simp only [length_app] at isNonGeneric
      contradiction -- ¬isNonGeneric : 0 + (pred.length + 1) ≠ 0

/-
theorem capacity_eq_zero_implies_not_app
  {arity: Nat} (typeStack: TypeCon arity) (capacityEqZero: typeStack.capacity = 0)
  : ¬(typeStack matches app ..) := by
  have lemma1 : typeStack.length = 0 := by apply typeStack.capacity_eq_zero_implies_length_eq_zero; assumption
-/

end NonGeneric



private def toList_aux {rc: Nat} (tst: TypeStack rc) : List TypeSpec :=
  match tst with
  | .alloc td => []
  | .push _ pred last =>
      let acc := pred.toList_aux;
      last::acc

private theorem toList_aux_length_eq_length
  {rc: Nat} (tst: TypeStack rc)
  : tst.toList_aux.length = tst.length := by
  match tst with
  | .alloc td =>
      simp only [length_alloc]
      rfl
  | .push rc pred last =>
      have lemma1 := pred.toList_aux_length_eq_length
      have lemma2 : (pred.pushAuto last).toList_aux = (last :: pred.toList_aux) := by rfl
      simp [lemma2]
      exact lemma1

namespace Initialized

def toList (typeStack: Initialized) : List TypeSpec := typeStack.toList_aux.reverse

@[simp]
theorem toList_length_eq_capacity (typeStack: Initialized) : typeStack.toList.length = typeStack.capacity := by
  unfold toList
  simp [toList_aux_length_eq_length]

def toVector (typeStack: Initialized) : Vector TypeSpec (typeStack.capacity) :=
  let result := typeStack.toList.toArray.toVector
  let fromT := typeStack.toList.toArray.size
  let toT := typeStack.capacity
  have lemma1 : fromT = toT := by
    unfold fromT toT
    simp
  have lemma2 : Vector TypeSpec fromT = Vector TypeSpec toT := by simp [lemma1]
  cast lemma2 result

end Initialized

set_option pp.proofs true in
#print HEq.rec



--set_option pp.proofs true in
set_option pp.proofs true in
theorem heq_imp_rc_eq
  {rc1 rc2: Nat} {tst1: TypeStack rc1} {tst2: TypeStack rc2}
  (is_heq: tst1 ≍ tst2)
  : rc1 = rc2 := by
  let getRc {rc₀: Nat} (tst₀: TypeStack rc₀) := rc₀
  have ht (rc1₀ rc2₀: Nat) (heq₀: rc1₀ ≍ rc2₀) : id rc1₀ = id rc2₀ := by simp_all
  sorry

/-
  match tst1 with
  | .alloc td₁ =>
    match tst2 with
    | .alloc td₂ =>
      have lemma1 := dcongr_heq
      rewrite [cas] at is_heq

  have lemma1 := ((type_eq_of_heq is_heq |> cast_heq <| tst1) |> HEq.trans <| is_heq) |> eq_of_heq
  let mtv {rc₀} (tst: TypeStack rc₀) := tst.remainedCount.val
  have lemma2 : mtv tst2 = mtv tst1 := by --congrArg mtv lemma1
    calc
      mtv tst2 = _ := congrArg mtv lemma1 |> Eq.symm
      _ = mtv tst1 := by
        unfold mtv TypeStack.remainedCount Subtype.val
        split
        next td₁ _ =>
          simp
          split
          next td₂ _ =>
            simp_all
            have lemma2 := heq_of_heq_of_eq is_heq lemma1.symm
            have mtv {rc₀} (tst1₀ tst2₀: TypeStack rc₀) : tst1₀.capacity = tst2₀.capacity := by
              simp only [capacity_eq_remainedCount_plus_length]
            have lemma3 :=
              lemma2.rec
-/

end TypeStack

end DotNet

end -- public section
