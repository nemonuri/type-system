module

public section

namespace DotNet

structure TypeDef where
  name : String
  arity : Nat
  deriving DecidableEq, Hashable


abbrev Pos := { x : Nat // 0 < x }


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

end TypeStack

end DotNet

end -- public section
