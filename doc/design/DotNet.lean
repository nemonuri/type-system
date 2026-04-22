module

public section

namespace DotNet

structure TypeDef where
  name : String
  arity : Nat
  deriving DecidableEq, BEq, Hashable

abbrev Pos := { x : Nat // 0 < x }

instance : BEq Pos where
  beq p1 p2 := p1.val == p2.val

instance : Hashable Pos where
  hash p := hash p.val


mutual
  inductive TypeCon : Nat → Type 0 where
    | init : (typeDef: TypeDef) → TypeCon typeDef.arity
    | app : {predArity: Pos} → (pred: TypeCon predArity) → (last: TypeSpec) → TypeCon (predArity-1)
    deriving Hashable

  inductive TypeSpec where
    | var : TypeSpec
    | con : (TypeCon 0) → TypeSpec
    deriving Hashable
end

namespace TypeCon


def typeDef {arity: Nat} (typeCon: TypeCon arity) : TypeDef :=
  match typeCon with
  | init td => td
  | app typeCon0 _ => typeCon0.typeDef

@[simp]
theorem typeDef_is_invariant {predArity: Pos} (pred: TypeCon predArity) (last: TypeSpec)
  : (pred.app last).typeDef = pred.typeDef := by
  rfl

def maxLength {arity: Nat} (typeCon: TypeCon arity) : Nat := typeCon.typeDef.arity



@[simp]
theorem maxLength_is_invariant {predArity: Pos} (pred: TypeCon predArity) (last: TypeSpec)
  : (pred.app last).maxLength = pred.maxLength := by
  rfl

def length {arity: Nat} (typeCon: TypeCon arity) : Nat :=
  match typeCon with
  | init _ => 0
  | app pred _ => pred.length + 1

@[simp]
theorem length_init (typeDef: TypeDef) : (TypeCon.init typeDef).length = 0 := by rfl

@[simp]
theorem length_app {predArity: Pos} (pred: TypeCon predArity) (last: TypeSpec)
  : (pred.app last).length = pred.length + 1 := by
  rfl

def arityPlusLength {arity: Nat} (typeCon: TypeCon arity) : Nat := arity + typeCon.length

@[simp]
theorem arityPlusLength_is_invariant
  {predArity: Pos}
  (pred : TypeCon predArity)
  (last: TypeSpec)
  : (pred.app last).arityPlusLength = pred.arityPlusLength := by
  unfold arityPlusLength
  simp
  omega

theorem arityPlusLength_init_eq_maxLength
  {arity: Nat} (typeCon: TypeCon arity) (refiner: typeCon matches init _)
  : typeCon.arityPlusLength = typeCon.maxLength := by
  cases typeCon with
  | app _ _ => contradiction
  | init td =>
      unfold arityPlusLength
      unfold maxLength
      simp
      rfl

@[simp]
theorem arityPlusLength_eq_maxLength
  {arity: Nat} (typeCon: TypeCon arity)
  : typeCon.arityPlusLength = typeCon.maxLength := by
  cases typeCon with
  | init td => simp [arityPlusLength_init_eq_maxLength]
  | app pred last =>
      simp
      have lemma1 : pred.arityPlusLength = pred.maxLength := pred.arityPlusLength_eq_maxLength
      exact lemma1

theorem arity_le_maxLength
  {arity: Nat} (typeCon: TypeCon arity)
  : arity ≤ typeCon.maxLength := by
  have lemma1 := typeCon.arityPlusLength_eq_maxLength
  unfold arityPlusLength at lemma1
  omega

theorem length_le_maxLength
  {arity: Nat} (typeCon: TypeCon arity)
  : typeCon.length ≤ typeCon.maxLength := by
  have lemma1 := typeCon.arityPlusLength_eq_maxLength
  unfold arityPlusLength at lemma1
  omega


abbrev NonGeneric (arity: Nat) := { typeCon: TypeCon arity // typeCon.maxLength = 0 }

namespace NonGeneric

def split {arity: Nat} (typeCon: TypeCon arity)
  : Sum (NonGeneric arity) { tc: TypeCon arity // tc.maxLength ≠ 0 } :=
  let p := typeCon.maxLength = 0
  Decidable.byCases
    (fun h1: p => Sum.inl ⟨typeCon, h1⟩)
    (fun h2: ¬p => Sum.inr ⟨typeCon, h2⟩)

@[simp]
theorem arity_eq_zero
  {arity: Nat} (nonGeneric: NonGeneric arity)
  : arity = 0 := by
  have lemma1 := nonGeneric.val.arity_le_maxLength
  omega

@[simp]
theorem eq_zero
  {arity: Nat} (nonGeneric: NonGeneric arity)
  : NonGeneric arity = NonGeneric 0 := by
  rw [nonGeneric.arity_eq_zero]

def toZero {arity: Nat} (nonGeneric: NonGeneric arity) : NonGeneric 0 :=
  cast nonGeneric.eq_zero nonGeneric

@[simp]
theorem length_eq_zero (nonGeneric: NonGeneric 0) : nonGeneric.val.length = 0 := by
  have lemma1 := nonGeneric.val.length_le_maxLength
  omega


/-
theorem not_app {arity: Nat} (nonGeneric: NonGeneric arity) : ¬(nonGeneric.val matches app ..) := by
  let tc := nonGeneric.val
  let typeDef := tc.typeDef
  simp
  match tc with
  | init td =>
      have lemma1 : typeDef = td := by rfl

  | app pred last =>
      have lemma1 :=
-/

      --have lemma2 : (pred.app last).maxLength = 0 := by
      --  have lemma2_1 := maxLength_is_invariant pred last





      --have lemma2 :=  (pred.app last).arity_eq_zero






/-
theorem maxLength_eq_zero_implies_not_app
  {arity: Nat} (typeCon: TypeCon arity) (maxLengthEqZero: typeCon.maxLength = 0)
  : ¬(typeCon matches app ..) := by
  have lemma1 : typeCon.length = 0 := by apply typeCon.maxLength_eq_zero_implies_length_eq_zero; assumption
-/

end NonGeneric


private def toList_aux {arity: Nat} (typeCon: TypeCon arity) : List TypeSpec :=
  match typeCon with
  | init td => []
  | app pred last =>
      let acc := pred.toList_aux;
      last::acc

def toList (typeCon: TypeCon 0) : List TypeSpec := typeCon.toList_aux.reverse

private theorem toList_aux_length_eq_length
  {arity: Nat} (typeCon: TypeCon arity)
  : typeCon.toList_aux.length = typeCon.length := by
  match typeCon with
  | init td =>
      simp only [length_init]
      rfl
  | app pred last =>
      have lemma1 := pred.toList_aux_length_eq_length
      have lemma2 : (pred.app last).toList_aux = (last :: pred.toList_aux) := by rfl
      simp [lemma2]
      exact lemma1

@[simp]
theorem toList_length_eq_maxLength (typeCon: TypeCon 0) : typeCon.toList.length = typeCon.maxLength := by
  unfold toList
  simp [toList_aux_length_eq_length]
  have lemma1 := typeCon.arityPlusLength_eq_maxLength |> Eq.symm
  rw [lemma1]
  unfold arityPlusLength
  omega

def toVector (typeCon: TypeCon 0) : Vector TypeSpec (typeCon.maxLength) :=
  let result := typeCon.toList.toArray.toVector
  let fromT := typeCon.toList.toArray.size
  let toT := typeCon.maxLength
  have lemma1 : fromT = toT := by
    unfold fromT toT
    simp
  have lemma2 : Vector TypeSpec fromT = Vector TypeSpec toT := by simp [lemma1]
  cast lemma2 result


end TypeCon

/-

theorem TypeCon.length_le_maxLength (arity: Nat) (typeCon: TypeCon arity)
  : typeCon.length <= typeCon.maxLength := by
  sorry

def TypeCon.typeArgs (typeCon: TypeCon 0) : Vector TypeSpec (typeCon.typeDef.arity) :=
  sorry

def TypeSpec.eq (ts1 ts2: TypeSpec) : Bool :=
  match (ts1, ts2) with
  | (var, con _) | (con _, var) => .false
  | (var, var) => .true
  | (con tc1, con tc2) =>
  match (tc1, tc2) with
  | (TypeCon.init td1, TypeCon.init td2) => .false
-/

mutual

  def TypeCon.isEqv (tc1 tc2: TypeCon 0) : Bool :=
    open TypeCon in
    let s1 := NonGeneric.split tc1
    let s2 := NonGeneric.split tc2
    match (s1, s2) with
    | (.inl _, .inr _) | (.inr _, .inl _) => false
    | (.inl ng1, .inl ng2) => ng1.val.typeDef == ng2.val.typeDef
    | (.inr g1, .inr g2) =>
    match (g1.val, g2.val) with
    | (init .., app ..) | (app .., init ..) => false

/-
    let p := tc1.maxLength = tc2.maxLength
    Decidable.byCases
      (fun h1: p =>
        have lemma1 : Vector TypeSpec tc2.maxLength = Vector TypeSpec tc1.maxLength := by rw [h1];
        let v2 := tc2.toVector |> cast lemma1
        v2.isEqv tc1.toVector TypeSpec.isEqv
      )
      (fun _: ¬p => false)
-/

  def TypeSpec.isEqv (ts1 ts2: TypeSpec) : Bool :=
    match (ts1, ts2) with
    | (.var, .con _) | (.con _, .var) => false
    | (.var, .var) => true
    | (.con tc1, .con tc2) => tc1.isEqv tc2


end


end DotNet

end -- public section
