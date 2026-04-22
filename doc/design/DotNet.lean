module

public section

namespace DotNet

structure TypeDef where
  name : String
  arity : Nat
  deriving BEq, Hashable

abbrev Pos := { x : Nat // 0 < x }

instance : BEq Pos where
  beq p1 p2 := p1.val == p2.val

instance : Hashable Pos where
  hash p := hash p.val


class HasArityDef (α: Type) where
  arityDef : α → Nat

instance : HasArityDef TypeDef where
  arityDef td := td.arity


abbrev Generic (α: Type) [HasArityDef α] := { a: α // HasArityDef.arityDef a > 0 }

abbrev NonGeneric (α: Type) [HasArityDef α] := { a: α // HasArityDef.arityDef a = 0 }


inductive MaybeGeneric (α: Type) [HasArityDef α] where
  | generic : (Generic α) → MaybeGeneric α
  | nonGeneric : (NonGeneric α) → MaybeGeneric α

def toMaybeGeneric {α: Type} [HasArityDef α] (a: α) : MaybeGeneric α :=
  let p := HasArityDef.arityDef a > 0
  Decidable.byCases
    (fun h1 : p => MaybeGeneric.generic ⟨a, h1⟩)
    (fun h2 : ¬p => MaybeGeneric.nonGeneric ⟨a, by omega⟩)


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

instance {arity: Nat} : HasArityDef (TypeCon arity) where
  arityDef tc := tc.maxLength


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

def toVector (typeCon: TypeCon 0) : Vector TypeSpec (typeCon.typeDef.arity) :=
  let result := typeCon.toList.toArray.toVector
  let fromT := typeCon.toList.toArray.size
  let toT := typeCon.typeDef.arity
  have lemma1 : fromT = toT := by
    unfold fromT toT
    simp
    unfold maxLength
    rfl
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

end DotNet

end -- public section
