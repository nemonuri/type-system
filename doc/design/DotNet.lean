module

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

inductive MaybeGeneric (α: Type) [HasArityDef α] where
  | generic : { a: α // HasArityDef.arityDef a > 0 } → MaybeGeneric α
  | nonGeneric : { a: α // HasArityDef.arityDef a = 0 } → MaybeGeneric α

def toMaybeGeneric {α: Type} [HasArityDef α] (a: α) : MaybeGeneric α :=
  let p := HasArityDef.arityDef a > 0
  Decidable.byCases
    (fun h1 : p => MaybeGeneric.generic ⟨a, h1⟩)
    (fun h2 : ¬p => MaybeGeneric.nonGeneric ⟨a, by omega⟩)


mutual
  inductive TypeCon : Nat → Type 0 where
    | init : (typeDef: TypeDef) → TypeCon typeDef.arity
    | app : (predArity: Pos) → (pred: TypeCon predArity) → (last: TypeSpec) → TypeCon (predArity-1)
    deriving Hashable

  inductive TypeSpec where
    | var : TypeSpec
    | con : (TypeCon 0) → TypeSpec
    deriving Hashable
end

namespace TypeCon

def apply {predArity: Pos} (pred: TypeCon predArity) (last: TypeSpec) : TypeCon (predArity-1) :=
  TypeCon.app predArity pred last

def typeDef (arity: Nat) (typeCon: TypeCon arity) : TypeDef :=
  match typeCon with
  | init td => td
  | app _ typeCon0 _ => typeCon0.typeDef

@[simp]
theorem typeDef_is_invariant (predArity: Pos) (pred: TypeCon predArity) (last: TypeSpec)
  : (pred.apply last).typeDef = pred.typeDef := by
  rfl

def maxLength (arity: Nat) (typeCon: TypeCon arity) : Nat := typeCon.typeDef.arity

instance {arity: Nat} : HasArityDef (TypeCon arity) where
  arityDef tc := tc.maxLength


@[simp]
theorem maxLength_is_invariant (predArity: Pos) (pred: TypeCon predArity) (last: TypeSpec)
  : (pred.apply last).maxLength = pred.maxLength := by
  rfl

def length (arity: Nat) (typeCon: TypeCon arity) : Nat :=
  match typeCon with
  | init _ => 0
  | app _ pred _ => pred.length + 1

@[simp]
theorem length_init (typeDef: TypeDef) : (TypeCon.init typeDef).length = 0 := by rfl

@[simp]
theorem length_app (predArity: Pos) (pred: TypeCon predArity) (last: TypeSpec)
  : (pred.apply last).length = pred.length + 1 := by
  rfl

def arityPlusLength (arity: Nat) (typeCon: TypeCon arity) : Nat := arity + typeCon.length

@[simp]
theorem arityPlusLength_unfold {arity: Nat} (typeCon: TypeCon arity)
  : typeCon.arityPlusLength = arity + typeCon.length := by
  rfl

@[simp]
theorem arityPlusLength_is_invariant
  (predArity: Pos)
  (pred : { a: TypeCon predArity // HasArityDef.arityDef a > 0 })
  (last: TypeSpec)
  : (pred.val.apply last).arityPlusLength = pred.val.arityPlusLength := by
  simp
  omega
/-
  let tcL := pred.val;
  let tcR := tcL.apply last;
  rw [arityPlusLength_unfold tcL]
  rw [arityPlusLength_unfold tcR]
  have lemma1 : tcL.length + 1 = tcR.length := by
    rw [tcL.length_app]
  omega
-/

/-
theorem length_le_maxLength (arity: Nat) (typeCon: TypeCon arity)
  : typeCon.length <= typeCon.maxLength := by
  let mg := toMaybeGeneric typeCon
  cases mg with
  | generic g =>
      have lemma1 : typeCon.maxLength = typeCon.typeDef.arity := by rfl
      rw [lemma1]
  | nonGeneric ng => sorry
-/

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
