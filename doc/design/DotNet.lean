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

def generic? {α: Type} [HasArityDef α] (a: α) : MaybeGeneric α :=
  let p := HasArityDef.arityDef a > 0
  Decidable.byCases
    (fun h1 : p => MaybeGeneric.generic ⟨a, h1⟩)
    (fun h2 : ¬p => MaybeGeneric.nonGeneric ⟨a, by omega⟩)
/-
  if p then
    MaybeGeneric.generic ⟨a, p⟩
  else
    MaybeGeneric.nonGeneric a
-/

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

#check TypeSpec.rec

#check TypeCon.rec
#check TypeCon.casesOn
#check TypeCon.noConfusion
#check TypeCon.noConfusionType


def TypeCon.apply {predArity: Pos} (pred: TypeCon predArity) (last: TypeSpec) : TypeCon (predArity-1) :=
  TypeCon.app predArity pred last

def TypeCon.typeDef (arity: Nat) (typeCon: TypeCon arity) : TypeDef :=
  match typeCon with
  | init td => td
  | app _ typeCon0 _ => typeCon0.typeDef

@[simp]
theorem TypeCon.typeDef_is_invariant (predArity: Pos) (pred: TypeCon predArity) (last: TypeSpec)
  : pred.typeDef = (pred.apply last).typeDef := by
  rfl

def TypeCon.maxLength (arity: Nat) (typeCon: TypeCon arity) : Nat := typeCon.typeDef.arity

abbrev PosTypeCon (arity: Nat) := { tc: TypeCon arity // tc.maxLength > 0 }


@[simp]
theorem TypeCon.maxLength_is_invariant (predArity: Pos) (pred: TypeCon predArity) (last: TypeSpec)
  : pred.maxLength = (pred.apply last).maxLength := by
  rfl

def TypeCon.length (arity: Nat) (typeCon: TypeCon arity) : Nat :=
  match typeCon with
  | init _ => 0
  | app _ pred _ => pred.length + 1

@[simp]
theorem TypeCon.length_init (typeDef: TypeDef) : (TypeCon.init typeDef).length = 0 := by rfl

@[simp]
theorem TypeCon.length_app (predArity: Pos) (pred: TypeCon predArity) (last: TypeSpec)
  : pred.length + 1 = (pred.apply last).length := by
  rfl

def TypeCon.arity_plus_length (arity: Nat) (typeCon: TypeCon arity) : Nat := arity + typeCon.length

namespace Lemma
namespace ArityPlusLengthIsInvariant

theorem case_of_init_aux (typeDef: TypeDef) (last: TypeSpec) (_: typeDef.arity > 0)
  : (TypeCon.init typeDef).arity_plus_length = ((TypeCon.init typeDef).apply last).arity_plus_length := by
  simp


end ArityPlusLengthIsInvariant
end Lemma

--theorem TypeCon.arity_plus_length_is_invariant__case_of_init
--  (typeDef: TypeDef) (last: TypeSpec)

/-
theorem TypeCon.arity_plus_length_is_invariant
  (predArity: Pos) (pred: TypeCon predArity) (last: TypeSpec)
  : pred.arity_plus_length = (pred.apply last).arity_plus_length := by
  omega

theorem TypeCon.length_app (predArity: Pos) (pred: TypeCon predArity) (last: TypeSpec)
  : (TypeCon.app predArity pred last).length = pred.length + 1 := by
  omega

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
