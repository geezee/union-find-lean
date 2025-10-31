import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

class FLikeData
  (Ctx: Type v → Type v → Type u)
  (α : (τ₁: Type v) → (τ₂: Type v) → Ctx τ₁ τ₂ → Type w)
  (τ₁ τ₂: Type v)
  (c: Ctx τ₁ τ₂)
where
  id : τ₁ = τ₂ → α τ₁ τ₂ c
  app: α τ₁ τ₂ c → τ₁ → τ₂
  update [BEq τ₁] : α τ₁ τ₂ c → τ₁ → τ₂ → α τ₁ τ₂ c

export FLikeData (id app update)

abbrev flike_ext
  {Ctx: Type v → Type v → Type u}
  {α : (τ₁: Type v) → (τ₂: Type v) → Ctx τ₁ τ₂ → Type w}
  {τ₁ τ₂: Type v}
  {c: Ctx τ₁ τ₂}
  [FLikeData Ctx α τ₁ τ₂ c]
  (f: α τ₁ τ₂ c) (g: α τ₁ τ₂ c)
:= ∀ (x: τ₁), app f x = app g x

macro:50 f:term " ≡ " g:term : term => `(flike_ext $f $g)

class FLike
  (Ctx: Type v → Type v → Type u)
  (α : (τ₁: Type v) → (τ₂: Type v) → Ctx τ₁ τ₂ → Type w)
  (τ₁ τ₂: Type v)
  (c: Ctx τ₁ τ₂)
extends FLikeData Ctx α τ₁ τ₂ c where
  id_is_id: (eq: τ₁ = τ₂) → app (id eq) x = eq.mp x
  update_same [BEq τ₁] [LawfulBEq τ₁] :
    app (update f x y) x = y
  update_diff [BEq τ₁] [LawfulBEq τ₁] :
    x₁ ≠ x₂ → app (update f x₁ y) x₂ = app f x₂

def FunCtx (_ _ : Type v) := Unit
def Fun (τ₁ τ₂: Type v) (_: FunCtx τ₁ τ₂) := τ₁ → τ₂

instance {τ₁ τ₂ : Type v} : FLike FunCtx Fun τ₁ τ₂ c where
  id := Eq.mp
  app := (· ·)
  update f x y := λ x' ↦ if x' == x then y else f x'

  id_is_id := by simp only [eq_mp_eq_cast, implies_true]
  update_same := by
    simp only [ite_eq_left_iff, Bool.not_eq_true]
    intros _ _ _ _ _ c
    rw [BEq.refl] at c
    contradiction
  update_diff := by
    simp only [ne_eq, ite_eq_right_iff]
    intros _ _ _ _ _ _ c₁ c₂;
    rw [LawfulBEq.eq_of_beq c₂] at c₁
    contradiction

class Default (τ₁ τ₂: Type v) where
  default: τ₁ → τ₂
  default_is_id: ∀ (x: τ₁), (eq: τ₁ = τ₂) → default x = eq.mp x

abbrev MapCtx (τ₁ τ₂: Type v) :=
  Σ' (_: BEq τ₁) (_: Hashable τ₁) (_: Default τ₁ τ₂), LawfulBEq τ₁ ∧ LawfulHashable τ₁

def MapType (τ₁ τ₂ : Type v) (ctx: MapCtx τ₁ τ₂) :=
  have ⟨_,_,_,_,_⟩ := ctx
  Std.HashMap τ₁ τ₂

instance
  [i₁: BEq τ₁]
  [i₂: Hashable τ₁]
  [i₃: Default τ₁ τ₂]
  [i₄: LawfulBEq τ₁]
  [i₅: LawfulHashable τ₁]
: FLike MapCtx MapType τ₁ τ₂ ⟨i₁,i₂,i₃,i₄,i₅⟩ where

  id _ := Std.HashMap.emptyWithCapacity
  app f x := f.getD x (i₃.default x)
  update f x y := f.insert x y

  id_is_id := by
    intro x eq
    rw [Default.default_is_id x eq]
    simp only [eq_mp_eq_cast, Std.HashMap.getD_emptyWithCapacity]

  update_same := by
    intros
    simp only [Std.HashMap.getD_insert_self]

  update_diff := by
    intros
    simp [Std.HashMap.getD_insert]
    intro h
    contradiction
