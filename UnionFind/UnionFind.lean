import UnionFind.FLike

-- This is taken from Mathlib.Data.Erased
def Erased (α : Sort u) : Sort max 1 u :=
  { s : α → Prop // ∃ a, (a = ·) = s }

-- This is taken from Mathlib.Data.Erased
@[inline]
def Erased.mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

-- This is taken from Mathlib.Data.Erased
noncomputable def Erased.out {α} : Erased α → α
  | ⟨_, h⟩ => Classical.choose h

-- This is taken from Mathlib.Data.Erased (adapted not to use Mathlib: congr_fun ↦ congrFun)
@[simp]
theorem Erased.out_mk {α} (a : α) : (Erased.mk a).out = a := by
  let h := (Erased.mk a).2;
  change Classical.choose h = a
  have := Classical.choose_spec h
  exact cast (congrFun this a).symm rfl



namespace UnionFind

namespace Data

structure Data
  (C: Type → Type → Type u)
  (α: (τ₁: Type) → (τ₂: Type) → C τ₁ τ₂ → Type w)
  (τ: Type)
where
  _c: C τ τ
  _fl: FLike C α τ τ _c
  _parent: α τ τ _c
  -- _rank: α τ Nat _c₂ -- I would like to change the arg to `(x: τ) × parent x = x`


@[simp] abbrev Data.parent {C α τ} (ufd: Data C α τ) (x: τ) : τ :=
  ufd._fl.app ufd._parent x

-- @[simp] abbrev Data.rank {C α τ} (ufd: Data C α τ) (x: τ) : Nat :=
--   ufd._fl₂.app ufd._rank x

@[simp] abbrev Data.is_root {C α τ} [BEq τ] (ufd: Data C α τ) (x: τ) : Bool :=
  ufd.parent x == x

end Data

structure UnionFind
  (C: Type → Type → Type u)
  (α: (τ₁: Type) → (τ₂: Type) → C τ₁ τ₂ → Type w)
  (τ: Type)
  [BEq τ]
extends self: Data.Data C α τ
where
  -- depth is only needed for proofs, so we erase it before compiling
  depth : Erased (τ → Nat)
  depth_root_zero: ∀ r, self.is_root r → depth.out r = 0
  -- We could force that depth = parent.depth + 1, but that forces methods like find_mut to fix a whole subtree
  -- since depth is only useful for termination checking it would be nice if its effect on the computation is minimal
  depth_parent_smaller: ∀ r, ¬ self.is_root r → depth.out (self.parent r) < depth.out r



def UnionFind.trivial {C α τ} [BEq τ] [LawfulBEq τ] (c: C τ τ) [fl: FLike C α τ τ c] : UnionFind C α τ := {
  _c := c
  _fl := fl
  _parent := fl.id rfl

  depth := Erased.mk (λ _ ↦ 0)

  depth_root_zero := by
    simp only [Data.Data.is_root, Data.Data.parent, Erased.out_mk, implies_true]

  depth_parent_smaller := by
    intros r
    simp only [Data.Data.is_root, Data.Data.parent, FLike.id_is_id, eq_mp_eq_cast, cast_eq,
               BEq.rfl, not_true_eq_false, Erased.out_mk, Nat.lt_irrefl, imp_self]
}


def UnionFind.induction
  {C α τ}
  [BEq τ]
  (uf: UnionFind C α τ)
  (motive: τ → Prop)
  (base: ∀ r, uf.is_root r → motive r)
  (ih: ∀ x, ¬ uf.is_root x → motive (uf.parent x) → motive x)
  : ∀ (r: τ), motive r
  := λ (x: τ) ↦
     if base_hyp: uf.is_root x
     then base x base_hyp
     else ih x base_hyp (uf.induction motive base ih (uf.parent x))
  termination_by r => uf.depth.out r
  decreasing_by exact uf.depth_parent_smaller r base_hyp


def UnionFind.depth_0_is_root {C α τ} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) :
  ∀ (x: τ), uf.depth.out x = 0 → uf.is_root x
  := by
    intros x x_root
    by_cases hyp: uf.parent x = x
    case pos =>
      dsimp only [Data.Data.is_root, Data.Data.parent] at hyp ⊢
      rw [hyp, beq_iff_eq]
    case neg =>
      have contra := uf.depth_parent_smaller x (by
        dsimp only [Data.Data.is_root, Data.Data.parent] at hyp ⊢;
        intro contra; rw [beq_iff_eq] at contra; rw [contra] at hyp; contradiction)
      rw [x_root] at contra
      simp only [Nat.not_lt_zero] at contra

def UnionFind.find {C α τ} [BEq τ] (uf: UnionFind C α τ) (x: τ) : τ :=
  if uf.is_root x
  then x
  else uf.find (uf.parent x)
  termination_by uf.depth.out x
  decreasing_by exact uf.depth_parent_smaller x (by assumption)


abbrev UnionFind.equiv {C α τ} [BEq τ] (uf: UnionFind C α τ) (x: τ) (y: τ) : Prop :=
  uf.find x = uf.find y

abbrev UnionFind.bequiv {C α τ} [BEq τ] (uf: UnionFind C α τ) (x: τ) (y: τ) : Bool :=
  uf.find x == uf.find y


macro:70 uf:term " ⊢ " x:term " ≃ " y:term : term => `(UnionFind.equiv $uf $x $y)
macro:70 uf:term " ⊩ " x:term " ≃ " y:term : term => `(UnionFind.bequiv $uf $x $y)

theorem UnionFind.equiv_bequiv {C α τ} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x: τ) (y: τ)
  : (uf ⊢ x ≃ y) ↔ (uf ⊩ x ≃ y)
  := by
    constructor
    all_goals simp only [UnionFind.equiv, UnionFind.bequiv, beq_iff_eq, imp_self]


theorem UnionFind.equiv_rfl {C α τ} [BEq τ] (uf: UnionFind C α τ) (x: τ)
  : uf ⊢ x ≃ x
  := by dsimp only [UnionFind.equiv]

theorem UnionFind.equiv_symm {C α} [BEq τ] (uf: UnionFind C α τ) (x: τ) (y: τ)
  : (uf ⊢ x ≃ y) → uf ⊢ y ≃ x
  := by intros hyp; dsimp [UnionFind.equiv] at hyp ⊢; rw [hyp]

theorem UnionFind.equiv_trans {C α} [BEq τ] (uf: UnionFind C α τ) (x: τ) (y: τ) (z: τ)
  : (uf ⊢ x ≃ y) → (uf ⊢ y ≃ z) → uf ⊢ x ≃ z
  := by intros hyp₁ hyp₂; dsimp [UnionFind.equiv] at hyp₁ hyp₂ ⊢; rw [hyp₁, hyp₂]

theorem UnionFind.find_root_is_id {C α} [BEq τ] (uf: UnionFind C α τ) (x: τ)
  : uf.is_root x → uf.find x = x
  := by
    intros hyp
    unfold find
    simp only [hyp, reduceIte]

theorem UnionFind.find_ans_is_root {C α} [BEq τ] (uf: UnionFind C α τ)
  : ∀ x, uf.is_root (uf.find x)
  := uf.induction (λ x ↦ uf.is_root (uf.find x))
      (by intros r hyp; rw [uf.find_root_is_id r hyp]; exact hyp)
      (by
        intros x hyp ih
        unfold find
        simp only [hyp, Bool.false_eq_true, reduceIte, ih])

theorem UnionFind.find_parent_is_find_self {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x: τ)
  : uf.find (uf.parent x) = uf.find x
  := by
      cases x_root: uf.is_root x
      case true =>
        simp only [Data.Data.is_root, beq_iff_eq] at x_root
        rw [x_root]
      case false =>
        conv => { rhs; unfold find }
        simp only [x_root, Bool.false_eq_true, reduceIte]

theorem UnionFind.parent_find_is_find_self {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x: τ)
  : uf.parent (uf.find x) = uf.find x
  := by
      have h := uf.find_ans_is_root x
      simp only [Data.Data.is_root, beq_iff_eq] at h
      exact h

theorem UnionFind.find_idempotent {C α} [BEq τ] (uf: UnionFind C α τ) (x: τ)
  : uf.find (uf.find x) = uf.find x
  := by rw [uf.find_root_is_id (uf.find x) (uf.find_ans_is_root x)]

theorem UnionFind.find_same_parents_equal {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ)
  : uf.parent x = uf.parent y → uf.find x = uf.find y
  := by
    intro hyp
    rw [←find_parent_is_find_self, hyp, find_parent_is_find_self]

theorem UnionFind.trivial_is_trivial {C α τ} [BEq τ] [LawfulBEq τ] (c: C τ τ) [FLike C α τ τ c] (x: τ)
  : (@trivial _ α _ _ _ c _).find x = x
  := by
    apply find_root_is_id
    simp [Data.Data.is_root, Data.Data.parent, trivial, FLike.id_is_id, BEq.rfl]


structure FindMutResult {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x: τ) where
  root: τ
  uf': UnionFind C α τ
  parent_is_root: uf'.parent x = root
  root_is_root: uf.is_root root
  root_stays_root: uf'.is_root root
  no_root_promotion: ∀ x, ¬ uf.is_root x → ¬ uf'.is_root x
  roots_remain: ∀ x, uf.is_root x → uf'.is_root x

def UnionFind.find_mut {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x: τ)
  : FindMutResult uf x :=
  if cond: uf.is_root x
  then {
    root := x,
    uf' := uf,
    parent_is_root := by simp only [Data.Data.is_root, Data.Data.parent, beq_iff_eq] at cond ⊢; exact cond
    root_is_root := cond,
    root_stays_root := cond,
    no_root_promotion := λ _ ↦ (·),
    roots_remain := λ _ ↦ (·)
  }
  else
    let { root, uf', parent_is_root, root_is_root, root_stays_root, no_root_promotion, roots_remain } := uf.find_mut (uf.parent x)
    {
      root := root
      uf' := {
      _c := uf'._c
      _fl := uf'._fl
      _parent := uf'._fl.update uf'._parent x root
      -- _rank :=
      --   if uf'.is_root (uf'.parent x) then uf'._rank
      --   else FLikeData.update uf'._ctx uf'._rank (uf'.parent x) 0

      depth := Erased.mk (λ y ↦ if y == x then 1 else uf'.depth.out y)

      depth_root_zero := by
        simp only [Data.Data.is_root, Data.Data.parent, Erased.out_mk, beq_iff_eq]
        intro r r_root
        by_cases hyp: r = x
        case pos =>
          rw [hyp, uf'._fl.update_same] at r_root
          rw [←r_root] at cond
          contradiction
        case neg =>
          rw [uf'._fl.update_diff (Ne.symm hyp)] at r_root
          simp only [beq_iff_eq, hyp, reduceIte]
          apply uf'.depth_root_zero
          dsimp only [Data.Data.is_root, Data.Data.parent]
          rw [r_root, BEq.refl]

      depth_parent_smaller := by
        simp only [Data.Data.parent, Data.Data.is_root, Erased.out_mk, beq_iff_eq]
        intro r r_not_root
        by_cases hyp₁: r = x
        case pos =>
          rw [hyp₁, uf'._fl.update_same] at r_not_root ⊢
          simp only [r_not_root, beq_iff_eq, BEq.rfl, reduceIte, Nat.lt_one_iff]
          apply uf'.depth_root_zero root root_stays_root
        case neg =>
          repeat rw [uf'._fl.update_diff (Ne.symm hyp₁)]
          rw [uf'._fl.update_diff (Ne.symm hyp₁)] at r_not_root
          by_cases hyp₂: uf'.parent r = x <;> unfold Data.Data.parent at hyp₂
          case pos =>
            simp only [BEq.rfl, reduceIte, beq_iff_eq, hyp₂, hyp₁]
            have qed₁ := uf'.depth_parent_smaller r
            have qed₂ := uf'.depth_parent_smaller x
            simp only [Data.Data.is_root, Data.Data.parent,
                       beq_iff_eq, r_not_root, not_false_eq_true, forall_const] at qed₁ qed₂
            specialize qed₂ (by
              have h := no_root_promotion x cond;
              simp only [Data.Data.is_root, Data.Data.parent, beq_iff_eq] at h;
              exact h)
            rw [hyp₂] at qed₁
            have qed₃ := Nat.zero_le $ uf'.depth.out (uf'._fl.app uf'._parent x)
            exact Nat.lt_of_succ_le
                    $ Nat.le_trans (Nat.succ_le_succ
                                      $ Nat.le_trans (Nat.succ_le_succ qed₃)
                                                     (Nat.succ_le_of_lt qed₂))
                                   (Nat.succ_le_of_lt qed₁)
          case neg =>
            simp only [beq_iff_eq, ↓reduceIte, hyp₂, hyp₁]
            apply uf'.depth_parent_smaller
            simp only [Data.Data.is_root, Data.Data.parent, beq_iff_eq]
            exact r_not_root
      }

      parent_is_root := by
        simp only [Data.Data.parent, FLike.update_same]

      root_is_root :=  root_is_root

      root_stays_root := by
        simp only [Data.Data.is_root, Data.Data.parent, beq_iff_eq]
        rw [uf'._fl.update_diff]
        . have qed := root_stays_root
          simp only [Data.Data.is_root, Data.Data.parent, beq_iff_eq] at qed
          exact qed
        . intro contra
          rw [contra, root_is_root] at cond
          contradiction

      no_root_promotion := by
        simp
        intro r r_not_root
        by_cases hyp: x = r
        case pos =>
          rw [hyp, uf'._fl.update_same]
          intro contra
          rw [hyp, ←contra, root_is_root] at cond
          contradiction
        case neg =>
          rw [uf'._fl.update_diff hyp]
          have qed := no_root_promotion r (by
            simp only [Data.Data.is_root, Data.Data.parent, beq_iff_eq];
            exact r_not_root)
          simp only [Data.Data.is_root, Data.Data.parent, beq_iff_eq] at qed
          exact qed

      roots_remain := by
        intros r r_root
        simp only [Data.Data.is_root, Data.Data.parent, beq_iff_eq] at roots_remain ⊢
        by_cases hyp: x = r
        case pos => rw [hyp] at cond; contradiction
        case neg =>
          rw [uf'._fl.update_diff hyp];
          apply roots_remain
          simp only [Data.Data.is_root, Data.Data.parent, beq_iff_eq] at r_root
          exact r_root
    }
  termination_by uf.depth.out x
  decreasing_by exact uf.depth_parent_smaller x (by assumption)


theorem UnionFind.find_mut_correct_root {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ)
  : ∀ x, uf.find x = (uf.find_mut x).root
  := UnionFind.find_mut.induct uf (λ x ↦ _)
      (by
        intros x x_root
        unfold find_mut
        split <;> try contradiction -- for whatever reason I can't rw [x_root]
        dsimp only
        apply uf.find_root_is_id x x_root)
      (by
        intro x x_not_root uf' p₁ p₂ p₃ p₄ huf' ih
        unfold find_mut
        split <;> try contradiction -- ditto ^
        dsimp only
        rw [←ih]
        symm
        apply uf.find_parent_is_find_self)


theorem UnionFind.find_mut_unrelated_parents_equal {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ)
  : ∀ x y, uf.find y ≠ uf.find x → (uf.find_mut x).uf'.parent y = uf.parent y
  := UnionFind.find_mut.induct uf (λ x ↦ _)
      (by 
        intros x x_root y hyp
        unfold find_mut
        split <;> try contradiction
        dsimp only)
      (by 
        intros x x_not_root uf' p₀ p₁ p₂ p₃ huf' ih y hyp
        rw [find_parent_is_find_self] at ih
        specialize ih y hyp
        unfold find_mut
        split <;> try contradiction
        dsimp only [Data.Data.parent, Data.Data.is_root, beq_iff_eq] at ih ⊢
        have hyp₂ : x ≠ y := by intro contra; rw [contra] at hyp; contradiction
        rw [(uf.find_mut (uf._fl.app uf._parent x)).uf'._fl.update_diff hyp₂]
        apply ih)

theorem UnionFind.find_mut_related_parents_are_root_or_equal {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ)
  : ∀ x y, uf.find y = uf.find x → (uf.find_mut x).uf'.parent y = uf.parent y ∨ (uf.find_mut x).uf'.parent y = uf.find x
  := UnionFind.find_mut.induct uf (λ x ↦ _)
      (by 
        intro x x_root y hyp
        left
        unfold find_mut
        split <;> try contradiction
        dsimp only)
      (by 
        intro x x_not_root uf' p₀ p₁ p₂ p₃ huf' ih y hyp
        by_cases hyp₂: x = y
        case pos =>
          right
          have qed := (uf.find_mut x).parent_is_root
          rw [hyp₂] at qed ⊢
          rw [uf.find_mut_correct_root]
          exact qed
        case neg => 
          rw [uf.find_parent_is_find_self] at ih
          specialize ih y hyp
          cases ih
          case inl ih =>
            left
            unfold find_mut
            split <;> try contradiction
            dsimp only [Data.Data.parent, Data.Data.is_root, beq_iff_eq] at ih ⊢
            rw [(uf.find_mut (uf._fl.app uf._parent x)).uf'._fl.update_diff hyp₂]; apply ih
          case inr ih =>
            right
            unfold find_mut
            split <;> try contradiction
            simp only [Data.Data.parent] at ih ⊢
            rw [(uf.find_mut (uf._fl.app uf._parent x)).uf'._fl.update_diff hyp₂]
            apply ih)

theorem UnionFind.find_mut_preserves_roots {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ)
  : ∀ y x, uf.find y = (uf.find_mut x).uf'.find y
  := uf.induction (λ y ↦ _)
      (by
        intros y y_root x
        rw [uf.find_root_is_id y y_root,
            (uf.find_mut x).uf'.find_root_is_id y $ (uf.find_mut x).roots_remain y y_root])
      (by
        intros y y_not_root ih x
        let uf' := (uf.find_mut x).uf'
        specialize ih x
        rw [uf.find_parent_is_find_self] at ih
        by_cases hyp: uf.find y = uf.find x
        case pos =>
          cases uf.find_mut_related_parents_are_root_or_equal x y hyp
          case inl hyp₂ =>
            rw [←hyp₂, find_parent_is_find_self] at ih
            apply ih
          case inr hyp₂ =>
            have xr_root' : uf'.is_root (uf.find x) := by
              have result := (uf.find_mut x).root_stays_root
              rw [←uf.find_mut_correct_root] at result
              exact result
            rw [←uf'.find_parent_is_find_self, hyp₂, uf'.find_root_is_id (uf.find x) xr_root']
            exact hyp
        case neg =>
          rw [←uf.find_mut_unrelated_parents_equal x y hyp, find_parent_is_find_self] at ih
          apply ih)

theorem UnionFind.find_mut_equiv_ufs {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ)
  : ∀ (x a b: τ), (uf ⊢ a ≃ b) ↔ ((uf.find_mut x).uf' ⊢ a ≃ b)
  := by
    unfold equiv
    intros x a b
    repeat rw [←uf.find_mut_preserves_roots]




def UnionFind.union {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ) : UnionFind C α τ :=
  let xr := uf.find x
  let yr := uf.find y
  if cond: xr == yr
  then uf
  else {
    _c := uf._c
    _fl := uf._fl
    _parent := uf._fl.update uf._parent xr yr,
    -- _rank := update uf._ctx uf._rank yr (app uf._ctx uf._rank xr + app uf._ctx uf._rank yr),

    depth := Erased.mk (λ x ↦ if uf.find x == xr then uf.depth.out x + 1 else uf.depth.out x)

    depth_root_zero := by
      simp [Data.Data.is_root, Data.Data.parent, Erased.out_mk]
      intros r r_root
      by_cases hyp₁: xr = r
      case pos =>
        rw [hyp₁, uf._fl.update_same] at r_root
        rw [r_root, hyp₁, BEq.refl] at cond
        contradiction
      case neg =>
        rw [uf._fl.update_diff hyp₁] at r_root
        have r_root : uf.is_root r := by simp [r_root]
        rw [uf.find_root_is_id r r_root]
        simp only [beq_iff_eq, (Ne.symm hyp₁), reduceIte]
        apply uf.depth_root_zero r r_root

    depth_parent_smaller := by
      simp [Data.Data.is_root, Data.Data.parent, Erased.out_mk]
      intro r r_not_root
      by_cases hyp₁: xr = r
      case pos =>
        have xr_root : uf.is_root xr := by unfold xr; apply uf.find_ans_is_root
        have yr_root : uf.is_root yr := by unfold yr; apply uf.find_ans_is_root
        rw [hyp₁, uf._fl.update_same, uf.find_root_is_id yr yr_root,
           ←hyp₁, uf.find_root_is_id xr xr_root]
        simp only [beq_iff_eq] at cond
        simp only [beq_iff_eq, (Ne.symm cond), reduceIte]
        rw [uf.depth_root_zero yr yr_root]
        simp only [Nat.zero_lt_succ]
      case neg =>
        rw [uf._fl.update_diff hyp₁] at r_not_root ⊢
        have cond₁ := uf.find_parent_is_find_self r
        simp only [Data.Data.parent] at cond₁
        rw [cond₁]
        have qed := uf.depth_parent_smaller r
        simp only [Data.Data.parent, Data.Data.is_root, beq_iff_eq,
                   r_not_root, not_false_eq_true, forall_const] at qed
        by_cases cond₂: uf.find r = xr
        all_goals simp only [cond₂, beq_iff_eq, reduceIte]
        case pos => apply Nat.succ_lt_succ qed
        case neg => apply qed
  }


theorem UnionFind.union_at_roots {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ)
  : uf.union x y = uf.union (uf.find x) (uf.find y)
  := by
    unfold union
    repeat simp only [UnionFind.find_idempotent]

theorem UnionFind.union_changes_parent_child {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ)
  : (uf.union x y).parent (uf.find x) = uf.find y
  := by
    generalize huf' : uf.union x y = uf'
    simp [union, beq_iff_eq] at huf'
    split at huf'
    case isTrue hyp =>
      simp only [beq_iff_eq] at hyp
      rw [hyp, huf']
      apply parent_find_is_find_self
    case isFalse hyp =>
      rw [←huf']
      simp only [uf._fl.update_same]

theorem UnionFind.union_preserves_parent_not_child {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ)
  : ∀ z, z ≠ uf.find x → (uf.union x y).parent z = uf.parent z
  := by
    intro z z_diff
    generalize huf' : uf.union x y = uf'
    simp only [Data.Data.parent]
    simp only [union] at huf'
    split at huf'
    case isTrue hyp => rw [huf']
    case isFalse hyp =>
      rw [←huf']
      simp only
      rw [uf._fl.update_diff (Ne.symm z_diff)]

theorem UnionFind.not_root_preserved_after_union {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ)
  : ∀ z, ¬ uf.is_root z → ¬ (uf.union x y).is_root z
  := by
    intro e e_not_root
    generalize huf' : uf.union x y = uf'
    simp [union] at huf'
    simp only [Data.Data.is_root, Data.Data.parent, beq_iff_eq] at e_not_root
    split at huf' <;> rename_i cond <;> simp at cond
    case isTrue =>
      rw [←huf']
      simp only [Data.Data.is_root, beq_iff_eq]
      exact e_not_root
    case isFalse =>
      have diff : uf.find x ≠ e := by
        intro contra
        rw [←contra] at e_not_root
        have contra₂ := uf.find_ans_is_root x
        simp at contra₂
        contradiction
      simp only [Data.Data.is_root, Data.Data.parent]
      rw [←huf']
      simp only [beq_iff_eq, FLike.update_diff diff, ne_eq]
      exact e_not_root

theorem UnionFind.union_neq_child {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ)
  : ∀ z, uf.find z ≠ uf.find x → (uf.union x y).find z = uf.find z
  := uf.induction _
    (by
      intro r r_root r_neq_x
      rw [uf.find_root_is_id r r_root] at r_neq_x ⊢
      apply find_root_is_id
      simp only [Data.Data.is_root, beq_iff_eq] at r_root ⊢
      conv => rhs; rw [←r_root]
      apply uf.union_preserves_parent_not_child x y r r_neq_x)
    (by
      intro e e_not_root ih e_neq_x
      rw [find_parent_is_find_self] at ih
      rw [←ih e_neq_x]
      conv => lhs; unfold UnionFind.find
      simp only [uf.not_root_preserved_after_union x y e e_not_root, Bool.false_eq_true, reduceIte]
      rw [uf.union_preserves_parent_not_child x y e]
      intro contra
      rw [contra, find_idempotent] at e_neq_x
      contradiction)

theorem UnionFind.union_eq_child {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ)
  : ∀ z, uf.find z = uf.find x → (uf.union x y).find z = uf.find y
  := uf.induction _
    (by
      intro r r_root hyp
      rw [uf.find_root_is_id r r_root] at hyp
      rw [hyp]
      have hyp₂ := uf.union_changes_parent_child x y
      rw [←(uf.union x y).find_parent_is_find_self, hyp₂]
      apply find_root_is_id
      generalize huf' : uf.union x y = uf'
      simp [union] at huf'
      have qed := uf.find_ans_is_root y
      simp at qed
      split at huf'
      case a.isTrue h =>
        rw [←huf']
        simp [Data.Data.is_root, Data.Data.parent]
        exact qed
      case a.isFalse h =>
        simp at h
        rw [←huf']
        simp [Data.Data.is_root, Data.Data.parent, FLike.update_diff h]
        exact qed)
    (by
      intro r r_not_root ih hyp
      rw [find_parent_is_find_self] at ih
      specialize ih hyp
      rw [←(uf.union x y).find_parent_is_find_self]
      have r_neq_xr : r ≠ uf.find x := by
        intro contra
        rw [contra] at r_not_root
        have contra₂ := uf.find_ans_is_root x
        contradiction
      rw [uf.union_preserves_parent_not_child x y r r_neq_xr]
      apply ih)

theorem UnionFind.union_correct {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ)
  : ∀ z, (uf ⊢ z ≃ x) → (uf.union x y ⊢ z ≃ y)
  := by
    unfold equiv
    intro z hyp₁
    have hyp₂ := uf.union_eq_child x y z hyp₁
    by_cases hyp₃ : uf.find x = uf.find y
    case pos =>
      unfold union
      simp [hyp₃, hyp₁]
    case neg =>
      have hyp₄ := uf.union_neq_child x y y (Ne.symm hyp₃)
      rw [hyp₄, hyp₂]


theorem UnionFind.preserves_equalities {C α} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ)
  : ∀ a b, (uf ⊢ a ≃ b) → (uf.union x y ⊢ a ≃ b)
  := by
    unfold equiv
    intros a b hyp
    by_cases uf.find a = uf.find x
    case pos h₁ => 
      rw [uf.union_eq_child x y a h₁, uf.union_eq_child x y b (hyp ▸ h₁)]
    case neg h₁ => 
      rw [uf.union_neq_child x y a h₁, uf.union_neq_child x y b (hyp ▸ h₁), hyp]


def UnionFind.from {C α τ} [BEq τ] [LawfulBEq τ] (c: C τ τ) [FLike C α τ τ c] (list: List (τ × τ)) : UnionFind C α τ :=
  match list with
  | List.nil => UnionFind.trivial c
  | List.cons (a,b) eqs => (UnionFind.from c eqs).union a b


theorem UnionFind.from_closes {C α τ} [BEq τ] [LawfulBEq τ] (c: C τ τ) [FLike C α τ τ c] (list: List (τ × τ))
  : ∀ eq ∈ list, @UnionFind.from C α τ _ _ c _ list ⊢ eq.1 ≃ eq.2
  := by 
    induction list
    case nil =>
      intro eqs contra
      simp only [List.not_mem_nil] at contra
    case cons ab eqs ih =>
      intro cd hyp
      simp only [List.mem_cons] at hyp
      unfold UnionFind.from
      cases hyp
      case inl hyp =>
        rw [hyp]
        apply (@UnionFind.from C α τ _ _ c _ eqs).union_correct ab.1 ab.2
        apply equiv_rfl
      case inr hyp =>
        apply preserves_equalities
        apply ih cd hyp


theorem UnionFind.from_is_smallest_rstc {C α τ} [BEq τ] [LawfulBEq τ] (ctx: C τ τ) [FLike C α τ τ ctx] (list: List (τ × τ)):
  ∀ (rel: τ → τ → Bool),
    (rel_refl: ∀ x, rel x x) →
    (rel_symm: ∀ {x y}, rel x y → rel y x) →
    (rel_trans: ∀ {x y z}, rel x y → rel y z → rel x z) →
    (rel_closes: ∀ ab ∈ list, rel ab.1 ab.2) →
    ∀ a b, (@UnionFind.from C α τ _ _ ctx _ list ⊢ a ≃ b) → rel a b
  :=
    have fold_equiv {a b} {uf: UnionFind C α τ} (h: uf.find a = uf.find b) : uf.equiv a b := by
      unfold equiv; apply h
    by
    intros rel rel_refl rel_symm rel_trans rel_closes
    revert list
    exact UnionFind.from.induct _
      (by
        intros rel_closes a b
        rw [UnionFind.from, equiv, trivial_is_trivial, trivial_is_trivial]
        intro h
        rw [h]
        apply rel_refl)
      (by
        intro a b eqs ih rel_closes c d hyp
        specialize ih (λ ab hyp' ↦ by
          specialize rel_closes ab
          simp [hyp'] at rel_closes
          exact rel_closes)
        unfold UnionFind.from at hyp
        generalize huf' : @UnionFind.from _ α _ _ _ ctx _ eqs = uf'
        rw [huf'] at ih hyp
        by_cases hyp₁: uf'.equiv c a <;> by_cases hyp₂: uf'.equiv d a
        case pos => exact rel_trans (ih c a hyp₁) (rel_symm (ih d a hyp₂))
        case neg =>
          unfold equiv at hyp hyp₂
          apply rel_trans (ih c a hyp₁)
          rw [uf'.union_neq_child a b d hyp₂, uf'.union_eq_child a b c hyp₁] at hyp
          apply rel_trans (rel_closes (a,b) _) (ih b d hyp)
          simp
        case pos =>
          unfold equiv at hyp hyp₁
          apply rel_trans _ (rel_symm (ih d a hyp₂))
          rw [uf'.union_eq_child a b d hyp₂, uf'.union_neq_child a b c hyp₁] at hyp
          apply rel_trans (ih c b (fold_equiv hyp)) (rel_symm (rel_closes (a,b) _))
          simp
        case neg =>
          unfold equiv at hyp hyp₁ hyp₂
          rw [uf'.union_neq_child a b d hyp₂, uf'.union_neq_child a b c hyp₁] at hyp
          apply ih c d (fold_equiv hyp))



def UnionFind.union_mut {C α τ} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ) : UnionFind C α τ :=
  let ⟨xr, uf₁, _, _, _, _, _⟩ := uf.find_mut x
  let ⟨yr, uf₂, _, _, _, _, _⟩ := uf₁.find_mut y
  uf₂.union xr yr

theorem UnionFind.union_mut_find {C α τ} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y z: τ)
  : ∀ a, (uf.union x y).find a = ((uf.find_mut z).uf'.union x y).find a
  := by
    intros a
    by_cases hyp₁: uf.find a = uf.find x
    case pos =>
      rw [uf.union_eq_child x y a hyp₁]
      repeat rw [uf.find_mut_preserves_roots] at hyp₁
      rw [(uf.find_mut z).uf'.union_eq_child x y a hyp₁, find_mut_preserves_roots]
    case neg =>
      rw [uf.union_neq_child x y a hyp₁]
      have h' := (uf.find_mut z).uf'.union_neq_child x y a (by
        repeat rw [←find_mut_preserves_roots]
        exact hyp₁)
      rw [h', find_mut_preserves_roots]

theorem UnionFind.union_mut_equiv {C α τ} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y z: τ)
  : ∀ a b, (uf.union x y ⊢ a ≃ b) ↔ ((uf.find_mut z).uf'.union x y ⊢ a ≃ b)
  := by
    intros a b
    unfold equiv
    repeat rw [←uf.union_mut_find]

theorem UnionFind.union_iff_union_mut {C α τ} [BEq τ] [LawfulBEq τ] (uf: UnionFind C α τ) (x y: τ)
  : ∀ a b, (uf.union x y ⊢ a ≃ b) ↔ (uf.union_mut x y ⊢ a ≃ b)
  := by
    intros a b
    dsimp only [union_mut]
    repeat rw [←find_mut_correct_root]
    repeat rw [←find_mut_preserves_roots]
    apply Iff.trans _ $ (uf.find_mut x).uf'.union_mut_equiv (uf.find x) (uf.find y) y a b
    apply Iff.trans _ $ uf.union_mut_equiv (uf.find x) (uf.find y) x a b
    rw [union_at_roots]


def UnionFind.from_mut {C α τ} [BEq τ] [LawfulBEq τ] (ctx: C τ τ) [FLike C α τ τ ctx] (list: List (τ × τ)) : UnionFind C α τ :=
  match list with
  | List.nil => @UnionFind.trivial C α τ _ _ ctx _
  | List.cons (a,b) eqs => (UnionFind.from_mut ctx eqs).union_mut a b
