module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsRowSums
public import SimultaneousPrimitiveRoots.Unconditional.Graph.AnchorMemory
public import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Tools for the column bound of the absolute edge

Source: `verification/stage7-sources/S-02.tex`, lines 704–756 and 788–794
(`[S-02:0704–0756, 0788–0794]`).

Finite, mostly combinatorial statements used in the column half of [S] Lemma 3.8.

* `l38_filterMap_split`, `l38_lw` — splitting a list of optional values by a predicate; the
  product of the weights `μ̃_g` of a list of particles, in terms of which the point masses
  `λ_g^{⊗j}/j!` of the memories are expressed (`l38_pointMass_eq`).
* `l38_shift_snd`, `l38_promoted_eq` — "each required residue … selects exactly one point of
  counting measure" [S-02:0735–0737]: a particle with prescribed label and zero translated residue
  is determined.
* `l38_tensor_rows_le` — the inequality form of `tensor_rows`: products of row actions over the
  big groups may be replaced by products of kernels one group at a time.
* `l38_marginal` — integrating out the coordinates of a product weight which a function does not
  read (the labels of the source slots which are not stored).
* `l38_sum_embedding_le` — the number of ordered retrievals of `b` particles among `Z` eligible
  ones is at most `Z^b` ("original stores are now ordered retrievals", [S-02:0789–0790]).
* `l38_slotW`, `l38_sum_prod_slotW` — the per-slot weights of a promotion map and their sum.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Lists of optional values -/

/-- The present values of a family, split by a predicate on the indices. -/
theorem l38_filterMap_split {α β : Type*} (p : α → Prop) [DecidablePred p] (f : α → Option β)
    (l : List α) :
    (l.filterMap f).Perm
      (l.filterMap (fun a => if p a then none else f a) ++
        l.filterMap (fun a => if p a then f a else none)) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a t ih =>
    obtain ⟨o, ho⟩ : ∃ o, f a = o := ⟨_, rfl⟩
    by_cases hp : p a
    · have e1 : (if p a then none else f a) = (none : Option β) := if_pos hp
      have e2 : (if p a then f a else none) = f a := if_pos hp
      rw [List.filterMap_cons_none (f := fun a => if p a then none else f a) e1]
      cases o with
      | none =>
        rw [List.filterMap_cons_none ho,
          List.filterMap_cons_none (f := fun a => if p a then f a else none) (e2.trans ho)]
        exact ih
      | some b =>
        rw [List.filterMap_cons_some ho,
          List.filterMap_cons_some (f := fun a => if p a then f a else none) (e2.trans ho)]
        exact (ih.cons b).trans List.perm_middle.symm
    · have e1 : (if p a then none else f a) = f a := if_neg hp
      have e2 : (if p a then f a else none) = (none : Option β) := if_neg hp
      rw [List.filterMap_cons_none (f := fun a => if p a then f a else none) e2]
      cases o with
      | none =>
        rw [List.filterMap_cons_none ho,
          List.filterMap_cons_none (f := fun a => if p a then none else f a) (e1.trans ho)]
        exact ih
      | some b =>
        rw [List.filterMap_cons_some ho,
          List.filterMap_cons_some (f := fun a => if p a then none else f a) (e1.trans ho),
          List.cons_append]
        exact ih.cons b

/-- The number of indices below `N` is at most `N`. -/
theorem l38_card_fin_lt_le {n : ℕ} (N : ℕ) :
    (Finset.univ.filter fun j : Fin n => j.val < N).card ≤ N := by
  have h : (Finset.univ.filter fun j : Fin n => j.val < N).card ≤ (Finset.range N).card := by
    refine Finset.card_le_card_of_injOn (fun j : Fin n => j.val) (fun j hj => ?_) ?_
    · exact Finset.mem_coe.mpr
        (Finset.mem_range.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2)
    · intro a _ b _ hab
      exact Fin.ext hab
  rw [Finset.card_range] at h
  exact h

/-! ### Products over the coordinates -/

/-- The inequality form of `sum_replace_coord`. -/
theorem l38_sum_replace_coord_le {B : Type*} [Fintype B] [DecidableEq B] {X : B → Type*}
    [∀ g, Fintype (X g)] [∀ g, Nonempty (X g)] (a : B) (m m' : X a → ℝ)
    (R F : (∀ g, X g) → ℝ) (hR0 : ∀ x, 0 ≤ R x)
    (hR : ∀ (x : ∀ g, X g) (u : X a), R (Function.update x a u) = R x)
    (h : ∀ x : ∀ g, X g, ∑ u : X a, m u * F (Function.update x a u) ≤
      ∑ u : X a, m' u * F (Function.update x a u)) :
    ∑ x : ∀ g, X g, m (x a) * R x * F x ≤ ∑ x : ∀ g, X g, m' (x a) * R x * F x := by
  have hN : (0 : ℝ) < (Fintype.card (X a) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have e : (Fintype.card (X a) : ℝ) * ∑ x : ∀ g, X g, m (x a) * R x * F x ≤
      (Fintype.card (X a) : ℝ) * ∑ x : ∀ g, X g, m' (x a) * R x * F x := by
    rw [sum_coord_swap a m R F hR, sum_coord_swap a m' R F hR]
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hR0 x)
  exact le_of_mul_le_mul_left e hN

/-- The inequality form of `tensor_replace`: if in every coordinate `g` the nonnegative weights
`μ_g` integrate the functions `u ↦ F(x[g ↦ u])` to at most what the nonnegative weights `k_g` do,
then `∑_x ∏_g μ_g(x_g) F(x) ≤ ∑_x ∏_g k_g(x_g) F(x)`. -/
theorem l38_tensor_replace_le {B : Type*} [Fintype B] [DecidableEq B] {X : B → Type*}
    [∀ g, Fintype (X g)] [∀ g, Nonempty (X g)] (μ k : ∀ g, X g → ℝ) (F : (∀ g, X g) → ℝ)
    (hμ : ∀ g u, 0 ≤ μ g u) (hk : ∀ g u, 0 ≤ k g u)
    (h : ∀ (g : B) (x : ∀ g, X g), ∑ u : X g, μ g u * F (Function.update x g u) ≤
      ∑ u : X g, k g u * F (Function.update x g u)) :
    ∑ x : ∀ g, X g, (∏ g, μ g (x g)) * F x ≤ ∑ x : ∀ g, X g, (∏ g, k g (x g)) * F x := by
  have key : ∀ T : Finset B,
      ∑ x : ∀ g, X g, (∏ g, μ g (x g)) * F x ≤
        ∑ x : ∀ g, X g, (∏ g, (if g ∈ T then k g (x g) else μ g (x g))) * F x := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      refine le_of_eq (Finset.sum_congr rfl fun x _ => congrArg (fun t => t * F x) ?_)
      exact Finset.prod_congr rfl fun g _ => (if_neg (Finset.notMem_empty g)).symm
    | insert a T ha ih =>
      obtain ⟨R, hRdef⟩ : ∃ R : (∀ g, X g) → ℝ, ∀ x, R x =
          ∏ g ∈ Finset.univ.erase a, (if g ∈ T then k g (x g) else μ g (x g)) :=
        ⟨_, fun _ => rfl⟩
      have hR0 : ∀ x, 0 ≤ R x := by
        intro x
        rw [hRdef]
        refine Finset.prod_nonneg fun g _ => ?_
        split_ifs
        · exact hk g _
        · exact hμ g _
      have hR : ∀ (x : ∀ g, X g) (u : X a), R (Function.update x a u) = R x := by
        intro x u
        rw [hRdef, hRdef]
        refine Finset.prod_congr rfl fun g hg => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hg)]
      have h1 : ∀ x : ∀ g, X g,
          (∏ g, (if g ∈ insert a T then k g (x g) else μ g (x g))) = k a (x a) * R x := by
        intro x
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
          if_pos (Finset.mem_insert_self a T), hRdef]
        refine congrArg (fun t => k a (x a) * t) (Finset.prod_congr rfl fun g hg => ?_)
        have hga : g ≠ a := Finset.ne_of_mem_erase hg
        by_cases hgT : g ∈ T
        · rw [if_pos hgT, if_pos (Finset.mem_insert_of_mem hgT)]
        · rw [if_neg hgT, if_neg fun h => (Finset.mem_insert.mp h).elim hga hgT]
      have h2 : ∀ x : ∀ g, X g,
          (∏ g, (if g ∈ T then k g (x g) else μ g (x g))) = μ a (x a) * R x := by
        intro x
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), if_neg ha, hRdef]
      calc ∑ x : ∀ g, X g, (∏ g, μ g (x g)) * F x
          ≤ ∑ x : ∀ g, X g, (∏ g, (if g ∈ T then k g (x g) else μ g (x g))) * F x := ih
        _ = ∑ x : ∀ g, X g, μ a (x a) * R x * F x :=
            Finset.sum_congr rfl fun x _ => congrArg (fun t => t * F x) (h2 x)
        _ ≤ ∑ x : ∀ g, X g, k a (x a) * R x * F x :=
            l38_sum_replace_coord_le a (μ a) (k a) R F hR0 hR fun x => h a x
        _ = ∑ x : ∀ g, X g, (∏ g, (if g ∈ insert a T then k g (x g) else μ g (x g))) * F x :=
            Finset.sum_congr rfl fun x _ => congrArg (fun t => t * F x) (h1 x).symm
  have h3 : ∑ x : ∀ g, X g,
        (∏ g, (if g ∈ (Finset.univ : Finset B) then k g (x g) else μ g (x g))) * F x =
      ∑ x : ∀ g, X g, (∏ g, k g (x g)) * F x :=
    Finset.sum_congr rfl fun x _ => congrArg (fun t => t * F x)
      (Finset.prod_congr rfl fun g _ => if_pos (Finset.mem_univ g))
  exact (key Finset.univ).trans (le_of_eq h3)

open _root_.Classical in
/-- **The inequality form of `tensor_rows`**: let `(a_g, t_g)` be, for every coordinate `g`, a
finite nonnegatively weighted family of points of `X_g`, and `k_g ≥ 0` a weight on `X_g`, such
that `∑_i a_g(i) F(x[g ↦ t_g(i)]) ≤ ∑_u k_g(u) F(x[g ↦ u])` for all `x`. Then
`∑_{(i_g)} ∏_g a_g(i_g) F((t_g(i_g))_g) ≤ ∑_x ∏_g k_g(x_g) F(x)`. -/
theorem l38_tensor_rows_le {B : Type*} [Fintype B] [DecidableEq B] {X : B → Type*}
    [∀ g, Fintype (X g)] [∀ g, Nonempty (X g)] {I : B → Type*} [∀ g, Fintype (I g)]
    (a : ∀ g, I g → ℝ) (t : ∀ g, I g → X g) (k : ∀ g, X g → ℝ) (F : (∀ g, X g) → ℝ)
    (ha : ∀ g i, 0 ≤ a g i) (hk : ∀ g u, 0 ≤ k g u)
    (h : ∀ (g : B) (x : ∀ g, X g), ∑ i : I g, a g i * F (Function.update x g (t g i)) ≤
      ∑ u : X g, k g u * F (Function.update x g u)) :
    ∑ i : ∀ g, I g, (∏ g, a g (i g)) * F (fun g => t g (i g)) ≤
      ∑ x : ∀ g, X g, (∏ g, k g (x g)) * F x := by
  -- the push-forward weights
  obtain ⟨μ, hμ⟩ : ∃ μ : ∀ g, X g → ℝ,
      ∀ g u, μ g u = ∑ i : I g, if t g i = u then a g i else 0 := ⟨_, fun _ _ => rfl⟩
  have hμ0 : ∀ g u, 0 ≤ μ g u := by
    intro g u
    rw [hμ]
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · exact ha g i
    · exact le_rfl
  have hpush : ∀ (g : B) (Φ : X g → ℝ),
      ∑ u : X g, μ g u * Φ u = ∑ i : I g, a g i * Φ (t g i) := by
    intro g Φ
    have e1 : ∀ u : X g, μ g u * Φ u = ∑ i : I g, if t g i = u then a g i * Φ u else 0 := by
      intro u
      rw [hμ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : t g i = u
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi, zero_mul]
    rw [Finset.sum_congr rfl fun u _ => e1 u, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e4 : (∑ u : X g, if t g i = u then a g i * Φ u else 0) =
        if t g i = t g i then a g i * Φ (t g i) else 0 :=
      Finset.sum_eq_single_of_mem (t g i) (Finset.mem_univ _) fun u _ hu =>
        if_neg (Ne.symm hu)
    exact e4.trans (if_pos rfl)
  have hsum : ∑ i : ∀ g, I g, (∏ g, a g (i g)) * F (fun g => t g (i g)) =
      ∑ x : ∀ g, X g, (∏ g, μ g (x g)) * F x :=
    tensor_rows a t μ F fun g x => (hpush g fun u => F (Function.update x g u)).symm
  rw [hsum]
  exact l38_tensor_replace_le μ k F hμ0 hk fun g x =>
    (le_of_eq (hpush g fun u => F (Function.update x g u))).trans (h g x)

/-! ### Integrating out unread coordinates -/

/-- A product over a finite type, split by a predicate, for arbitrary instances on the two
subtypes. -/
theorem l38_prod_subtype_split {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    [Fintype {x : ι // p x}] [Fintype {x : ι // ¬p x}] (f : ι → ℝ) :
    (∏ i : {x : ι // p x}, f i) * ∏ i : {x : ι // ¬p x}, f i = ∏ i, f i := by
  have h1 : ∏ i : {x : ι // p x}, f i = ∏ i ∈ Finset.univ.filter p, f i :=
    (Finset.prod_subtype (Finset.univ.filter p)
      (fun x => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ x)) f).symm
  have h2 : ∏ i : {x : ι // ¬p x}, f i = ∏ i ∈ Finset.univ.filter (fun x => ¬p x), f i :=
    (Finset.prod_subtype (Finset.univ.filter fun x => ¬p x)
      (fun x => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ x)) f).symm
  rw [h1, h2]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ p f

/-- **Marginals of a product weight**: if a function of `ξ : ι → α` only reads the coordinates
of a list `ls` without repetitions, the other coordinates of the product weight `∏_i ω_i(ξ_i)`
integrate to their total masses. -/
theorem l38_marginal {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] (ls : List ι)
    (hnd : ls.Nodup) (ω : ι → α → ℝ) (H : (Fin ls.length → α) → ℝ) :
    ∑ ξ : ι → α, (∏ i, ω i (ξ i)) * H (fun h => ξ (ls.get h)) =
      (∏ i : {i : ι // ¬i ∈ ls}, ∑ a, ω i a) *
        ∑ q : Fin ls.length → α, (∏ h, ω (ls.get h) (q h)) * H q := by
  have h1 : ∑ ξ : ι → α, (∏ i, ω i (ξ i)) * H (fun h => ξ (ls.get h)) =
      ∑ p : ({i : ι // i ∈ ls} → α) × ({i : ι // ¬i ∈ ls} → α),
        (∏ i : {i : ι // i ∈ ls}, ω i (p.1 i)) * (∏ i : {i : ι // ¬i ∈ ls}, ω i (p.2 i)) *
          H (fun h => p.1 ⟨ls.get h, List.get_mem ls h⟩) := by
    refine Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ ls) (fun _ => α)) _ _
      fun ξ => ?_
    have hp : (∏ i : {i : ι // i ∈ ls}, ω i (ξ i)) * ∏ i : {i : ι // ¬i ∈ ls}, ω i (ξ i) =
        ∏ i, ω i (ξ i) := l38_prod_subtype_split (fun i => i ∈ ls) (fun i => ω i (ξ i))
    rw [← hp]
    rfl
  have h2 : ∑ p : ({i : ι // i ∈ ls} → α) × ({i : ι // ¬i ∈ ls} → α),
        (∏ i : {i : ι // i ∈ ls}, ω i (p.1 i)) * (∏ i : {i : ι // ¬i ∈ ls}, ω i (p.2 i)) *
          H (fun h => p.1 ⟨ls.get h, List.get_mem ls h⟩) =
      (∑ ξ₂ : {i : ι // ¬i ∈ ls} → α, ∏ i : {i : ι // ¬i ∈ ls}, ω i (ξ₂ i)) *
        ∑ ξ₁ : {i : ι // i ∈ ls} → α, (∏ i : {i : ι // i ∈ ls}, ω i (ξ₁ i)) *
          H (fun h => ξ₁ ⟨ls.get h, List.get_mem ls h⟩) := by
    refine (Fintype.sum_prod_type' fun (ξ₁ : {i : ι // i ∈ ls} → α)
      (ξ₂ : {i : ι // ¬i ∈ ls} → α) =>
        (∏ i : {i : ι // i ∈ ls}, ω i (ξ₁ i)) * (∏ i : {i : ι // ¬i ∈ ls}, ω i (ξ₂ i)) *
          H (fun h => ξ₁ ⟨ls.get h, List.get_mem ls h⟩)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ₁ _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun ξ₂ _ => by ring
  have h3 : ∑ ξ₂ : {i : ι // ¬i ∈ ls} → α, ∏ i : {i : ι // ¬i ∈ ls}, ω i (ξ₂ i) =
      ∏ i : {i : ι // ¬i ∈ ls}, ∑ a, ω i a :=
    (Fintype.prod_sum fun (i : {i : ι // ¬i ∈ ls}) (a : α) => ω i a).symm
  have h4 : ∑ ξ₁ : {i : ι // i ∈ ls} → α, (∏ i : {i : ι // i ∈ ls}, ω i (ξ₁ i)) *
        H (fun h => ξ₁ ⟨ls.get h, List.get_mem ls h⟩) =
      ∑ q : Fin ls.length → α, (∏ h, ω (ls.get h) (q h)) * H q := by
    refine Fintype.sum_equiv
      ((List.Nodup.getEquiv ls hnd).symm.arrowCongr (Equiv.refl α)) _ _ fun ξ₁ => ?_
    rw [← Equiv.prod_comp (List.Nodup.getEquiv ls hnd)
      (fun i : {i : ι // i ∈ ls} => ω i (ξ₁ i))]
    rfl
  rw [h1, h2, h3, h4]

/-! ### Ordered retrievals -/

/-- **The number of ordered retrievals**: the embeddings of `b` slots into the indices with a
property are at most `Z^b`, `Z` the number of these indices ("Original stores are now ordered
retrievals. Their count is controlled by the original input `ρ` factors after reversed
translation", [S-02:0789–0791]). -/
theorem l38_sum_embedding_le {b n : ℕ} (A : Fin n → Prop) [DecidablePred A] :
    ∑ e : Fin b ↪ Fin n, (if ∀ h, A (e h) then (1 : ℝ) else 0) ≤
      ((Finset.univ.filter A).card : ℝ) ^ b := by
  have h1 : ∑ e : Fin b ↪ Fin n, (if ∀ h, A (e h) then (1 : ℝ) else 0) ≤
      ∑ φ : Fin b → Fin n, (if ∀ h, A (φ h) then (1 : ℝ) else 0) := by
    have e1 : ∑ e : Fin b ↪ Fin n, (if ∀ h, A (e h) then (1 : ℝ) else 0) =
        ∑ φ ∈ (Finset.univ : Finset (Fin b ↪ Fin n)).image
            (fun e : Fin b ↪ Fin n => (e : Fin b → Fin n)),
          (if ∀ h, A (φ h) then (1 : ℝ) else 0) :=
      (Finset.sum_image (f := fun φ : Fin b → Fin n => if ∀ h, A (φ h) then (1 : ℝ) else 0)
        (fun e₁ _ e₂ _ h12 => DFunLike.coe_injective h12)).symm
    rw [e1]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun φ _ _ => ?_
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have h2 : ∑ φ : Fin b → Fin n, (if ∀ h, A (φ h) then (1 : ℝ) else 0) =
      ∑ φ : Fin b → Fin n, ∏ h : Fin b, (if A (φ h) then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl fun φ _ =>
      (ite_congr_of_iff Iff.rfl rfl rfl).trans
        (Fintype.prod_boole (p := fun h : Fin b => A (φ h))).symm
  have h3 : ∑ φ : Fin b → Fin n, ∏ h : Fin b, (if A (φ h) then (1 : ℝ) else 0) =
      ∏ _h : Fin b, ∑ i : Fin n, (if A i then (1 : ℝ) else 0) :=
    (Fintype.prod_sum fun (_ : Fin b) (i : Fin n) => if A i then (1 : ℝ) else 0).symm
  have h4 : ∑ i : Fin n, (if A i then (1 : ℝ) else 0) = ((Finset.univ.filter A).card : ℝ) :=
    Finset.sum_boole A Finset.univ
  rw [h2, h3, h4, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact h1

/-! ### Particles -/

section OneGroup

variable {S B : Type} {𝒢 : GroupFamily S B} {Bc : ℕ} {g : B}

theorem l38_shift_fst (Δ : ℤ) (pr : Particle 𝒢 g) : (shiftParticle Δ pr).1 = pr.1 := rfl

/-- The residue of a translated particle. -/
theorem l38_shift_snd (Δ : ℤ) (pr : Particle 𝒢 g) :
    (shiftParticle Δ pr).2 = ((Δ : ℤ) : Res pr.1.1) + pr.2 := rfl

theorem l38_shift_injective (Δ : ℤ) :
    Function.Injective (shiftParticle (𝒢 := 𝒢) (g := g) Δ) :=
  (Graph.residueTranslation fun p : {p : ℕ // p ∈ 𝒢.big g} => ((Δ : ℤ) : Res p.1)).injective

/-- **A required residue selects one point of counting measure** [S-02:0735–0737]: a particle
with the label `p` whose translated residue is zero is `(p, -Δ)`. -/
theorem l38_promoted_eq {Δ : ℤ} {p : {p : ℕ // p ∈ 𝒢.big g}} {pr : Particle 𝒢 g}
    (h1 : p = pr.1) (h0 : (shiftParticle Δ pr).2 = 0) :
    pr = ⟨p, -((Δ : ℤ) : Res p.1)⟩ := by
  obtain ⟨p', r⟩ := pr
  have hp : p = p' := h1
  subst hp
  have h0a : ((Δ : ℤ) : Res p.1) + r = 0 := h0
  have hr : r = -((Δ : ℤ) : Res p.1) := eq_neg_of_add_eq_zero_right h0a
  rw [hr]

/-- An index carries no particle if and only if it is at least the size of the memory. -/
theorem l38_memAt_eq_none_iff (z : Mem 𝒢 Bc g) (j : Fin Bc) :
    memAt z j = none ↔ ¬j.val < z.1.val := by
  unfold memAt
  constructor
  · intro h hlt
    rw [dif_pos hlt] at h
    exact Option.some_ne_none _ h
  · intro h
    exact dif_neg h

/-- An index which carries a particle is smaller than the size of the memory. -/
theorem l38_memAt_lt {z : Mem 𝒢 Bc g} {j : Fin Bc} {pr : Particle 𝒢 g}
    (h : memAt z j = some pr) : j.val < z.1.val := by
  by_contra hcon
  rw [(l38_memAt_eq_none_iff z j).mpr hcon] at h
  exact Option.some_ne_none pr h.symm

/-! ### The weights of lists of particles -/

/-- The product of the weights of the labels of a list of particles. -/
def l38_lw (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (l : List (Particle 𝒢 g)) : ℝ :=
  (l.map fun pr : Particle 𝒢 g => μ pr.1).prod

theorem l38_lw_perm (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) {l₁ l₂ : List (Particle 𝒢 g)}
    (h : l₁.Perm l₂) : l38_lw μ l₁ = l38_lw μ l₂ :=
  (h.map _).prod_eq

theorem l38_lw_append (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (l₁ l₂ : List (Particle 𝒢 g)) :
    l38_lw μ (l₁ ++ l₂) = l38_lw μ l₁ * l38_lw μ l₂ := by
  unfold l38_lw
  rw [List.map_append, List.prod_append]

theorem l38_lw_nonneg {μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ} (hμ : ∀ p, 0 ≤ μ p)
    (l : List (Particle 𝒢 g)) : 0 ≤ l38_lw μ l := by
  unfold l38_lw
  refine List.prod_nonneg fun a ha => ?_
  obtain ⟨pr, _, rfl⟩ := List.mem_map.mp ha
  exact hμ _

/-- Translation of the residues does not change the weight of a list. -/
theorem l38_lw_map_shift (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (Δ : ℤ) (l : List (Particle 𝒢 g)) :
    l38_lw μ (l.map (shiftParticle Δ)) = l38_lw μ l := by
  unfold l38_lw
  rw [List.map_map]
  rfl

/-- The weight of the list of a tuple. -/
theorem l38_lw_ofFn (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) {n : ℕ} (x : Fin n → Particle 𝒢 g) :
    l38_lw μ (List.ofFn x) = ∏ i, μ (x i).1 :=
  (congrArg List.prod (List.map_ofFn (f := x) (g := fun pr : Particle 𝒢 g => μ pr.1))).trans
    (List.prod_ofFn (f := fun i => μ (x i).1))

/-- **The point mass `λ_g^{⊗j}/j!` of a memory** in terms of the list of its particles. -/
theorem l38_pointMass_eq (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (z : Mem 𝒢 Bc g) :
    Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => μ pr.1) z =
      l38_lw μ (List.ofFn z.2) / (z.1.val.factorial : ℝ) := by
  rw [l38_lw_ofFn]
  rfl

end OneGroup

/-! ### Promotion maps: the weights of the slots -/

section Slots

variable {J ℓ Bc : ℕ}

open _root_.Classical in
/-- The weight of the promotion choice of one target slot, for an arbitrary set `U` of admissible
slots and an arbitrary set `E` of admissible indices: `1` for no promotion, `κ` for an admissible
promotion, `0` otherwise. -/
def l38_slotW (κ : ℝ) (U : Slot J ℓ → Prop) (E : Fin Bc → Prop) (sl : Slot J ℓ) :
    Option (Fin Bc) → ℝ
  | none => 1
  | some j => if U sl ∧ E j then κ else 0

theorem l38_slotW_none (κ : ℝ) (U : Slot J ℓ → Prop) (E : Fin Bc → Prop) (sl : Slot J ℓ) :
    l38_slotW κ U E sl none = 1 := rfl

open _root_.Classical in
theorem l38_slotW_some (κ : ℝ) (U : Slot J ℓ → Prop) (E : Fin Bc → Prop) (sl : Slot J ℓ)
    (j : Fin Bc) : l38_slotW κ U E sl (some j) = if U sl ∧ E j then κ else 0 := rfl

theorem l38_slotW_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (U : Slot J ℓ → Prop) (E : Fin Bc → Prop)
    (sl : Slot J ℓ) (o : Option (Fin Bc)) : 0 ≤ l38_slotW κ U E sl o := by
  cases o with
  | none =>
    rw [l38_slotW_none]
    exact zero_le_one
  | some j =>
    rw [l38_slotW_some]
    split_ifs
    · exact hκ
    · exact le_rfl

/-- For an admissible promotion map the product of the slot weights is `κ^a`. -/
theorem l38_prod_slotW_of_valid (κ : ℝ) (U : Slot J ℓ → Prop) (E : Fin Bc → Prop)
    (pm : Slot J ℓ → Option (Fin Bc)) (h : ∀ sl j, pm sl = some j → U sl ∧ E j)
    {hd : DecidablePred fun sl : Slot J ℓ => pm sl ≠ none} :
    ∏ sl, l38_slotW κ U E sl (pm sl) =
      κ ^ (@Finset.filter _ (fun sl : Slot J ℓ => pm sl ≠ none) hd Finset.univ).card := by
  have hfac : ∀ sl : Slot J ℓ,
      l38_slotW κ U E sl (pm sl) = if pm sl ≠ none then κ else 1 := by
    intro sl
    obtain ⟨o, ho⟩ : ∃ o, pm sl = o := ⟨_, rfl⟩
    cases o with
    | none =>
      rw [if_neg (fun hne : pm sl ≠ none => hne ho), ho, l38_slotW_none]
    | some j =>
      rw [if_pos (fun hn : pm sl = none => Option.some_ne_none j (ho.symm.trans hn)), ho,
        l38_slotW_some]
      exact if_pos (h sl j ho)
  rw [Finset.prod_congr rfl fun sl _ => hfac sl]
  exact l38_prod_ite_const (fun sl : Slot J ℓ => pm sl ≠ none) κ

open _root_.Classical in
/-- The sum of the slot weights over all promotion maps: `∏_{sl ∈ U} (1 + #E · κ)` (classical
decidability instances). -/
theorem l38_sum_prod_slotW_cl (κ : ℝ) (U : Slot J ℓ → Prop) (E : Fin Bc → Prop) :
    ∑ pm : Slot J ℓ → Option (Fin Bc), ∏ sl, l38_slotW κ U E sl (pm sl) =
      (1 + ((Finset.univ.filter fun j : Fin Bc => E j).card : ℝ) * κ) ^
        (Finset.univ.filter fun sl : Slot J ℓ => U sl).card := by
  have hslot : ∀ sl : Slot J ℓ, ∑ o : Option (Fin Bc), l38_slotW κ U E sl o =
      if U sl then 1 + ((Finset.univ.filter fun j : Fin Bc => E j).card : ℝ) * κ else 1 := by
    intro sl
    rw [Fintype.sum_option, l38_slotW_none,
      Finset.sum_congr rfl fun j _ => l38_slotW_some κ U E sl j]
    by_cases hU : U sl
    · rw [if_pos hU]
      have e : ∀ j : Fin Bc, (if U sl ∧ E j then κ else 0) = if E j then κ else 0 := fun j =>
        ite_congr_of_iff (and_iff_right hU) rfl rfl
      rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul]
    · rw [if_neg hU]
      have e : ∀ j : Fin Bc, (if U sl ∧ E j then κ else 0) = 0 := fun j =>
        if_neg fun h => hU h.1
      rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_const_zero, add_zero]
  have h1 : ∑ pm : Slot J ℓ → Option (Fin Bc), ∏ sl, l38_slotW κ U E sl (pm sl) =
      ∏ sl : Slot J ℓ, ∑ o : Option (Fin Bc), l38_slotW κ U E sl o :=
    (Fintype.prod_sum fun (sl : Slot J ℓ) (o : Option (Fin Bc)) => l38_slotW κ U E sl o).symm
  rw [h1, Finset.prod_congr rfl fun sl _ => hslot sl]
  exact l38_prod_ite_const (fun sl : Slot J ℓ => U sl) _

/-- **The sum of the slot weights over all promotion maps**: `(1 + #E · κ)^{#U}`, for arbitrary
decidability instances. -/
theorem l38_sum_prod_slotW (κ : ℝ) (U : Slot J ℓ → Prop) (E : Fin Bc → Prop)
    {hE : DecidablePred E} {hU : DecidablePred U} :
    ∑ pm : Slot J ℓ → Option (Fin Bc), ∏ sl, l38_slotW κ U E sl (pm sl) =
      (1 + ((@Finset.filter _ E hE Finset.univ).card : ℝ) * κ) ^
        (@Finset.filter _ U hU Finset.univ).card := by
  have e1 : hE = fun j => _root_.Classical.propDecidable (E j) := Subsingleton.elim _ _
  have e2 : hU = fun sl => _root_.Classical.propDecidable (U sl) := Subsingleton.elim _ _
  subst e1
  subst e2
  exact l38_sum_prod_slotW_cl κ U E

end Slots

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
