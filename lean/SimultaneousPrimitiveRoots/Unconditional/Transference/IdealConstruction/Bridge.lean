module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Probes
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Sampling fresh labels: from the definitions of [S] §§3–4 to sums over label lists

Source: `verification/stage7-sources/S-02.tex`, lines 79–96, and `S-03.tex`, lines 38–49.

Definition 3.2 samples "all unshared target labels" and "the auxiliary labels of `D_ℬ`"
independently; the statement layer writes this with sums over the target lists which retain the
shared labels (`SharedBig`, `unsharedWeight`) and over tuples `AuxList big Λ`. Here both are
rewritten as sums over *all* label lists with the product measure of `ℋ_id`:

* `sum_shared_eq` — sampling the unshared target labels of a pattern with sets `C_g` is the
  same as replacing the labels of the source list in the coordinates `freeSet C` (the slots of
  `C` and the last `ℓ` slots) by those of an independent list.
* `sum_aux_eq` — a sum over the tuples of type `Λ` with their product law is a sum over all
  lists of a function of the labels in the slots of `Λ` (`restr`).

Both follow from the product formula `sum_prod_prod` (`Fintype.prod_sum`, twice).

* `sp`, `sharedProd` — the product of the labels in the slots of `Λ`, and the product of the
  shared labels; `tupleProd_restr`, `bigDil_restr`.
* `dilPhase_mul`, `norm_dilPhase_le` — `(sn)^{iζ} e(Θ s n) = s^{iζ} · n^{iζ} e((Θ s) n)`: "the
  fixed shared product contributes `C^{iζ}`, of modulus one, and changes the additive frequency
  to `α = Θ C`" [S-03:0567–0569].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### A product over a finite set, as a product over the subtype -/

theorem prod_dite_mem {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α)
    (φ : {i // i ∈ s} → ℝ) :
    ∏ i : α, (if h : i ∈ s then φ ⟨i, h⟩ else 1) = ∏ i : {i // i ∈ s}, φ i := by
  have h1 : ∏ i : α, (if h : i ∈ s then φ ⟨i, h⟩ else 1) =
      ∏ i ∈ s, (if h : i ∈ s then φ ⟨i, h⟩ else 1) :=
    (Finset.prod_subset (Finset.subset_univ s) (fun i _ hi => by simp [hi])).symm
  rw [h1, ← Finset.prod_coe_sort s (fun i => if h : i ∈ s then φ ⟨i, h⟩ else 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

section Products

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- **The product formula** for sums over label lists. -/
theorem sum_prod_prod (f : (g : B) → Slot J ℓ → {q : ℕ // q ∈ big g} → ℝ) :
    ∑ q : LabelList big J ℓ, ∏ g, ∏ s, f g s (q g s) =
      ∏ g, ∏ s, ∑ a : {q : ℕ // q ∈ big g}, f g s a :=
  calc ∑ q : LabelList big J ℓ, ∏ g, ∏ s, f g s (q g s)
      = ∏ g, ∑ φ : Slot J ℓ → {q : ℕ // q ∈ big g}, ∏ s, f g s (φ s) :=
        (Fintype.prod_sum (fun (g : B) (φ : Slot J ℓ → {q : ℕ // q ∈ big g}) =>
          ∏ s, f g s (φ s))).symm
    _ = ∏ g, ∏ s, ∑ a : {q : ℕ // q ∈ big g}, f g s a :=
        Finset.prod_congr rfl fun g _ =>
          (Fintype.prod_sum (fun (s : Slot J ℓ) (a : {q : ℕ // q ∈ big g}) => f g s a)).symm

omit [Fintype B] [DecidableEq B] in
theorem sum_law_subtype (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1) (g : B) :
    ∑ a : {q : ℕ // q ∈ big g}, Graph.primeGroupLaw (big g) a = 1 := by
  rw [Finset.sum_coe_sort (big g) (fun q => Graph.primeGroupLaw (big g) q)]
  exact hlaw g

/-! ### Sampling the unshared target labels -/

/-- The coordinates which a pattern with sets `C_g` samples afresh at the target: the slots of
`C` and the last `ℓ` slots. -/
def freeSet (ℓ : ℕ) (C : B → Finset (Fin J)) : Finset (B × Slot J ℓ) :=
  slotSet ℓ C ∪ lastSet B J ℓ

theorem inl_mem_freeSet {C : B → Finset (Fin J)} {g : B} {i : Fin J} :
    (g, (Sum.inl i : Slot J ℓ)) ∈ freeSet ℓ C ↔ i ∈ C g := by
  unfold freeSet
  rw [Finset.mem_union, inl_mem_slotSet]
  exact ⟨fun h => h.elim id (fun h' => (inl_notMem_lastSet g i h').elim), Or.inl⟩

theorem inr_mem_freeSet (C : B → Finset (Fin J)) (g : B) (j : Fin ℓ) :
    (g, (Sum.inr j : Slot J ℓ)) ∈ freeSet ℓ C :=
  Finset.mem_union_right _ (inr_mem_lastSet g j)

/-- The law of `mix U p q` for a random list `q`: the labels of `U` are fresh, the others are
those of `p`. -/
theorem sum_mix_eq (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (U : Finset (B × Slot J ℓ)) (p p' : LabelList big J ℓ) :
    ∑ q : LabelList big J ℓ, (if mix U p q = p' then idealWeight big J ℓ q else 0) =
      ∏ g, ∏ s, (if (g, s) ∈ U then Graph.primeGroupLaw (big g) (p' g s)
        else if p g s = p' g s then 1 else 0) := by
  have hterm : ∀ q : LabelList big J ℓ,
      (if mix U p q = p' then idealWeight big J ℓ q else 0) =
        ∏ g, ∏ s, (if (if (g, s) ∈ U then q g s else p g s) = p' g s then
          Graph.primeGroupLaw (big g) (q g s) else 0) := by
    intro q
    by_cases h : mix U p q = p'
    · rw [if_pos h]
      unfold idealWeight
      refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun s _ => ?_
      have hgs : (if (g, s) ∈ U then q g s else p g s) = p' g s := congrFun (congrFun h g) s
      rw [if_pos hgs]
    · rw [if_neg h]
      have hne : ∃ g s, ¬ (if (g, s) ∈ U then q g s else p g s) = p' g s := by
        by_contra hcon
        refine h (funext fun g => funext fun s => ?_)
        by_contra hgs
        exact hcon ⟨g, s, hgs⟩
      obtain ⟨g, s, hgs⟩ := hne
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ g)
        (Finset.prod_eq_zero (Finset.mem_univ s) ?_)
      exact if_neg hgs
  calc ∑ q : LabelList big J ℓ, (if mix U p q = p' then idealWeight big J ℓ q else 0)
      = ∑ q : LabelList big J ℓ, ∏ g, ∏ s,
          (if (if (g, s) ∈ U then q g s else p g s) = p' g s then
            Graph.primeGroupLaw (big g) (q g s) else 0) :=
        Finset.sum_congr rfl fun q _ => hterm q
    _ = ∏ g, ∏ s, ∑ a : {q : ℕ // q ∈ big g},
          (if (if (g, s) ∈ U then a else p g s) = p' g s then
            Graph.primeGroupLaw (big g) a else 0) :=
        sum_prod_prod (fun g s a => if (if (g, s) ∈ U then a else p g s) = p' g s then
          Graph.primeGroupLaw (big g) a else 0)
    _ = ∏ g, ∏ s, (if (g, s) ∈ U then Graph.primeGroupLaw (big g) (p' g s)
          else if p g s = p' g s then 1 else 0) := by
        refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun s _ => ?_
        by_cases hU : (g, s) ∈ U
        · have h1 : ∀ a : {q : ℕ // q ∈ big g},
              (if (if (g, s) ∈ U then a else p g s) = p' g s then
                Graph.primeGroupLaw (big g) a else 0) =
              (if a = p' g s then Graph.primeGroupLaw (big g) a else 0) := fun a => by
            rw [if_pos hU]
          rw [Finset.sum_congr rfl fun a _ => h1 a,
            Finset.sum_ite_eq' Finset.univ (p' g s) (fun a => Graph.primeGroupLaw (big g) a),
            if_pos (Finset.mem_univ _), if_pos hU]
        · have h1 : ∀ a : {q : ℕ // q ∈ big g},
              (if (if (g, s) ∈ U then a else p g s) = p' g s then
                Graph.primeGroupLaw (big g) a else 0) =
              (if p g s = p' g s then Graph.primeGroupLaw (big g) a else 0) := fun a => by
            rw [if_neg hU]
          rw [Finset.sum_congr rfl fun a _ => h1 a, if_neg hU]
          by_cases hp : p g s = p' g s
          · have h2 : ∀ a : {q : ℕ // q ∈ big g},
                (if p g s = p' g s then Graph.primeGroupLaw (big g) a else 0) =
                  Graph.primeGroupLaw (big g) a := fun a => if_pos hp
            rw [Finset.sum_congr rfl fun a _ => h2 a, sum_law_subtype hlaw g, if_pos hp]
          · have h2 : ∀ a : {q : ℕ // q ∈ big g},
                (if p g s = p' g s then Graph.primeGroupLaw (big g) a else (0 : ℝ)) = 0 :=
              fun a => if_neg hp
            rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_const_zero, if_neg hp]

/-- The law of the target list of a pattern, as a product over the coordinates. -/
theorem shared_weight_eq (C : B → Finset (Fin J)) (p p' : LabelList big J ℓ)
    [Decidable (SharedBig C p p')] :
    (if SharedBig C p p' then unsharedWeight big C p' else 0) =
      ∏ g, ∏ s, (if (g, s) ∈ freeSet ℓ C then Graph.primeGroupLaw (big g) (p' g s)
        else if p g s = p' g s then 1 else 0) := by
  by_cases h : SharedBig C p p'
  · rw [if_pos h]
    unfold unsharedWeight
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [Fintype.prod_sum_type]
    refine congrArg₂ (fun a b : ℝ => a * b) (Finset.prod_congr rfl fun i _ => ?_)
      (Finset.prod_congr rfl fun j _ => ?_)
    · by_cases hi : i ∈ C g
      · rw [if_pos hi, if_pos ((inl_mem_freeSet (ℓ := ℓ)).mpr hi)]
      · rw [if_neg hi,
          if_neg (fun hh : (g, (Sum.inl i : Slot J ℓ)) ∈ freeSet ℓ C =>
            hi (inl_mem_freeSet.mp hh)),
          if_pos (h g i hi).symm]
    · rw [if_pos (inr_mem_freeSet C g j)]
  · rw [if_neg h]
    unfold SharedBig at h
    obtain ⟨g, hg⟩ := not_forall.mp h
    obtain ⟨i, hi'⟩ := not_forall.mp hg
    obtain ⟨hi, hne⟩ := Classical.not_imp.mp hi'
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ g)
      (Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i)) ?_)
    rw [if_neg (fun hh : (g, (Sum.inl i : Slot J ℓ)) ∈ freeSet ℓ C =>
        hi (inl_mem_freeSet.mp hh)),
      if_neg (fun hh : p g (Sum.inl i) = p' g (Sum.inl i) => hne hh.symm)]

/-- **Sampling the unshared target labels** [S-02:0086–0090]: the sum over the target lists which
retain the shared labels, with the law of the unshared labels, is the sum over all lists `q` of
the value at `mix (freeSet C) p q`. -/
theorem sum_shared_eq (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (C : B → Finset (Fin J)) (p : LabelList big J ℓ) (Ψ : LabelList big J ℓ → ℂ)
    [DecidablePred (SharedBig C p)] :
    ∑ p' : LabelList big J ℓ,
        (if SharedBig C p p' then ((unsharedWeight big C p' : ℝ) : ℂ) * Ψ p' else 0) =
      ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) * Ψ (mix (freeSet ℓ C) p q) := by
  have hk : ∀ p' : LabelList big J ℓ,
      (if SharedBig C p p' then unsharedWeight big C p' else 0) =
        ∑ q : LabelList big J ℓ,
          (if mix (freeSet ℓ C) p q = p' then idealWeight big J ℓ q else 0) := by
    intro p'
    rw [shared_weight_eq, sum_mix_eq hlaw]
  have h1 : ∀ p' : LabelList big J ℓ,
      (if SharedBig C p p' then ((unsharedWeight big C p' : ℝ) : ℂ) * Ψ p' else 0) =
        ∑ q : LabelList big J ℓ,
          (if mix (freeSet ℓ C) p q = p' then (idealWeight big J ℓ q : ℂ) * Ψ p' else 0) := by
    intro p'
    have h2 : (if SharedBig C p p' then ((unsharedWeight big C p' : ℝ) : ℂ) * Ψ p' else 0) =
        (((if SharedBig C p p' then unsharedWeight big C p' else 0 : ℝ)) : ℂ) * Ψ p' := by
      by_cases hs : SharedBig C p p'
      · rw [if_pos hs, if_pos hs]
      · rw [if_neg hs, if_neg hs, Complex.ofReal_zero, zero_mul]
    rw [h2, hk p', Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : mix (freeSet ℓ C) p q = p'
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq, Complex.ofReal_zero, zero_mul]
  rw [Finset.sum_congr rfl fun p' _ => h1 p', Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (mix (freeSet ℓ C) p q)
    (fun p' => (idealWeight big J ℓ q : ℂ) * Ψ p'), if_pos (Finset.mem_univ _)]

/-! ### Tuples of type `Λ` and label lists -/

/-- The labels of a list in the slots of `Λ`, as a tuple of type `Λ`. -/
def restr (Λ : B → Finset (Fin J)) (q : LabelList big J ℓ) : AuxList big Λ :=
  fun g i => q g (Sum.inl i.1)

/-- The list `p` with the labels of the tuple `t` in the slots of `Λ`. -/
def ins (Λ : B → Finset (Fin J)) (p : LabelList big J ℓ) (t : AuxList big Λ) :
    LabelList big J ℓ :=
  fun g s => match s with
    | Sum.inl i => if h : i ∈ Λ g then t g ⟨i, h⟩ else p g (Sum.inl i)
    | Sum.inr j => p g (Sum.inr j)

theorem mix_slotSet_eq_ins (Λ : B → Finset (Fin J)) (p q : LabelList big J ℓ) :
    mix (slotSet ℓ Λ) p q = ins Λ p (restr Λ q) := by
  funext g s
  cases s with
  | inl i =>
    by_cases h : i ∈ Λ g
    · rw [mix_of_mem p q (inl_mem_slotSet.mpr h)]
      simp [ins, restr, h]
    · rw [mix_of_notMem p q (fun hh => h (inl_mem_slotSet.mp hh))]
      simp [ins, h]
  | inr j =>
    rw [mix_of_notMem p q inr_notMem_slotSet]
    simp [ins]

/-- (auxiliary) The factor of the coordinate `(g, s)` in the law of the lists whose labels in
the slots of `Λ` are those of the tuple `t`. -/
def restrFactor (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (t : AuxList big Λ) (g : B)
    (s : Slot J ℓ) (a : {q : ℕ // q ∈ big g}) : ℝ :=
  match s with
  | Sum.inl i =>
    if h : i ∈ Λ g then (if a = t g ⟨i, h⟩ then Graph.primeGroupLaw (big g) a else 0)
    else Graph.primeGroupLaw (big g) a
  | Sum.inr _ => Graph.primeGroupLaw (big g) a

/-- The lists with prescribed labels `t` in the slots of `Λ` have total mass `auxWeight t`. -/
theorem sum_restr_eq (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (Λ : B → Finset (Fin J)) (t : AuxList big Λ) :
    ∑ q : LabelList big J ℓ, (if restr Λ q = t then idealWeight big J ℓ q else 0) =
      auxWeight big Λ t := by
  have hterm : ∀ q : LabelList big J ℓ,
      (if restr Λ q = t then idealWeight big J ℓ q else 0) =
        ∏ g, ∏ s, restrFactor big Λ t g s (q g s) := by
    intro q
    by_cases h : restr Λ q = t
    · rw [if_pos h]
      unfold idealWeight
      refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun s _ => ?_
      cases s with
      | inl i =>
        by_cases hi : i ∈ Λ g
        · have e : q g (Sum.inl i) = t g ⟨i, hi⟩ := congrFun (congrFun h g) ⟨i, hi⟩
          simp [restrFactor, hi, e]
        · simp [restrFactor, hi]
      | inr j => simp [restrFactor]
    · rw [if_neg h]
      have hne : ∃ g, ∃ i : {i : Fin J // i ∈ Λ g}, ¬ q g (Sum.inl i.1) = t g i := by
        by_contra hcon
        refine h (funext fun g => funext fun i => ?_)
        by_contra hgi
        exact hcon ⟨g, i, hgi⟩
      obtain ⟨g, i, hgi⟩ := hne
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ g)
        (Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i.1)) ?_)
      simp [restrFactor, hgi]
  have hinl : ∀ (g : B) (i : Fin J),
      ∑ a : {q : ℕ // q ∈ big g}, restrFactor big Λ t g (Sum.inl i : Slot J ℓ) a =
        if h : i ∈ Λ g then Graph.primeGroupLaw (big g) (t g ⟨i, h⟩) else 1 := by
    intro g i
    by_cases hi : i ∈ Λ g
    · have h1 : ∀ a : {q : ℕ // q ∈ big g},
          restrFactor big Λ t g (Sum.inl i : Slot J ℓ) a =
            (if a = t g ⟨i, hi⟩ then Graph.primeGroupLaw (big g) a else 0) := fun a => by
        simp [restrFactor, hi]
      rw [Finset.sum_congr rfl fun a _ => h1 a,
        Finset.sum_ite_eq' Finset.univ (t g ⟨i, hi⟩) (fun a => Graph.primeGroupLaw (big g) a),
        if_pos (Finset.mem_univ _)]
      simp [hi]
    · have h1 : ∀ a : {q : ℕ // q ∈ big g},
          restrFactor big Λ t g (Sum.inl i : Slot J ℓ) a = Graph.primeGroupLaw (big g) a :=
        fun a => by simp [restrFactor, hi]
      rw [Finset.sum_congr rfl fun a _ => h1 a, sum_law_subtype hlaw g]
      simp [hi]
  have hinr : ∀ (g : B) (j : Fin ℓ),
      ∑ a : {q : ℕ // q ∈ big g}, restrFactor big Λ t g (Sum.inr j : Slot J ℓ) a = 1 :=
    fun g j => sum_law_subtype hlaw g
  calc ∑ q : LabelList big J ℓ, (if restr Λ q = t then idealWeight big J ℓ q else 0)
      = ∑ q : LabelList big J ℓ, ∏ g, ∏ s, restrFactor big Λ t g s (q g s) :=
        Finset.sum_congr rfl fun q _ => hterm q
    _ = ∏ g, ∏ s : Slot J ℓ, ∑ a : {q : ℕ // q ∈ big g}, restrFactor big Λ t g s a :=
        sum_prod_prod (restrFactor big Λ t)
    _ = ∏ g, ∏ i : {i : Fin J // i ∈ Λ g}, Graph.primeGroupLaw (big g) (t g i) := by
        refine Finset.prod_congr rfl fun g _ => ?_
        rw [Fintype.prod_sum_type, Finset.prod_congr rfl fun i _ => hinl g i,
          Finset.prod_congr rfl fun j _ => hinr g j, Finset.prod_const_one, mul_one,
          prod_dite_mem (Λ g) (fun i => Graph.primeGroupLaw (big g) (t g i))]
    _ = auxWeight big Λ t := rfl

/-- **Sampling a tuple of type `Λ`**: a sum over the tuples with their product law is a sum over
all label lists. -/
theorem sum_aux_eq (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (Λ : B → Finset (Fin J)) (Φ : AuxList big Λ → ℂ) :
    ∑ t : AuxList big Λ, (auxWeight big Λ t : ℂ) * Φ t =
      ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) * Φ (restr Λ q) := by
  have h1 : ∀ t : AuxList big Λ, (auxWeight big Λ t : ℂ) * Φ t =
      ∑ q : LabelList big J ℓ,
        (if restr Λ q = t then (idealWeight big J ℓ q : ℂ) * Φ t else 0) := by
    intro t
    rw [← sum_restr_eq (ℓ := ℓ) hlaw Λ t, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : restr Λ q = t
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq, Complex.ofReal_zero, zero_mul]
  rw [Finset.sum_congr rfl fun t _ => h1 t, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (restr Λ q)
    (fun t => (idealWeight big J ℓ q : ℂ) * Φ t), if_pos (Finset.mem_univ _)]

/-! ### Products of labels -/

/-- The product of the labels of `q` in the slots of `Λ`. -/
def sp (Λ : B → Finset (Fin J)) (q : LabelList big J ℓ) : ℕ :=
  ∏ g, ∏ i ∈ Λ g, (q g (Sum.inl i) : ℕ)

omit [DecidableEq B] in
theorem tupleProd_restr (Λ : B → Finset (Fin J)) (q : LabelList big J ℓ) :
    tupleProd Λ (restr Λ q) = sp Λ q := by
  unfold tupleProd sp
  refine Finset.prod_congr rfl fun g _ => ?_
  exact Finset.prod_coe_sort (Λ g) (fun i => (q g (Sum.inl i) : ℕ))

theorem sp_mix_of_subset {Λ : B → Finset (Fin J)} {U : Finset (B × Slot J ℓ)}
    (h : slotSet ℓ Λ ⊆ U) (p q : LabelList big J ℓ) : sp Λ (mix U p q) = sp Λ q := by
  unfold sp
  refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i hi => ?_
  rw [mix_of_mem p q (h (inl_mem_slotSet.mpr hi))]

theorem sp_mix_of_disjoint {Λ : B → Finset (Fin J)} {U : Finset (B × Slot J ℓ)}
    (h : Disjoint (slotSet ℓ Λ) U) (p q : LabelList big J ℓ) : sp Λ (mix U p q) = sp Λ p := by
  unfold sp
  refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i hi => ?_
  rw [mix_of_notMem p q (Finset.disjoint_left.mp h (inl_mem_slotSet.mpr hi))]

/-- The product of the shared labels of `p`: the first `J` slots outside `C`. -/
def sharedProd (C : B → Finset (Fin J)) (p : LabelList big J ℓ) : ℕ :=
  ∏ g, ∏ i : Fin J, if i ∈ C g then 1 else (p g (Sum.inl i) : ℕ)

/-- The product of the labels of `p` in the first `J` slots: the dilation of the raw pattern. -/
def fullProd (p : LabelList big J ℓ) : ℕ := ∏ g, ∏ i : Fin J, (p g (Sum.inl i) : ℕ)

omit [DecidableEq B] in
theorem bigDil_restr (C : B → Finset (Fin J)) (p d : LabelList big J ℓ) :
    bigDil C p (restr C d) = sharedProd C p * sp C d := by
  unfold bigDil sharedProd sp
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  exact congrArg (fun x => (∏ i : Fin J, if i ∈ C g then 1 else (p g (Sum.inl i) : ℕ)) * x)
    (Finset.prod_coe_sort (C g) (fun i => (d g (Sum.inl i) : ℕ)))

omit [DecidableEq B] in
theorem fullProd_eq (C : B → Finset (Fin J)) (p : LabelList big J ℓ) :
    fullProd p = sharedProd C p * sp C p := by
  unfold fullProd sharedProd sp
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hC : ∏ i ∈ C g, (p g (Sum.inl i) : ℕ) =
      ∏ i : Fin J, if i ∈ C g then (p g (Sum.inl i) : ℕ) else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ C g
  · rw [if_pos hi, if_pos hi, one_mul]
  · rw [if_neg hi, if_neg hi, mul_one]

/-- The shared product does not change when labels in free slots are replaced. -/
theorem sharedProd_mix {C : B → Finset (Fin J)} {U : Finset (B × Slot J ℓ)}
    (h : ∀ (g : B) (i : Fin J), (g, (Sum.inl i : Slot J ℓ)) ∈ U → i ∈ C g)
    (p q : LabelList big J ℓ) : sharedProd C (mix U p q) = sharedProd C p := by
  unfold sharedProd
  refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ C g
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi, mix_of_notMem p q (fun hh => hi (h g i hh))]

end Products

/-! ### The phase of a product -/

theorem norm_natCast_cpow_le (D : ℕ) (ζ : ℝ) : ‖(D : ℂ) ^ ((ζ : ℂ) * Complex.I)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos D with h0 | hpos
  · rw [h0, Nat.cast_zero]
    by_cases hw : (ζ : ℂ) * Complex.I = 0
    · rw [hw, Complex.cpow_zero, norm_one]
    · rw [Complex.zero_cpow hw, norm_zero]
      exact zero_le_one
  · have hre : ((ζ : ℂ) * Complex.I).re = 0 := by simp
    rw [Complex.norm_natCast_cpow_of_pos hpos]
    exact le_of_eq (by rw [hre, Real.rpow_zero])

theorem norm_dilPhase_le (ζ Θ : ℝ) (D : ℕ) : ‖dilPhase ζ Θ D‖ ≤ 1 := by
  unfold dilPhase
  rw [norm_mul, norm_expUnit, mul_one]
  exact norm_natCast_cpow_le D ζ

/-- `(sn)^{iζ} e(Θ s n) = s^{iζ} · n^{iζ} e((Θ s) n)`. -/
theorem dilPhase_mul (ζ Θ : ℝ) (s n : ℕ) :
    dilPhase ζ Θ (s * n) = (s : ℂ) ^ ((ζ : ℂ) * Complex.I) * dilPhase ζ (Θ * (s : ℝ)) n := by
  have h1 : ((s * n : ℕ) : ℂ) = (s : ℂ) * (n : ℂ) := Nat.cast_mul s n
  have h2 : Θ * ((s * n : ℕ) : ℝ) = Θ * (s : ℝ) * (n : ℝ) := by
    rw [Nat.cast_mul, mul_assoc]
  unfold dilPhase
  rw [h1, h2, Complex.natCast_mul_natCast_cpow, mul_assoc]

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction
