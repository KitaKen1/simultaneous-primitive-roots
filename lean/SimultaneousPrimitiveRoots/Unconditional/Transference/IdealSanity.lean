module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealOperator
import Mathlib.Tactic.Ring

/-!
# Sanity checks for the ideal operator: the row operation is a probability kernel

The unsymmetrized ideal row operation of a pattern "retains shared labels, samples all unshared
target labels independently with laws `μ_g`, and samples the auxiliary labels of `D_ℬ`
independently with the same laws" [S-02:0086–0090]. So, before the multiplier
`K_ν D_ℬ^{iζ} e(Θ D_ℬ)` is inserted, its coefficients are the point masses of a probability
measure on (auxiliary labels, target list): `sum_transition_weight`. This is the fact behind
"the ideal absolute row and column sums are at most `L^{C₁}` …, since all its unrestricted fresh
laws are probabilities" [S-02:0995–0997].

Consequences proved here: for the raw pattern (`C_g = ∅`, `K₀ = 1`) at `ζ = Θ = 0` the ideal
operator fixes the constant function (`idealOp_raw_one`), hence `‖𝒯(0)‖ ≥ 1` for the family
consisting of the raw pattern alone (`one_le_idealOpNorm_raw`): the raw pairing
(eq:ideal-raw-pairing) [S-03:0463–0469] has norm one at `Θ = ζ = 0`, and the ideal estimate needs
the comparison patterns of Theorem 4.1.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators ComplexConjugate

noncomputable section

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- The auxiliary free labels have total probability one. -/
theorem sum_auxWeight (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (C : B → Finset (Fin J)) : ∑ r : AuxList big C, auxWeight big C r = 1 := by
  unfold auxWeight
  rw [← Fintype.prod_sum (fun (g : B) (φ : {i : Fin J // i ∈ C g} → {q : ℕ // q ∈ big g}) =>
    ∏ i, Graph.primeGroupLaw (big g) (φ i))]
  refine Finset.prod_eq_one fun g _ => ?_
  rw [← Fintype.prod_sum (fun (_ : {i : Fin J // i ∈ C g}) (q : {q : ℕ // q ∈ big g}) =>
    Graph.primeGroupLaw (big g) q)]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Finset.sum_coe_sort (big g) (fun q => Graph.primeGroupLaw (big g) q)]
  exact hlaw g

/-- The law of the target label in one slot of the group `g`, given the source list `p`: the
retained label of `p` in a shared slot, a fresh label of law `μ_g` in an unshared slot. -/
def slotLaw (big : B → Finset ℕ) (C : B → Finset (Fin J)) (p : LabelList big J ℓ) (g : B)
    (s : Slot J ℓ) (q : {q : ℕ // q ∈ big g}) : ℝ :=
  match s with
  | Sum.inl i =>
    if i ∈ C g then Graph.primeGroupLaw (big g) q else if q = p g (Sum.inl i) then 1 else 0
  | Sum.inr _ => Graph.primeGroupLaw (big g) q

omit [Fintype B] [DecidableEq B] in
theorem sum_slotLaw (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (C : B → Finset (Fin J)) (p : LabelList big J ℓ) (g : B) (s : Slot J ℓ) :
    ∑ q : {q : ℕ // q ∈ big g}, slotLaw big C p g s q = 1 := by
  have hfresh : ∑ q : {q : ℕ // q ∈ big g}, Graph.primeGroupLaw (big g) q = 1 := by
    rw [Finset.sum_coe_sort (big g) (fun q => Graph.primeGroupLaw (big g) q)]
    exact hlaw g
  cases s with
  | inl i =>
    by_cases hi : i ∈ C g
    · simpa [slotLaw, hi] using hfresh
    · simp [slotLaw, hi]
  | inr j => simpa [slotLaw] using hfresh

open Classical in
omit [DecidableEq B] in
/-- The law of the target list is the product over groups and slots of the one-slot laws. -/
theorem shared_unshared_eq_prod (C : B → Finset (Fin J)) (p p' : LabelList big J ℓ) :
    (if SharedBig C p p' then unsharedWeight big C p' else 0) =
      ∏ g, ∏ s, slotLaw big C p g s (p' g s) := by
  by_cases h : SharedBig C p p'
  · rw [if_pos h]
    unfold unsharedWeight
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [Fintype.prod_sum_type]
    refine congrArg₂ (fun a b : ℝ => a * b) (Finset.prod_congr rfl fun i _ => ?_)
      (Finset.prod_congr rfl fun j _ => rfl)
    by_cases hi : i ∈ C g
    · simp [slotLaw, hi]
    · simp [slotLaw, hi, h g i hi]
  · rw [if_neg h]
    unfold SharedBig at h
    obtain ⟨g, hg⟩ := not_forall.mp h
    obtain ⟨i, hi'⟩ := not_forall.mp hg
    obtain ⟨hi, hne⟩ := Classical.not_imp.mp hi'
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ g) ?_
    rw [Fintype.prod_sum_type]
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) ?_) _
    simp [slotLaw, hi, hne]

open Classical in
/-- Given the source list, the target lists with the retained shared labels and fresh unshared
labels have total probability one. -/
theorem sum_shared_unsharedWeight (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (C : B → Finset (Fin J)) (p : LabelList big J ℓ) :
    ∑ p' : LabelList big J ℓ, (if SharedBig C p p' then unsharedWeight big C p' else 0) = 1 := by
  simp only [shared_unshared_eq_prod]
  rw [← Fintype.prod_sum (fun (g : B) (φ : Slot J ℓ → {q : ℕ // q ∈ big g}) =>
    ∏ s, slotLaw big C p g s (φ s))]
  refine Finset.prod_eq_one fun g _ => ?_
  rw [← Fintype.prod_sum (fun (s : Slot J ℓ) (q : {q : ℕ // q ∈ big g}) =>
    slotLaw big C p g s q)]
  exact Finset.prod_eq_one fun s _ => sum_slotLaw hlaw C p g s

open Classical in
/-- **The ideal row operation is a probability kernel** [S-02:0086–0090]: for every pattern and
every source list, the transition weights (probability of the auxiliary labels times probability
of the unshared target labels, on the targets retaining the shared labels) sum to one. -/
theorem sum_transition_weight (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (C : B → Finset (Fin J)) (p : LabelList big J ℓ) :
    ∑ r : AuxList big C, ∑ p' : LabelList big J ℓ,
      (if SharedBig C p p' then auxWeight big C r * unsharedWeight big C p' else 0) = 1 := by
  have h : ∀ r : AuxList big C, ∑ p' : LabelList big J ℓ,
      (if SharedBig C p p' then auxWeight big C r * unsharedWeight big C p' else 0) =
        auxWeight big C r := by
    intro r
    have h1 : ∀ p' : LabelList big J ℓ,
        (if SharedBig C p p' then auxWeight big C r * unsharedWeight big C p' else 0) =
          auxWeight big C r * (if SharedBig C p p' then unsharedWeight big C p' else 0) := by
      intro p'
      split_ifs <;> simp
    simp only [h1]
    rw [← Finset.mul_sum, sum_shared_unsharedWeight hlaw, mul_one]
  simp only [h]
  exact sum_auxWeight hlaw C

theorem dilPhase_zero (D : ℕ) : dilPhase 0 0 D = 1 := by
  unfold dilPhase expUnit
  simp

open Classical in
omit [DecidableEq B] in
/-- The coefficients of the raw row operation at `ζ = Θ = 0` are the transition weights. -/
theorem idealCoef_raw_zero (p p' : LabelList big J ℓ)
    (r : AuxList big (Pattern.raw big J ℓ).C) :
    idealCoef (Pattern.raw big J ℓ) 0 0 p r p' =
      ((if SharedBig (Pattern.raw big J ℓ).C p p' then
        auxWeight big (Pattern.raw big J ℓ).C r *
          unsharedWeight big (Pattern.raw big J ℓ).C p' else 0 : ℝ) : ℂ) := by
  unfold idealCoef
  split_ifs with h
  · have hK : (Pattern.raw big J ℓ).K p p' r = 1 := rfl
    rw [hK, dilPhase_zero, mul_one, mul_one]
  · exact Complex.ofReal_zero.symm

/-- At `ζ = Θ = 0` the raw row operation fixes the constant function `1`. -/
theorem idealRow_raw_one (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (p : LabelList big J ℓ) :
    idealRow (Pattern.raw big J ℓ) 0 0 (fun _ => 1) p = 1 := by
  unfold idealRow
  rw [rowOp_apply, Fintype.sum_prod_type]
  simp only [idealCoef_raw_zero, mul_one]
  rw [← Complex.ofReal_one, ← sum_transition_weight hlaw (Pattern.raw big J ℓ).C p,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.ofReal_sum]

/-- Symmetrization fixes the constant function `1`. -/
theorem bigSym_one : bigSym big J ℓ (fun _ => 1) = fun _ => 1 := by
  funext p
  rw [bigSym_apply]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- **The raw ideal operator at `ζ = Θ = 0` fixes constants.** -/
theorem idealOp_raw_one (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1) :
    idealOp (fun _ : Unit => Pattern.raw big J ℓ) 0 0 (fun _ => 1) = fun _ => 1 := by
  have h : idealRow (Pattern.raw big J ℓ) 0 0 (fun _ => 1) = fun _ => 1 :=
    funext fun p => idealRow_raw_one hlaw p
  unfold idealOp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, bigSym_one, Fintype.sum_unique, h, bigSym_one]

/-- **The raw pattern alone does not satisfy the ideal estimate**: `‖𝒯(0)‖ ≥ 1` at `ζ = 0` for the
family consisting of the raw pattern, whenever the laws `μ_g` are positive probability laws. -/
theorem one_le_idealOpNorm_raw (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (hpos : ∀ (g : B) (q : ℕ), q ∈ big g → 0 < Graph.primeGroupLaw (big g) q) :
    1 ≤ idealOpNorm (fun _ : Unit => Pattern.raw big J ℓ) 0 0 := by
  have h := wNorm_apply_le (idealWeight_pos (J := J) (ℓ := ℓ) hpos)
    (idealOp (fun _ : Unit => Pattern.raw big J ℓ) 0 0) (fun _ => 1)
  rw [idealOp_raw_one hlaw] at h
  have h1 : wNorm (idealWeight big J ℓ) (fun _ => (1 : ℂ)) = 1 := by
    unfold wNorm wNormSq
    simp only [norm_one, one_pow, mul_one]
    rw [sum_idealWeight hlaw, Real.sqrt_one]
  rw [h1, mul_one] at h
  exact h

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
