module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.FiniteOperators
public import SimultaneousPrimitiveRoots.Unconditional.Transference.PrimeGroups
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
# The ideal operator `𝒯(Θ)` ([S] Definition 3.2)

Source: `verification/stage7-sources/S-02.tex`, lines 79–96 (`[S-02:0079–0096]`).

The ideal Hilbert space is `ℋ_id = L²(∏_{g ∈ ℬ} 𝒫_g^M, ⊗_{g ∈ ℬ} μ_g^{⊗M})`; repetitions of prime
values are allowed. Here it is the space of functions on the finite type `LabelList big J ℓ` with
the point masses `idealWeight` (`wInner`, `wNorm` of `FiniteOperators.lean`).

* `idealRow ν ζ Θ` — the unsymmetrized ideal row operation of a pattern `ν`: it "retains shared
  labels, samples all unshared target labels independently with laws `μ_g`, and samples the
  auxiliary labels of `D_ℬ` independently with the same laws", with multiplier
  `K_ν D_ℬ^{iζ} e(Θ D_ℬ)`.
* `bigSym` — big-group symmetrization (the average over all `M!` slot permutations, independently
  in each big group).
* `idealOp 𝔉 ζ Θ` — `𝒯(Θ)`: the sum over the patterns of a family `𝔉`, composed on both sides
  with `bigSym`. It is a `ℂ`-linear endomorphism of `LabelList big J ℓ → ℂ`.
* `idealOpNorm 𝔉 ζ Θ` — the operator norm `‖𝒯(Θ)‖_{2 → 2}` on `ℋ_id`, the quantity of
  (eq:ideal-norm-hypothesis) [S-02:0167–0169] and (eq:ideal-small-norm) [S-03:0029–0032].

Sanity lemmas proved here: the total mass of `ℋ_id` is `1` (`sum_idealWeight`); symmetrization is
an orthogonal projection (`bigSym_idem`, `wInner_bigSym`), as asserted in [S-02:0074–0075]; the
norm is the least operator bound (`idealOpNorm_le_iff`); and for an empty family of big groups
`𝒯(Θ)` is multiplication by `(∑_ν K_ν) e(Θ)` (`idealOp_of_isEmpty`, `idealOpNorm_of_isEmpty`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators ComplexConjugate

noncomputable section

/-- `e(t) = exp(2πit)` [S-01:0010]. -/
def expUnit (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

theorem norm_expUnit (t : ℝ) : ‖expUnit t‖ = 1 := by
  unfold expUnit
  have h : (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The phase `D^{iζ} e(Θ D)` of a positive integer `D`; with `D = D_ℬ` this is the factor of the
ideal multiplier `K_ν D_ℬ^{iζ} e(Θ D_ℬ)` [S-02:0090–0093]. -/
def dilPhase (ζ Θ : ℝ) (D : ℕ) : ℂ :=
  (D : ℂ) ^ ((ζ : ℂ) * Complex.I) * expUnit (Θ * D)

section Ideal

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- The measure `⊗_{g ∈ ℬ} μ_g^{⊗M}` of `ℋ_id` [S-02:0082–0085]: the point mass of a list of big
labels is `∏_g ∏_i μ_g(p_{g,i})`. -/
def idealWeight (big : B → Finset ℕ) (J ℓ : ℕ) (p : LabelList big J ℓ) : ℝ :=
  ∏ g, ∏ i : Slot J ℓ, Graph.primeGroupLaw (big g) (p g i)

/-- The law of the unshared target labels of a pattern with sets `C_g`: independent, of law `μ_g`,
in the `t_g = ℓ + |C_g|` unshared slots (the slots of `C_g` and the last `ℓ` slots) of every big
group [S-02:0087–0088]. -/
def unsharedWeight (big : B → Finset ℕ) (C : B → Finset (Fin J)) (p' : LabelList big J ℓ) : ℝ :=
  ∏ g, ((∏ i : Fin J, if i ∈ C g then Graph.primeGroupLaw (big g) (p' g (Sum.inl i)) else 1) *
    ∏ j : Fin ℓ, Graph.primeGroupLaw (big g) (p' g (Sum.inr j)))

open Classical in
/-- The coefficient of the unsymmetrized ideal row operation of `ν` from the source list `p`, with
auxiliary labels `r`, to the target list `p'`: zero unless the shared labels are retained;
otherwise the probability of `r` and of the unshared target labels times the multiplier
`K_ν D_ℬ^{iζ} e(Θ D_ℬ)` [S-02:0086–0093]. -/
def idealCoef (ν : Pattern big J ℓ) (ζ Θ : ℝ) (p : LabelList big J ℓ) (r : AuxList big ν.C)
    (p' : LabelList big J ℓ) : ℂ :=
  if SharedBig ν.C p p' then
    ((auxWeight big ν.C r * unsharedWeight big ν.C p' : ℝ) : ℂ) *
      (ν.K p p' r * dilPhase ζ Θ (bigDil ν.C p r))
  else 0

/-- **The unsymmetrized ideal row operation for `ν`** [S-02:0086–0093]:
`(idealRow ν ζ Θ F) p = ∑_{r, p'} idealCoef ν ζ Θ p r p' * F p'`. Following [S-02:0076–0077] it
integrates the function at the target `p'` and returns a function at the source `p`. -/
def idealRow (ν : Pattern big J ℓ) (ζ Θ : ℝ) :
    (LabelList big J ℓ → ℂ) →ₗ[ℂ] (LabelList big J ℓ → ℂ) :=
  rowOp (Ξ := AuxList big ν.C × LabelList big J ℓ)
    (fun p ξ => idealCoef ν ζ Θ p ξ.1 ξ.2) (fun _ ξ => ξ.2)

/-- **Big-group symmetrization** [S-02:0072–0075]: the average over all `M!` slot permutations,
independently in each big group. -/
def bigSym (big : B → Finset ℕ) (J ℓ : ℕ) :
    (LabelList big J ℓ → ℂ) →ₗ[ℂ] (LabelList big J ℓ → ℂ) :=
  rowOp (Ξ := SlotPerms B J ℓ) (fun _ _ => (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹)
    (fun p σ => permuteSlots σ p)

/-- **The ideal operator `𝒯(Θ)` of Definition 3.2** [S-02:0079–0096] for a finite pattern family
`𝔉` and a real `ζ`: "the sum over `ν`, composed on both sides with big-group symmetrization". -/
def idealOp {N : Type} [Fintype N] (𝔉 : N → Pattern big J ℓ) (ζ Θ : ℝ) :
    (LabelList big J ℓ → ℂ) →ₗ[ℂ] (LabelList big J ℓ → ℂ) :=
  bigSym big J ℓ ∘ₗ (∑ ν, idealRow (𝔉 ν) ζ Θ) ∘ₗ bigSym big J ℓ

/-- **`‖𝒯(Θ)‖`**, the operator norm on `ℋ_id = L²(⊗ μ_g^{⊗M})`: the norm of
(eq:ideal-norm-hypothesis) [S-02:0167–0169] and of (eq:ideal-small-norm) [S-03:0029–0032]. -/
def idealOpNorm {N : Type} [Fintype N] (𝔉 : N → Pattern big J ℓ) (ζ Θ : ℝ) : ℝ :=
  wOpNorm (idealWeight big J ℓ) (idealOp 𝔉 ζ Θ)

/-! ### Sanity lemmas -/

theorem bigSym_apply (F : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) :
    bigSym big J ℓ F p =
      (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ * ∑ σ : SlotPerms B J ℓ, F (permuteSlots σ p) := by
  unfold bigSym
  rw [rowOp_apply, Finset.mul_sum]

omit [DecidableEq B] in
/-- The measure of `ℋ_id` is invariant under slot permutations [S-02:0074–0075]. -/
theorem idealWeight_permute (σ : SlotPerms B J ℓ) (p : LabelList big J ℓ) :
    idealWeight big J ℓ (permuteSlots σ p) = idealWeight big J ℓ p := by
  unfold idealWeight
  refine Finset.prod_congr rfl fun g _ => ?_
  exact Equiv.prod_comp (σ g) (fun i => Graph.primeGroupLaw (big g) (p g i))

omit [DecidableEq B] in
theorem idealWeight_pos
    (hpos : ∀ (g : B) (q : ℕ), q ∈ big g → 0 < Graph.primeGroupLaw (big g) q)
    (p : LabelList big J ℓ) : 0 < idealWeight big J ℓ p :=
  Finset.prod_pos fun g _ => Finset.prod_pos fun i _ => hpos g _ (p g i).2

/-- **`ℋ_id` carries a probability measure**: `∑_p ∏_g ∏_i μ_g(p_{g,i}) = 1` when every `μ_g` has
total mass one. -/
theorem sum_idealWeight (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1) :
    ∑ p : LabelList big J ℓ, idealWeight big J ℓ p = 1 := by
  unfold idealWeight
  rw [← Fintype.prod_sum (fun (g : B) (φ : Slot J ℓ → {q : ℕ // q ∈ big g}) =>
    ∏ i, Graph.primeGroupLaw (big g) (φ i))]
  refine Finset.prod_eq_one fun g _ => ?_
  rw [← Fintype.prod_sum (fun (_ : Slot J ℓ) (q : {q : ℕ // q ∈ big g}) =>
    Graph.primeGroupLaw (big g) q)]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Finset.sum_coe_sort (big g) (fun q => Graph.primeGroupLaw (big g) q)]
  exact hlaw g

/-- For the prime groups of Definition 3.1 the measure of `ℋ_id` is a probability measure. -/
theorem PrimeGroups.sum_idealWeight {P : GroupParams} {x : ℝ} {S : Type} [Fintype S]
    (𝔊 : PrimeGroups P x S B) (J ℓ : ℕ) :
    ∑ p : LabelList 𝔊.big J ℓ, idealWeight 𝔊.big J ℓ p = 1 :=
  Transference.sum_idealWeight 𝔊.big_law_sum

/-- **Symmetrization is idempotent.** -/
theorem bigSym_idem (F : LabelList big J ℓ → ℂ) :
    bigSym big J ℓ (bigSym big J ℓ F) = bigSym big J ℓ F := by
  funext p
  have hsum : ∀ σ : SlotPerms B J ℓ,
      ∑ τ : SlotPerms B J ℓ, F (permuteSlots τ (permuteSlots σ p)) =
        ∑ ρ : SlotPerms B J ℓ, F (permuteSlots ρ p) := fun σ =>
    Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun τ => by
      simp only [Equiv.coe_mulLeft, permuteSlots_mul]
  have hcard : (Fintype.card (SlotPerms B J ℓ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [bigSym_apply]
  simp only [bigSym_apply, hsum]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel_left₀ hcard]

/-- **Symmetrization is self-adjoint** on `ℋ_id`. With `bigSym_idem` it is the orthogonal
projection of [S-02:0074–0075] ("This is an orthogonal projection because the measures are
invariant under these permutations"). -/
theorem wInner_bigSym (F G : LabelList big J ℓ → ℂ) :
    wInner (idealWeight big J ℓ) F (bigSym big J ℓ G) =
      wInner (idealWeight big J ℓ) (bigSym big J ℓ F) G := by
  have hA : ∀ σ : SlotPerms B J ℓ,
      ∑ p : LabelList big J ℓ,
          (idealWeight big J ℓ p : ℂ) * (conj (F p) * G (permuteSlots σ p)) =
        ∑ p : LabelList big J ℓ,
          (idealWeight big J ℓ p : ℂ) * (conj (F (permuteSlots σ⁻¹ p)) * G p) := by
    intro σ
    refine Fintype.sum_equiv (permuteEquiv σ) _ _ fun p => ?_
    simp only [permuteEquiv_apply, idealWeight_permute, permuteSlots_inv_cancel]
  have hc : conj ((Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹) =
      (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_natCast]
  have hL : wInner (idealWeight big J ℓ) F (bigSym big J ℓ G) =
      (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ *
        ∑ σ : SlotPerms B J ℓ, ∑ p : LabelList big J ℓ,
          (idealWeight big J ℓ p : ℂ) * (conj (F p) * G (permuteSlots σ p)) := by
    unfold wInner
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [bigSym_apply]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  have hR : wInner (idealWeight big J ℓ) (bigSym big J ℓ F) G =
      (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ *
        ∑ σ : SlotPerms B J ℓ, ∑ p : LabelList big J ℓ,
          (idealWeight big J ℓ p : ℂ) * (conj (F (permuteSlots σ p)) * G p) := by
    unfold wInner
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [bigSym_apply, map_mul, map_sum, hc, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [hL, hR]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv (SlotPerms B J ℓ)) _ _ fun σ => hA σ

/-- **The ideal norm is the least operator bound** when the laws `μ_g` are positive (as they are
for the prime groups of Definition 3.1): `‖𝒯(Θ)‖ ≤ C` if and only if `‖𝒯(Θ) F‖ ≤ C ‖F‖` for every
`F ∈ ℋ_id`. -/
theorem idealOpNorm_le_iff
    (hpos : ∀ (g : B) (q : ℕ), q ∈ big g → 0 < Graph.primeGroupLaw (big g) q)
    {N : Type} [Fintype N] (𝔉 : N → Pattern big J ℓ) (ζ Θ : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    idealOpNorm 𝔉 ζ Θ ≤ C ↔ ∀ F : LabelList big J ℓ → ℂ,
      wNorm (idealWeight big J ℓ) (idealOp 𝔉 ζ Θ F) ≤ C * wNorm (idealWeight big J ℓ) F :=
  wOpNorm_le_iff (idealWeight_pos hpos) _ hC

/-! ### The trivial case: no big groups -/

theorem bigSym_of_isEmpty [IsEmpty B] (F : LabelList big J ℓ → ℂ) : bigSym big J ℓ F = F := by
  funext p
  rw [bigSym_apply, Fintype.card_unique, Fintype.sum_unique, Nat.cast_one, inv_one, one_mul]
  exact congrArg F (Subsingleton.elim _ _)

omit [DecidableEq B] in
theorem idealCoef_of_isEmpty [IsEmpty B] (ν : Pattern big J ℓ) (ζ Θ : ℝ)
    (p p' : LabelList big J ℓ) (r : AuxList big ν.C) :
    idealCoef ν ζ Θ p r p' = ν.K p p' r * expUnit Θ := by
  have hs : SharedBig ν.C p p' := fun g => isEmptyElim g
  have h1 : auxWeight big ν.C r = 1 := by
    unfold auxWeight
    exact Fintype.prod_empty _
  have h2 : unsharedWeight big ν.C p' = 1 := by
    unfold unsharedWeight
    exact Fintype.prod_empty _
  have h3 : bigDil ν.C p r = 1 := by
    unfold bigDil
    exact Fintype.prod_empty _
  unfold idealCoef
  rw [if_pos hs, h1, h2, h3]
  unfold dilPhase
  simp

/-- **Without big groups `𝒯(Θ)` is a scalar**: `ℋ_id = ℂ`, `D_ℬ = 1`, and `𝒯(Θ)` is
multiplication by `(∑_ν K_ν) e(Θ)`. -/
theorem idealOp_of_isEmpty [IsEmpty B] {N : Type} [Fintype N] (𝔉 : N → Pattern big J ℓ)
    (ζ Θ : ℝ) (F : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) :
    idealOp 𝔉 ζ Θ F p = (∑ ν, (𝔉 ν).K default default default) * expUnit Θ * F p := by
  unfold idealOp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, bigSym_of_isEmpty, bigSym_of_isEmpty,
    LinearMap.sum_apply, Finset.sum_apply, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold idealRow
  rw [rowOp_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_unique,
    idealCoef_of_isEmpty]
  have key : ∀ (p₁ p₂ p₃ p₄ : LabelList big J ℓ) (r₁ r₂ : AuxList big (𝔉 ν).C),
      (𝔉 ν).K p₁ p₂ r₁ * expUnit Θ * F p₃ = (𝔉 ν).K p₄ p₄ r₂ * expUnit Θ * F p := by
    intro p₁ p₂ p₃ p₄ r₁ r₂
    rw [Subsingleton.elim p₁ p₄, Subsingleton.elim p₂ p₄, Subsingleton.elim r₁ r₂,
      Subsingleton.elim p₃ p]
  exact key _ _ _ _ _ _

/-- Without big groups, `‖𝒯(Θ)‖ = |∑_ν K_ν|` for every `Θ` and `ζ`. -/
theorem idealOpNorm_of_isEmpty [IsEmpty B] {N : Type} [Fintype N] (𝔉 : N → Pattern big J ℓ)
    (ζ Θ : ℝ) : idealOpNorm 𝔉 ζ Θ = ‖∑ ν, (𝔉 ν).K default default default‖ := by
  have hop : idealOp 𝔉 ζ Θ =
      ((∑ ν, (𝔉 ν).K default default default) * expUnit Θ) •
        (LinearMap.id : (LabelList big J ℓ → ℂ) →ₗ[ℂ] (LabelList big J ℓ → ℂ)) := by
    refine LinearMap.ext fun F => funext fun p => ?_
    exact idealOp_of_isEmpty 𝔉 ζ Θ F p
  have hw : ∀ p : LabelList big J ℓ, 0 < idealWeight big J ℓ p := by
    intro p
    have h : idealWeight big J ℓ p = 1 := by
      unfold idealWeight
      exact Fintype.prod_empty _
    rw [h]
    exact one_pos
  unfold idealOpNorm
  rw [hop, wOpNorm_smul_id hw, norm_mul, norm_expUnit, mul_one]

end Ideal

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
