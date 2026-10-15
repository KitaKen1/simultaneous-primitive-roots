module

public import SimultaneousPrimitiveRoots.Hecke.HeckeIntegral
public import SimultaneousPrimitiveRoots.Hecke.UnitWeights
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne

/-!
# Hecke's integral for a number field

For `x ∈ K^×` let `Q_p(x) = ∑_σ y_p(σ) |σ x|²` with the (unclamped) unit weights
`y_p(σ) = exp(2 ∑_i p_i log |σ η_i|)`, `p ∈ ℝ^r`. Then for `s > 0`

`∫_{ℝ^r} Q_p(x)^{-s} dp = heckeConst K s · |N x|^{-2s/n}`,

where `heckeConst K s` does not depend on `x`. This is the abstract Hecke integral
(`integral_heckeForm_rpow`) with the places of `K` indexed by `Option (Fin r)` (`none ↦ w₀`); the
determinant is nonzero because the logarithms of the fundamental units are linearly independent
(Dirichlet's unit theorem, `basisUnitLattice`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone MeasureTheory

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The places of `K` indexed by `Option (Fin r)`, with `none ↦ w₀`. -/
def placeEquiv : Option (Fin (rank K)) ≃ InfinitePlace K :=
  (Equiv.optionCongr equivFinRank).trans (Equiv.optionSubtypeNe w₀)

@[simp] theorem placeEquiv_none : placeEquiv K none = w₀ := rfl

@[simp] theorem placeEquiv_some (j : Fin (rank K)) :
    placeEquiv K (some j) = (equivFinRank j : InfinitePlace K) := rfl

variable {K}

theorem sum_embeddings_eq_sum_places (g : InfinitePlace K → ℝ) :
    ∑ σ : K →+* ℂ, g (InfinitePlace.mk σ) = ∑ w, (mult w : ℝ) * g w := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun φ : K →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : ∀ σ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      g (InfinitePlace.mk σ) = g w := fun σ hσ => by rw [(Finset.mem_filter.mp hσ).2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have := card_filter_mk_eq w
  exact_mod_cast (by convert this using 2)

/-- The unclamped unit weights `y_p(σ) = exp(2 ∑_i p_i log |σ η_i|)`. -/
def unitWeight (p : Fin (rank K) → ℝ) (σ : K →+* ℂ) : ℝ :=
  Real.exp (2 * ∑ i, p i * unitLog K i σ)

/-- The norm form `Q_p(x) = ∑_σ y_p(σ) |σ x|²`. -/
def normForm (x : K) (p : Fin (rank K) → ℝ) : ℝ :=
  ∑ σ : K →+* ℂ, unitWeight p σ * Complex.normSq (σ x)

/-- The multiplicities, indexed by `Option (Fin r)`. -/
def placeMult (o : Option (Fin (rank K))) : ℝ := (mult (placeEquiv K o) : ℝ)

/-- The squared absolute values of `x`, indexed by `Option (Fin r)`. -/
def placeAbsSq (x : K) (o : Option (Fin (rank K))) : ℝ := (placeEquiv K o x) ^ 2

/-- Twice the logarithms of the fundamental units, indexed by `Option (Fin r)`. -/
def placeLog (i : Fin (rank K)) (o : Option (Fin (rank K))) : ℝ :=
  2 * Real.log (placeEquiv K o ((fundSystem K i : (𝓞 K)ˣ) : K))

theorem unitLog_eq_log_place (i : Fin (rank K)) (σ : K →+* ℂ) :
    unitLog K i σ = Real.log (InfinitePlace.mk σ ((fundSystem K i : (𝓞 K)ˣ) : K)) := rfl

theorem normForm_eq_heckeForm (x : K) (p : Fin (rank K) → ℝ) :
    normForm x p = heckeForm placeMult (placeAbsSq x) placeLog p := by
  unfold normForm heckeForm unitWeight
  set g : InfinitePlace K → ℝ := fun w => (w x) ^ 2 *
    Real.exp (∑ i, p i * (2 * Real.log (w ((fundSystem K i : (𝓞 K)ˣ) : K)))) with hg
  have h1 : ∀ σ : K →+* ℂ, Real.exp (2 * ∑ i, p i * unitLog K i σ) * Complex.normSq (σ x) =
      g (InfinitePlace.mk σ) := by
    intro σ
    simp only [hg, unitLog_eq_log_place, InfinitePlace.apply, Complex.normSq_eq_norm_sq]
    rw [mul_comm, Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_congr rfl (fun σ _ => h1 σ), sum_embeddings_eq_sum_places g,
    ← Equiv.sum_comp (placeEquiv K)]
  apply Finset.sum_congr rfl
  intro o _
  simp only [hg, placeMult, placeAbsSq, placeLog]
  ring

theorem placeMult_pos (o : Option (Fin (rank K))) : 0 < placeMult (K := K) o := by
  unfold placeMult
  exact_mod_cast mult_pos

theorem placeAbsSq_pos {x : K} (hx : x ≠ 0) (o : Option (Fin (rank K))) :
    0 < placeAbsSq x o := by
  unfold placeAbsSq
  have := (InfinitePlace.pos_iff (w := placeEquiv K o)).mpr hx
  positivity

theorem sum_placeMult : ∑ o, placeMult (K := K) o = Module.finrank ℚ K := by
  unfold placeMult
  rw [Equiv.sum_comp (placeEquiv K) (fun w => (mult w : ℝ))]
  exact_mod_cast sum_mult_eq

theorem sum_placeMult_mul_placeLog (i : Fin (rank K)) :
    ∑ o, placeMult (K := K) o * placeLog i o = 0 := by
  unfold placeMult placeLog
  rw [Equiv.sum_comp (placeEquiv K)
    (fun w => (mult w : ℝ) * (2 * Real.log (w ((fundSystem K i : (𝓞 K)ˣ) : K))))]
  have h := sum_mult_mul_log (fundSystem K i)
  have : ∑ w : InfinitePlace K, (mult w : ℝ) * (2 * Real.log (w ((fundSystem K i : (𝓞 K)ˣ) : K)))
      = 2 * ∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w ((fundSystem K i : (𝓞 K)ˣ) : K)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [this, h, mul_zero]

/-- **The logarithmic unit map is invertible** (Dirichlet). -/
theorem heckeLin_injective :
    Function.Injective (heckeLin (R := Fin (rank K)) (placeLog (K := K))) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨τ, p⟩ hz
  have hall : ∀ o, τ + ∑ i, p i * placeLog i o = 0 := by
    intro o
    have := congrArg (fun v => placeVal v o) hz
    simp only [placeVal_heckeLin] at this
    rw [this]
    cases o <;> rfl
  -- `τ = 0`
  have hτ : τ = 0 := by
    have hsum : ∑ o, placeMult (K := K) o * (τ + ∑ i, p i * placeLog i o) = 0 := by
      simp [hall]
    have : ∑ o, placeMult (K := K) o * (τ + ∑ i, p i * placeLog i o) =
        (Module.finrank ℚ K : ℝ) * τ := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h0 : ∀ i, ∑ o, placeMult (K := K) o * (p i * placeLog i o) = 0 := fun i => by
        have : ∑ o, placeMult (K := K) o * (p i * placeLog i o) =
            p i * ∑ o, placeMult (K := K) o * placeLog i o := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro o _
          ring
        rw [this, sum_placeMult_mul_placeLog, mul_zero]
      simp_rw [h0, Finset.sum_const_zero, add_zero]
      rw [← Finset.sum_mul, sum_placeMult]
    rw [this] at hsum
    have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    rcases mul_eq_zero.mp hsum with h | h
    · linarith
    · exact h
  subst hτ
  -- `p = 0`, from the linear independence of `log |η_i|`
  have hcomb : ∑ i, p i • logEmbedding K (Additive.ofMul (fundSystem K i)) = 0 := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      logEmbedding_component]
    have hw := hall (some (equivFinRank.symm w))
    simp only [zero_add, placeLog, placeEquiv_some, Equiv.apply_symm_apply] at hw
    have : ∑ i, p i * (mult w.val * Real.log (w.val ((fundSystem K i : (𝓞 K)ˣ) : K))) =
        (mult w.val / 2 : ℝ) *
          ∑ i, p i * (2 * Real.log (w.val ((fundSystem K i : (𝓞 K)ˣ) : K))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this, hw, mul_zero]
  have hp := (Fintype.linearIndependent_iff.mp (isMaxRank_fundSystem K)) p hcomb
  simp only [Prod.mk_eq_zero, true_and]
  funext i
  exact hp i

theorem det_heckeLin_ne_zero :
    LinearMap.det (heckeLin (R := Fin (rank K)) (placeLog (K := K))) ≠ 0 := by
  have hu : IsUnit (heckeLin (R := Fin (rank K)) (placeLog (K := K))) := by
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
    exact heckeLin_injective
  exact ((LinearMap.isUnit_iff_isUnit_det _).mp hu).ne_zero

variable (K) in
/-- The constant of Hecke's integral. -/
def heckeConst (s : ℝ) : ℝ :=
  |LinearMap.det (heckeLin (R := Fin (rank K)) (placeLog (K := K)))|⁻¹ *
    (∏ o, Real.Gamma (s * placeMult (K := K) o / Module.finrank ℚ K) *
      placeMult (K := K) o ^ (-(s * placeMult (K := K) o / Module.finrank ℚ K))) / Real.Gamma s

/-- **Hecke's integral for a number field.** -/
theorem integral_normForm_rpow {x : K} (hx : x ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∫ p : Fin (rank K) → ℝ, normForm x p ^ (-s) =
      heckeConst K s * |(Algebra.norm ℚ x : ℝ)| ^ (-(2 * s / Module.finrank ℚ K)) := by
  simp_rw [normForm_eq_heckeForm]
  rw [integral_heckeForm_rpow placeMult_pos (placeAbsSq_pos hx) sum_placeMult_mul_placeLog
    det_heckeLin_ne_zero hs, sum_placeMult]
  unfold heckeConst
  set n : ℝ := (Module.finrank ℚ K : ℝ) with hn
  -- split the product
  have hsplit : ∀ o, Real.Gamma (s * placeMult (K := K) o / n) *
      (placeMult o * placeAbsSq x o) ^ (-(s * placeMult (K := K) o / n)) =
      (Real.Gamma (s * placeMult (K := K) o / n) *
        placeMult (K := K) o ^ (-(s * placeMult (K := K) o / n))) *
        (placeAbsSq x o) ^ (-(s * placeMult (K := K) o / n)) := fun o => by
    rw [Real.mul_rpow (placeMult_pos o).le (placeAbsSq_pos hx o).le]
    ring
  simp_rw [hsplit]
  rw [Finset.prod_mul_distrib]
  -- the norm
  have hnorm : ∏ o, (placeAbsSq x o) ^ (-(s * placeMult (K := K) o / n)) =
      |(Algebra.norm ℚ x : ℝ)| ^ (-(2 * s / n)) := by
    have h1 : ∀ o, (placeAbsSq x o) ^ (-(s * placeMult (K := K) o / n)) =
        ((placeEquiv K o x) ^ (mult (placeEquiv K o))) ^ (-(2 * s / n)) := fun o => by
      unfold placeAbsSq placeMult
      have h0 : 0 ≤ placeEquiv K o x := apply_nonneg _ _
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_mul h0]
      congr 1
      push_cast
      ring
    simp_rw [h1]
    rw [Real.finsetProd_rpow _ _ (fun o _ => pow_nonneg (apply_nonneg _ _) _)]
    congr 1
    rw [Equiv.prod_comp (placeEquiv K) (fun w => (w x) ^ (mult w)), prod_eq_abs_norm]
    push_cast
    rfl
  rw [hnorm]
  ring

end SimultaneousPrimitiveRoots.Hecke

end
