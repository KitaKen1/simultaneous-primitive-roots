module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Compat4331.ExpSubstitution
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Hecke's integral over the unit directions

Let `W` be a finite set (the infinite places), `m_w > 0` multiplicities with `n = ∑ m_w`, and
`Λ_i : W → ℝ` (`i` running over `W \ {w₀}`) with `∑_w m_w Λ_i(w) = 0` (logarithms of units).
Suppose the linear map `L(τ, p)_w = τ + ∑_i p_i Λ_i(w)` is invertible (Dirichlet). Then for
`a_w > 0` and `s > 0`,

`∫_{ℝ^{W \ w₀}} (∑_w m_w a_w e^{∑_i p_i Λ_i(w)})^{-s} dp
   = |det L|⁻¹ ∏_w Γ(s m_w / n) (m_w a_w)^{-s m_w / n} / Γ(s)`.

For a number field with `a_w = |x|_w²` the right side is a constant times `|N x|^{-2s/n}`: this turns
the averaged Epstein zeta function of `UnitWeights` into a partial Dedekind zeta function.

The proof: write `Γ(s) Q^{-s} = ∫_ℝ exp(-e^τ Q) e^{sτ} dτ`, assemble `(τ, p)` into one vector of `ℝ^W`,
change variables by `L`, and split the result into one-dimensional Gamma integrals.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function

theorem exp_smul_rpow_exp (c a τ : ℝ) :
    Real.exp τ • (Real.exp τ ^ (a - 1) * Real.exp (-(c * Real.exp τ))) =
      Real.exp (-(c * Real.exp τ)) * Real.exp (a * τ) := by
  rw [smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos τ), Real.log_exp]
  have h : Real.exp τ * Real.exp (τ * (a - 1)) = Real.exp (a * τ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp τ * (Real.exp (τ * (a - 1)) * Real.exp (-(c * Real.exp τ)))
      = (Real.exp τ * Real.exp (τ * (a - 1))) * Real.exp (-(c * Real.exp τ)) := by ring
    _ = _ := by rw [h, mul_comm]

theorem integrableOn_rpow_mul_exp_neg_mul' {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ (a - 1) * Real.exp (-(c * y))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := c)
    (by linarith) one_pos hc
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

/-- `∫_ℝ exp(-c e^τ) e^{aτ} dτ = Γ(a) c^{-a}`. -/
theorem integral_exp_neg_mul_exp_mul {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∫ τ : ℝ, Real.exp (-(c * Real.exp τ)) * Real.exp (a * τ) = Real.Gamma a * c ^ (-a) := by
  have h := integral_comp_exp (fun y : ℝ => y ^ (a - 1) * Real.exp (-(c * y)))
  simp only [exp_smul_rpow_exp] at h
  rw [h, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hc, one_div, Real.inv_rpow hc.le,
    ← Real.rpow_neg hc.le, mul_comm]

theorem integrable_exp_neg_mul_exp_mul {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    Integrable fun τ : ℝ => Real.exp (-(c * Real.exp τ)) * Real.exp (a * τ) := by
  have h := (integrable_comp_exp (fun y : ℝ => y ^ (a - 1) * Real.exp (-(c * y)))).mpr
    (integrableOn_rpow_mul_exp_neg_mul' ha hc)
  simpa only [exp_smul_rpow_exp] using h

variable {R : Type*} [Fintype R]

/-- The linear map `(τ, p) ↦ (τ + ∑_i p_i Λ_i(w))_w` on `ℝ × ℝ^R`; the places are `Option R`, the
radial place being `none`. -/
def heckeLin (Λ : R → Option R → ℝ) : (ℝ × (R → ℝ)) →ₗ[ℝ] (ℝ × (R → ℝ)) where
  toFun z := (z.1 + ∑ i, z.2 i * Λ i none, fun j => z.1 + ∑ i, z.2 i * Λ i (some j))
  map_add' z z' := by
    refine Prod.ext ?_ (funext fun j => ?_)
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      ring
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      ring
  map_smul' c z := by
    refine Prod.ext ?_ (funext fun j => ?_)
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The coordinate of `v ∈ ℝ × ℝ^R` at the place `w : Option R`. -/
def placeVal (v : ℝ × (R → ℝ)) : Option R → ℝ
  | none => v.1
  | some j => v.2 j

theorem placeVal_heckeLin (Λ : R → Option R → ℝ) (z : ℝ × (R → ℝ)) (w : Option R) :
    placeVal (heckeLin Λ z) w = z.1 + ∑ i, z.2 i * Λ i w := by
  cases w <;> rfl

/-- The norm form `Q_p = ∑_w m_w a_w e^{∑_i p_i Λ_i(w)}`. -/
def heckeForm (m a : Option R → ℝ) (Λ : R → Option R → ℝ) (p : R → ℝ) : ℝ :=
  ∑ w, m w * a w * Real.exp (∑ i, p i * Λ i w)

theorem heckeForm_pos {m a : Option R → ℝ} (hm : ∀ w, 0 < m w) (ha : ∀ w, 0 < a w)
    (Λ : R → Option R → ℝ) (p : R → ℝ) : 0 < heckeForm m a Λ p :=
  Finset.sum_pos (fun w _ => mul_pos (mul_pos (hm w) (ha w)) (Real.exp_pos _))
    ⟨none, Finset.mem_univ _⟩

/-- One factor `exp(-m_w a_w e^x) e^{(s m_w / n) x}`. -/
def heckeFactor (m a : Option R → ℝ) (s : ℝ) (w : Option R) (x : ℝ) : ℝ :=
  Real.exp (-((m w * a w) * Real.exp x)) * Real.exp ((s * m w / ∑ w', m w') * x)

/-- The product integrand `∏_w heckeFactor_w(v_w)`. -/
def heckeProd (m a : Option R → ℝ) (s : ℝ) (v : ℝ × (R → ℝ)) : ℝ :=
  heckeFactor m a s none v.1 * ∏ j, heckeFactor m a s (some j) (v.2 j)

theorem heckeProd_eq (m a : Option R → ℝ) (s : ℝ) (v : ℝ × (R → ℝ)) :
    heckeProd m a s v = ∏ w, heckeFactor m a s w (placeVal v w) := by
  rw [Fintype.prod_option]
  rfl

theorem heckeProd_heckeLin {m a : Option R → ℝ} (s : ℝ)
    {Λ : R → Option R → ℝ} (hΛ : ∀ i, ∑ w, m w * Λ i w = 0) (hn : ∑ w', m w' ≠ 0)
    (z : ℝ × (R → ℝ)) :
    heckeProd m a s (heckeLin Λ z) =
      Real.exp (-(heckeForm m a Λ z.2 * Real.exp z.1)) * Real.exp (s * z.1) := by
  rw [heckeProd_eq]
  unfold heckeFactor heckeForm
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.exp_sum]
  congr 1
  · congr 1
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [placeVal_heckeLin, Real.exp_add]
    ring
  · congr 1
    have h3 : ∀ i : R, ∑ w, m w * (z.2 i * Λ i w) = 0 := fun i => by
      have : ∑ w, m w * (z.2 i * Λ i w) = z.2 i * ∑ w, m w * Λ i w := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      rw [this, hΛ i, mul_zero]
    have h2 : ∑ w, m w * placeVal (heckeLin Λ z) w = (∑ w', m w') * z.1 := by
      simp only [placeVal_heckeLin, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [h3, Finset.sum_const_zero, add_zero, Finset.sum_mul]
    calc ∑ w, (s * m w / ∑ w', m w') * placeVal (heckeLin Λ z) w
        = (s / ∑ w', m w') * ∑ w, m w * placeVal (heckeLin Λ z) w := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
      _ = s * z.1 := by
          rw [h2]
          field_simp

/-- **Hecke's integral.** -/
theorem integral_heckeForm_rpow {m a : Option R → ℝ} (hm : ∀ w, 0 < m w) (ha : ∀ w, 0 < a w)
    {Λ : R → Option R → ℝ} (hΛ : ∀ i, ∑ w, m w * Λ i w = 0)
    (hdet : LinearMap.det (heckeLin Λ) ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∫ p : R → ℝ, heckeForm m a Λ p ^ (-s) =
      |LinearMap.det (heckeLin Λ)|⁻¹ *
        (∏ w, Real.Gamma (s * m w / ∑ w', m w') *
          (m w * a w) ^ (-(s * m w / ∑ w', m w'))) / Real.Gamma s := by
  have hn : 0 < ∑ w', m w' := Finset.sum_pos (fun w _ => hm w) ⟨none, Finset.mem_univ _⟩
  have hfac : ∀ w, 0 < s * m w / ∑ w', m w' := fun w => by
    have := hm w
    positivity
  have hfint : ∀ w, Integrable (heckeFactor m a s w) := fun w =>
    integrable_exp_neg_mul_exp_mul (mul_pos (hm w) (ha w)) (hfac w)
  have hfval : ∀ w, ∫ x, heckeFactor m a s w x = Real.Gamma (s * m w / ∑ w', m w') *
      (m w * a w) ^ (-(s * m w / ∑ w', m w')) := fun w =>
    integral_exp_neg_mul_exp_mul (mul_pos (hm w) (ha w)) (hfac w)
  -- the product integral
  have hGint : Integrable (heckeProd m a s) ((volume : Measure ℝ).prod (volume : Measure (R → ℝ))) := by
    have h2 : Integrable (fun q : R → ℝ => ∏ j, heckeFactor m a s (some j) (q j)) := by
      have := Integrable.fintype_prod (μ := fun _ : R => (volume : Measure ℝ))
        (f := fun j => heckeFactor m a s (some j)) (fun j => hfint (some j))
      exact this
    exact (hfint none).mul_prod h2
  have hGval : ∫ v, heckeProd m a s v ∂((volume : Measure ℝ).prod (volume : Measure (R → ℝ))) =
      ∏ w, Real.Gamma (s * m w / ∑ w', m w') * (m w * a w) ^ (-(s * m w / ∑ w', m w')) := by
    unfold heckeProd
    have hpm := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (R → ℝ)))
      (heckeFactor m a s none) (fun q : R → ℝ => ∏ j, heckeFactor m a s (some j) (q j))
    rw [hpm, integral_fintype_prod_volume_eq_prod, Fintype.prod_option]
    rw [hfval none]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact hfval (some j)
  -- change of variables by `L`
  set L := heckeLin (R := R) Λ with hL
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    ((volume : Measure ℝ).prod (volume : Measure (R → ℝ))) hdet
  have hcont : Continuous (heckeProd m a s) := by
    unfold heckeProd heckeFactor
    fun_prop
  have hGL : ∫ z, heckeProd m a s (L z) ∂((volume : Measure ℝ).prod (volume : Measure (R → ℝ))) =
      |LinearMap.det L|⁻¹ * ∏ w, Real.Gamma (s * m w / ∑ w', m w') *
        (m w * a w) ^ (-(s * m w / ∑ w', m w')) := by
    rw [← integral_map (L.continuous_of_finiteDimensional.aemeasurable)
      hcont.aestronglyMeasurable, hmap, integral_smul_measure, smul_eq_mul,
      ENNReal.toReal_ofReal (by positivity), abs_inv, hGval]
  have hGLint : Integrable (fun z => heckeProd m a s (L z))
      ((volume : Measure ℝ).prod (volume : Measure (R → ℝ))) := by
    have h1 : Integrable (heckeProd m a s)
        (Measure.map L ((volume : Measure ℝ).prod (volume : Measure (R → ℝ)))) := by
      rw [hmap]
      exact hGint.smul_measure ENNReal.ofReal_ne_top
    exact (integrable_map_measure h1.aestronglyMeasurable
      L.continuous_of_finiteDimensional.aemeasurable).mp h1
  rw [integral_prod_symm _ hGLint] at hGL
  have hu : ∀ q : R → ℝ, ∫ τ : ℝ, heckeProd m a s (L (τ, q)) =
      Real.Gamma s * heckeForm m a Λ q ^ (-s) := by
    intro q
    simp_rw [hL, heckeProd_heckeLin s hΛ hn.ne']
    exact integral_exp_neg_mul_exp_mul (heckeForm_pos hm ha Λ q) hs
  simp_rw [hu, integral_const_mul] at hGL
  have hΓ : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  rw [eq_div_iff hΓ.ne']
  exact (mul_comm _ _).trans hGL

end SimultaneousPrimitiveRoots.Hecke

end
