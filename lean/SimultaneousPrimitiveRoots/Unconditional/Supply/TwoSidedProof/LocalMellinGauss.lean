module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.SeparationTools
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian identities for the lemma (local Mellin energy)

Tools for `LocalMellin` (`[P-06:0488–0528]`). The manuscript takes "a smooth bump `K` … supported
close enough to zero that its additive Fourier transform has modulus at least `1/2` on `[-1,1]`"
and uses Plancherel twice. Here the bump is a Gaussian, for which every Fourier transform is
explicit, so that Plancherel's theorem is replaced by two identities between finite quadratic
forms:

* `integral_gauss_mul`: `∫ e^{-g(p-y)²} e^{-g(q-y)²} dy = √(π/(2g)) e^{-g(p-q)²/2}`;
* `integral_gauss_phase`: `∫ e^{-ct²} e^{itx} dt = √(π/c) e^{-x²/(4c)}`;
* `integral_weighted_normSq_sum`: `∫ ρ |∑_w a_w φ_w|² = ∑_{w,w'} a_w \bar a_{w'} ∫ ρ φ_w \bar φ_{w'}`;
* `gauss_bridge` (Plancherel for Gaussian windows): for frequencies `p_w` and `c > 0`,
  `∫ e^{-ct²} |∑_w a_w e^{it p_w}|² dt = c⁻¹ ∫ |∑_w a_w e^{-(p_w - y)²/(2c)}|² dy`;
* `integral_gauss_conv`: a Gaussian is an average of narrower Gaussians,
  `∫ e^{-g(x-z)²} e^{-κz²} dz = √(π/(g+κ)) e^{-(gκ/(g+κ)) x²}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace LocalMellinAux

/-! ### Real Gaussians -/

/-- A shifted Gaussian is integrable. -/
theorem integrable_gauss {g : ℝ} (hg : 0 < g) (p : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-g * (p - y) ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq hg).comp_sub_right p
  have e : (fun y : ℝ => Real.exp (-g * (p - y) ^ 2)) =
      fun y : ℝ => Real.exp (-g * (y - p) ^ 2) :=
    funext fun y => by rw [show (p - y) ^ 2 = (y - p) ^ 2 by ring]
  rw [e]
  exact h

theorem integral_gauss {g : ℝ} (p : ℝ) :
    ∫ y : ℝ, Real.exp (-g * (p - y) ^ 2) = Real.sqrt (Real.pi / g) := by
  have e : (fun y : ℝ => Real.exp (-g * (p - y) ^ 2)) =
      fun y : ℝ => Real.exp (-g * (y - p) ^ 2) :=
    funext fun y => by rw [show (p - y) ^ 2 = (y - p) ^ 2 by ring]
  rw [e]
  exact (integral_sub_right_eq_self (fun y : ℝ => Real.exp (-g * y ^ 2)) p).trans
    (integral_gaussian g)

theorem gauss_mul_eq (g p q y : ℝ) :
    Real.exp (-g * (p - y) ^ 2) * Real.exp (-g * (q - y) ^ 2) =
      Real.exp (-g * (p - q) ^ 2 / 2) * Real.exp (-(2 * g) * ((p + q) / 2 - y) ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem integrable_gauss_mul {g : ℝ} (hg : 0 < g) (p q : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-g * (p - y) ^ 2) * Real.exp (-g * (q - y) ^ 2)) := by
  have e : (fun y : ℝ => Real.exp (-g * (p - y) ^ 2) * Real.exp (-g * (q - y) ^ 2)) =
      fun y : ℝ => Real.exp (-g * (p - q) ^ 2 / 2) *
        Real.exp (-(2 * g) * ((p + q) / 2 - y) ^ 2) := funext fun y => gauss_mul_eq g p q y
  rw [e]
  exact (integrable_gauss (mul_pos two_pos hg) ((p + q) / 2)).const_mul _

/-- The product of two Gaussians with the same width. -/
theorem integral_gauss_mul {g : ℝ} (p q : ℝ) :
    ∫ y : ℝ, Real.exp (-g * (p - y) ^ 2) * Real.exp (-g * (q - y) ^ 2) =
      Real.sqrt (Real.pi / (2 * g)) * Real.exp (-g * (p - q) ^ 2 / 2) := by
  have e : (fun y : ℝ => Real.exp (-g * (p - y) ^ 2) * Real.exp (-g * (q - y) ^ 2)) =
      fun y : ℝ => Real.exp (-g * (p - q) ^ 2 / 2) *
        Real.exp (-(2 * g) * ((p + q) / 2 - y) ^ 2) := funext fun y => gauss_mul_eq g p q y
  rw [e, integral_const_mul, integral_gauss, mul_comm]

theorem gauss_conv_eq {g κ : ℝ} (hgκ : g + κ ≠ 0) (x z : ℝ) :
    Real.exp (-g * (x - z) ^ 2) * Real.exp (-κ * z ^ 2) =
      Real.exp (-(g * κ / (g + κ)) * x ^ 2) *
        Real.exp (-(g + κ) * (g * x / (g + κ) - z) ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **A Gaussian is an average of narrower Gaussians.** -/
theorem integral_gauss_conv {g κ : ℝ} (hg : 0 < g) (hκ : 0 < κ) (x : ℝ) :
    ∫ z : ℝ, Real.exp (-g * (x - z) ^ 2) * Real.exp (-κ * z ^ 2) =
      Real.sqrt (Real.pi / (g + κ)) * Real.exp (-(g * κ / (g + κ)) * x ^ 2) := by
  have hgκ : g + κ ≠ 0 := (add_pos hg hκ).ne'
  have e : (fun z : ℝ => Real.exp (-g * (x - z) ^ 2) * Real.exp (-κ * z ^ 2)) =
      fun z : ℝ => Real.exp (-(g * κ / (g + κ)) * x ^ 2) *
        Real.exp (-(g + κ) * (g * x / (g + κ) - z) ^ 2) := funext fun z => gauss_conv_eq hgκ x z
  rw [e, integral_const_mul, integral_gauss, mul_comm]

/-! ### The Fourier transform of a Gaussian -/

/-- `conj e^{ivs} = e^{-ivs}`. -/
theorem conj_phase (v s : ℝ) : conj (Separation.phase v s) = Separation.phase v (-s) := by
  unfold Separation.phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem integrable_gauss_phase {c : ℝ} (hc : 0 < c) (x : ℝ) :
    Integrable (fun t : ℝ => ((Real.exp (-c * t ^ 2) : ℝ) : ℂ) * Separation.phase t x) :=
  Integrable.mono' (integrable_exp_neg_mul_sq hc)
    ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-c * t ^ 2))).mul (Separation.continuous_phase x)).aestronglyMeasurable
    (ae_of_all _ fun t => by
      show ‖((Real.exp (-c * t ^ 2) : ℝ) : ℂ) * Separation.phase t x‖ ≤ Real.exp (-c * t ^ 2)
      rw [norm_mul, Separation.norm_phase, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le])

/-- **The Fourier transform of a Gaussian**: `∫ e^{-ct²} e^{itx} dt = √(π/c) e^{-x²/(4c)}`. -/
theorem integral_gauss_phase {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ∫ t : ℝ, ((Real.exp (-c * t ^ 2) : ℝ) : ℂ) * Separation.phase t x =
      ((Real.sqrt (Real.pi / c) * Real.exp (-x ^ 2 / (4 * c)) : ℝ) : ℂ) := by
  have hb : 0 < ((c : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact hc
  have hfun : (fun t : ℝ => ((Real.exp (-c * t ^ 2) : ℝ) : ℂ) * Separation.phase t x) =
      fun t : ℝ => Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) *
        Complex.exp (-(c : ℂ) * (t : ℂ) ^ 2) := by
    funext t
    unfold Separation.phase
    rw [Complex.ofReal_exp, mul_comm]
    congr 2
    · push_cast
      ring
    · push_cast
      ring
  have e1 : ((Real.sqrt (Real.pi / c) : ℝ) : ℂ) = ((Real.pi : ℂ) / (c : ℂ)) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (div_pos Real.pi_pos hc).le, Complex.ofReal_div,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have e2 : ((Real.exp (-x ^ 2 / (4 * c)) : ℝ) : ℂ) =
      Complex.exp (-(x : ℂ) ^ 2 / (4 * (c : ℂ))) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hfun, fourierIntegral_gaussian hb (x : ℂ), Complex.ofReal_mul, e1, e2]

/-! ### Quadratic forms -/

/-- Expansion of the square of a finite sum. -/
theorem normSq_sum_eq (s : Finset ℕ) (a z : ℕ → ℂ) :
    ((‖∑ w ∈ s, a w * z w‖ ^ 2 : ℝ) : ℂ) =
      ∑ w ∈ s, ∑ w' ∈ s, a w * conj (a w') * (z w * conj (z w')) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
  rw [map_mul]
  ring

/-- **The weighted mean square of a finite combination as a quadratic form.** -/
theorem integral_weighted_normSq_sum (s : Finset ℕ) (a : ℕ → ℂ) (ρ : ℝ → ℝ) (φ : ℕ → ℝ → ℂ)
    (hint : ∀ w ∈ s, ∀ w' ∈ s,
      Integrable (fun x => ((ρ x : ℝ) : ℂ) * (φ w x * conj (φ w' x)))) :
    Integrable (fun x => ρ x * ‖∑ w ∈ s, a w * φ w x‖ ^ 2) ∧
      ((∫ x, ρ x * ‖∑ w ∈ s, a w * φ w x‖ ^ 2 : ℝ) : ℂ) =
        ∑ w ∈ s, ∑ w' ∈ s, a w * conj (a w') *
          ∫ x, ((ρ x : ℝ) : ℂ) * (φ w x * conj (φ w' x)) := by
  have hpt : ∀ x, ((ρ x * ‖∑ w ∈ s, a w * φ w x‖ ^ 2 : ℝ) : ℂ) =
      ∑ w ∈ s, ∑ w' ∈ s, a w * conj (a w') * (((ρ x : ℝ) : ℂ) * (φ w x * conj (φ w' x))) := by
    intro x
    rw [Complex.ofReal_mul, normSq_sum_eq s a fun w => φ w x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w' _ => by ring
  have hterm : ∀ w ∈ s, ∀ w' ∈ s, Integrable (fun x =>
      a w * conj (a w') * (((ρ x : ℝ) : ℂ) * (φ w x * conj (φ w' x)))) :=
    fun w hw w' hw' => (hint w hw w' hw').const_mul _
  have hinner : ∀ w ∈ s, Integrable (fun x => ∑ w' ∈ s,
      a w * conj (a w') * (((ρ x : ℝ) : ℂ) * (φ w x * conj (φ w' x)))) :=
    fun w hw => integrable_finsetSum s fun w' hw' => hterm w hw w' hw'
  have hsum : Integrable (fun x => ∑ w ∈ s, ∑ w' ∈ s,
      a w * conj (a w') * (((ρ x : ℝ) : ℂ) * (φ w x * conj (φ w' x)))) :=
    integrable_finsetSum s hinner
  have hC : Integrable (fun x => ((ρ x * ‖∑ w ∈ s, a w * φ w x‖ ^ 2 : ℝ) : ℂ)) :=
    hsum.congr (ae_of_all _ fun x => (hpt x).symm)
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
      Complex.reCLM.integrable_comp hC
  · rw [← integral_complex_ofReal, integral_congr_ae (ae_of_all _ hpt),
      integral_finsetSum s hinner]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [integral_finsetSum s fun w' hw' => hterm w hw w' hw']
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [integral_const_mul]

/-- The Gaussian-weighted mean square of an exponential sum with the frequencies `p_w`. -/
theorem integral_gauss_expSum (s : Finset ℕ) (a : ℕ → ℂ) (p : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ =>
        Real.exp (-c * t ^ 2) * ‖∑ w ∈ s, a w * Separation.phase t (p w)‖ ^ 2) ∧
      ((∫ t : ℝ, Real.exp (-c * t ^ 2) * ‖∑ w ∈ s, a w * Separation.phase t (p w)‖ ^ 2 : ℝ) :
          ℂ) = ∑ w ∈ s, ∑ w' ∈ s, a w * conj (a w') *
        ((Real.sqrt (Real.pi / c) * Real.exp (-(p w - p w') ^ 2 / (4 * c)) : ℝ) : ℂ) := by
  have hker : ∀ w w' : ℕ, (fun t : ℝ => ((Real.exp (-c * t ^ 2) : ℝ) : ℂ) *
        (Separation.phase t (p w) * conj (Separation.phase t (p w')))) =
      fun t : ℝ => ((Real.exp (-c * t ^ 2) : ℝ) : ℂ) * Separation.phase t (p w - p w') :=
    fun w w' => funext fun t => by
      rw [conj_phase, ← Separation.phase_add, sub_eq_add_neg]
  obtain ⟨h1, h2⟩ := integral_weighted_normSq_sum s a (fun t => Real.exp (-c * t ^ 2))
    (fun w t => Separation.phase t (p w)) (fun w _ w' _ => by
      show Integrable (fun t : ℝ => ((Real.exp (-c * t ^ 2) : ℝ) : ℂ) *
        (Separation.phase t (p w) * conj (Separation.phase t (p w'))))
      rw [hker w w']
      exact integrable_gauss_phase hc _)
  refine ⟨h1, h2.trans ?_⟩
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
  rw [hker w w', integral_gauss_phase hc]

/-- The mean square of a combination of Gaussian windows centred at the points `p_w`. -/
theorem integral_gauss_windowSum (s : Finset ℕ) (a : ℕ → ℂ) (p : ℕ → ℝ) {g : ℝ} (hg : 0 < g) :
    Integrable (fun y : ℝ =>
        ‖∑ w ∈ s, a w * ((Real.exp (-g * (p w - y) ^ 2) : ℝ) : ℂ)‖ ^ 2) ∧
      ((∫ y : ℝ, ‖∑ w ∈ s, a w * ((Real.exp (-g * (p w - y) ^ 2) : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        ∑ w ∈ s, ∑ w' ∈ s, a w * conj (a w') *
          ((Real.sqrt (Real.pi / (2 * g)) * Real.exp (-g * (p w - p w') ^ 2 / 2) : ℝ) : ℂ) := by
  have hker : ∀ w w' : ℕ, (fun y : ℝ => (((1 : ℝ) : ℝ) : ℂ) *
        (((Real.exp (-g * (p w - y) ^ 2) : ℝ) : ℂ) *
          conj ((Real.exp (-g * (p w' - y) ^ 2) : ℝ) : ℂ))) =
      fun y : ℝ => ((Real.exp (-g * (p w - y) ^ 2) * Real.exp (-g * (p w' - y) ^ 2) : ℝ) : ℂ) :=
    fun w w' => funext fun y => by
      rw [Complex.ofReal_one, one_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  obtain ⟨h1, h2⟩ := integral_weighted_normSq_sum s a (fun _ => (1 : ℝ))
    (fun w y => ((Real.exp (-g * (p w - y) ^ 2) : ℝ) : ℂ)) (fun w _ w' _ => by
      show Integrable (fun y : ℝ => (((1 : ℝ) : ℝ) : ℂ) *
        (((Real.exp (-g * (p w - y) ^ 2) : ℝ) : ℂ) *
          conj ((Real.exp (-g * (p w' - y) ^ 2) : ℝ) : ℂ)))
      rw [hker w w']
      exact (integrable_gauss_mul hg (p w) (p w')).ofReal)
  have hone : (fun y : ℝ => (1 : ℝ) *
        ‖∑ w ∈ s, a w * ((Real.exp (-g * (p w - y) ^ 2) : ℝ) : ℂ)‖ ^ 2) =
      fun y : ℝ => ‖∑ w ∈ s, a w * ((Real.exp (-g * (p w - y) ^ 2) : ℝ) : ℂ)‖ ^ 2 :=
    funext fun y => one_mul _
  rw [hone] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
  rw [hker w w', integral_complex_ofReal, integral_gauss_mul]

/-- **Plancherel for Gaussian windows**: for frequencies `p_w` and `c > 0`,
`∫ e^{-ct²} |∑_w a_w e^{it p_w}|² dt = c⁻¹ ∫ |∑_w a_w e^{-(p_w - y)²/(2c)}|² dy`. -/
theorem gauss_bridge (s : Finset ℕ) (a : ℕ → ℂ) (p : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, Real.exp (-c * t ^ 2) * ‖∑ w ∈ s, a w * Separation.phase t (p w)‖ ^ 2 =
      c⁻¹ * ∫ y : ℝ,
        ‖∑ w ∈ s, a w * ((Real.exp (-(1 / (2 * c)) * (p w - y) ^ 2) : ℝ) : ℂ)‖ ^ 2 := by
  have hg : 0 < 1 / (2 * c) := by positivity
  obtain ⟨-, h1⟩ := integral_gauss_expSum s a p hc
  obtain ⟨-, h2⟩ := integral_gauss_windowSum s a p hg
  have hsq : Real.sqrt (Real.pi / c) = c⁻¹ * Real.sqrt (Real.pi / (2 * (1 / (2 * c)))) := by
    have e : Real.pi / (2 * (1 / (2 * c))) = Real.pi * c := by
      field_simp
    rw [e, Real.sqrt_eq_iff_mul_self_eq (div_pos Real.pi_pos hc).le
      (mul_nonneg (inv_pos.mpr hc).le (Real.sqrt_nonneg _))]
    have h3 := Real.mul_self_sqrt (mul_pos Real.pi_pos hc).le
    have h4 : c⁻¹ * Real.sqrt (Real.pi * c) * (c⁻¹ * Real.sqrt (Real.pi * c)) =
        c⁻¹ * c⁻¹ * (Real.sqrt (Real.pi * c) * Real.sqrt (Real.pi * c)) := by ring
    rw [h4, h3]
    field_simp
  have hC : ((∫ t : ℝ, Real.exp (-c * t ^ 2) *
        ‖∑ w ∈ s, a w * Separation.phase t (p w)‖ ^ 2 : ℝ) : ℂ) =
      ((c⁻¹ * ∫ y : ℝ, ‖∑ w ∈ s, a w *
        ((Real.exp (-(1 / (2 * c)) * (p w - y) ^ 2) : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [h1, Complex.ofReal_mul, h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w' _ => ?_
    have hexp : -(p w - p w') ^ 2 / (4 * c) = -(1 / (2 * c)) * (p w - p w') ^ 2 / 2 := by
      field_simp
      ring
    rw [hsq, hexp]
    push_cast
    ring
  exact Complex.ofReal_injective hC

end LocalMellinAux

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
