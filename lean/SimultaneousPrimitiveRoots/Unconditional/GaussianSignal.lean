module

public import SimultaneousPrimitiveRoots.Unconditional.MellinSignal
public import SimultaneousPrimitiveRoots.Unconditional.RayLSeries
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# [A]'s Gaussian signal: from a bound at `∞` to a Mellin signal (step Z6, analytic part)

Let `χ` be a ray class character of a modulus `𝔪` of a number field `K`, and let `H` be
holomorphic and nowhere zero on `Re s > 1 - κ` and bounded on `Re s ≥ 2`. [A] (`A-02a`, §6) works
with the signal (`gaussianSignal χ H`)

`f(Z) = (1/2πi) ∫_{Re s = 2} Z^{s - 8/15} e^{(s - 5/6)²} H(s) / L(s, χ) ds`   (`Z > 0`).

This file proves the generic complex analysis that turns [A]'s estimate
`f(Z) ≪ Z^{1 - κ - 8/15}` (`Z → ∞`) into a Mellin signal of width `κ`
(`hasMellinSignal_of_isBigO`), hence, by `rayClassLZeroFree_of_hasMellinSignal`, into the absence
of zeros of `L(s, χ)` on `Re s > 1 - κ`:

* `L(s, χ)` on `Re s > 1`: holomorphic (`rayClassLSeries_analyticOnNhd`), nonzero
  (`rayClassLSeries_ne_zero`), and `|1 / L(s, χ)| ≤ exp(∑_𝔭 N𝔭^{-2})` on `Re s ≥ 2`
  (`norm_inv_rayClassLSeries_le`); all three come from Tau Ceti's Euler product, applied to the
  completely multiplicative ideal weight `rayWeight χ` of `χ`;
* (a) `f` is continuous on `(0, ∞)`, as a Fourier transform of an integrable function
  (`gaussianSignalOf_continuousOn`), hence locally integrable there;
* (b) for every `σ ≥ 2`, `|f(Z)| ≤ C_σ Z^{σ - 8/15}` on `0 < Z ≤ 1`: shift the line of
  integration to `Re s = σ` (`vertical_integral_eq_of_gaussian_bound`) under the Gaussian bound
  `|e^{(s - 5/6)²}| = e^{(Re s - 5/6)² - (Im s)²}`; so `f` decays rapidly at `0`
  (`gaussianSignalOf_rapidDecayAtZero`);
* (c) Mellin inversion (`mellin_mellinInv_eq`, from Fourier inversion): the Mellin transform
  `signalMellin f (-8/15)` is `e^{(s - 5/6)²} H(s) / L(s, χ)` on the line `Re s = 2`
  (`signalMellin_gaussianSignalOf_on_line`);
* (d) both sides are holomorphic on `Re s > 1`, so they agree there by the identity theorem
  (`signalMellin_gaussianSignalOf`);
* (e) multiplying by `L(s, χ) ≠ 0` gives the identity required by `HasMellinSignal`.

Steps (a)–(d) are stated for any `Q` holomorphic on `Re s > 1` and bounded on `Re s ≥ 2`, with
the signal `gaussianSignalOf Q c x = x^c · (1/2πi) ∫_{Re s = 2} x^s e^{(s - 5/6)²} Q(s) ds`;
[A]'s signal is the case `Q = H / L(·, χ)`, `c = -8/15`.

The analytic part is adapted from openai/math `OAI.NumberTheory.DirichletL.ContinuationInversion`
/ `ContinuationContour` (Apache-2.0), with the signal construction of
`OAI.NumberTheory.DirichletL.Hecke.Signal` / `Hecke.SignalIdentity`, where the same
`Gaussian × H / L` signal is treated for Hecke characters of `ℚ(√-3)`; the bounded-quotient
hypothesis replaces their `|H - 1| ≤ 1/2` and their reciprocal bound.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional

noncomputable section

section Analysis

open Filter Asymptotics MeasureTheory Set Complex
open scoped Topology FourierTransform

/-! ### Mellin inversion on a vertical line -/

/-- The Mellin integral of a signal of growth `Z^{a + c}`, rapidly decaying at `0`, converges at
`-(s + c)` for `Re s > a`. -/
theorem signalMellin_convergent (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) {s : ℂ} (hs : a < s.re) :
    MellinConvergent f (-(s + (c : ℂ))) := by
  apply mellinConvergent_of_isBigO_rpow (a := -(a + c))
    (b := (-(s + (c : ℂ))).re - 1) hlocal
  · simpa only [neg_neg] using htop
  · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    linarith
  · exact hzero _
  · linarith

/-- Mellin convergence at `σ` is integrability of the logarithmic profile
`u ↦ e^{-σu} f(e^{-u})`. -/
theorem integrable_logProfile {f : ℝ → ℂ} {σ : ℝ}
    (hf : MellinConvergent f (σ : ℂ)) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  have hder : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
    fun x _ => mul_neg_one (Real.exp (-x)) ▸
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt
  have himage : Real.exp ∘ Neg.neg '' (univ : Set ℝ) = Ioi 0 := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
      Set.image_univ, Real.range_exp]
  have hinj : univ.InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [MellinConvergent, ← himage,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj] at hf
  have heq (u : ℝ) :
      |-(Real.exp (-u))| • ((Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1) • f (Real.exp (-u))) =
        Real.exp (-σ * u) • f (Real.exp (-u)) := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    change (Real.exp (-u) : ℂ) *
      ((Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1) * f (Real.exp (-u))) =
        (Real.exp (-σ * u) : ℂ) * f (Real.exp (-u))
    rw [← mul_assoc]
    congr 1
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (Real.exp_pos (-u)).le]
    norm_cast
    rw [Real.rpow_def_of_pos (Real.exp_pos (-u)), Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  simpa only [Function.comp_apply, integrableOn_univ, heq] using hf

/-- **Mellin inversion on a vertical line**: if `f = mellinInv σ F` on `(0, ∞)`, `f` is Mellin
convergent at `σ`, and `F` is integrable and continuous on the line `Re s = σ`, then
`mellin f = F` on that line. -/
theorem mellin_mellinInv_eq (σ : ℝ) (F : ℂ → ℂ) (f : ℝ → ℂ)
    (hf : MellinConvergent f (σ : ℂ))
    (hF : Integrable (fun y : ℝ => F ((σ : ℂ) + 2 * Real.pi * y * Complex.I)))
    (hcont : Continuous (fun y : ℝ => F ((σ : ℂ) + 2 * Real.pi * y * Complex.I)))
    (hrep : ∀ x : ℝ, 0 < x → f x = mellinInv σ F x) (y : ℝ) :
    mellin f ((σ : ℂ) + 2 * Real.pi * y * Complex.I) =
      F ((σ : ℂ) + 2 * Real.pi * y * Complex.I) := by
  let A : ℝ → ℂ := fun y => F ((σ : ℂ) + 2 * Real.pi * y * Complex.I)
  let g : ℝ → ℂ := fun u => Real.exp (-σ * u) • f (Real.exp (-u))
  have hg : Integrable g := integrable_logProfile hf
  have hginv : g = 𝓕⁻ A := by
    funext u
    dsimp [g]
    rw [hrep _ (Real.exp_pos _), mellinInv_eq_fourierInv _ _ (Real.exp_pos _)]
    simp only [Real.log_exp, neg_neg]
    change (Real.exp (-σ * u) : ℂ) *
      ((Real.exp (-u) : ℂ) ^ (-(σ : ℂ)) * 𝓕⁻ A u) = 𝓕⁻ A u
    rw [← mul_assoc, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (Real.exp_pos (-u)).le]
    have hc : Real.exp (-σ * u) * Real.exp (-u) ^ (-σ) = 1 := by
      rw [Real.rpow_def_of_pos (Real.exp_pos (-u)), Real.log_exp, ← Real.exp_add]
      rw [show -σ * u + -u * -σ = 0 by ring, Real.exp_zero]
    rw [← Complex.ofReal_mul, hc, Complex.ofReal_one, one_mul]
  have hfourier : Integrable (𝓕 A) := by
    have hn := hg.comp_neg
    rw [hginv] at hn
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hn
  rw [mellin_eq_fourier]
  have hre : ((σ : ℂ) + 2 * Real.pi * y * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + 2 * Real.pi * y * Complex.I).im / (2 * Real.pi) = y := by
    simp
  rw [hre, him]
  change 𝓕 g y = A y
  rw [hginv]
  exact hF.fourier_fourierInv_eq hfourier hcont.continuousAt

/-- The signal normalized by `x^{-c}`, so that its Mellin transform at `-s` is
`signalMellin f c s`. -/
def normalizedSignal (f : ℝ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(c : ℂ)) • f x

/-- The Mellin transform of the normalized signal at `-s` is `signalMellin f c s`. -/
theorem mellin_normalizedSignal (f : ℝ → ℂ) (c : ℝ) (s : ℂ) :
    mellin (normalizedSignal f c) (-s) = signalMellin f c s := by
  unfold normalizedSignal signalMellin
  rw [mellin_cpow_smul]
  congr 1
  ring

/-- **Mellin inversion for `signalMellin`**: if `x^{-c} f(x) = mellinInv (-d) (s ↦ A(-s)) x` on
`(0, ∞)`, then `signalMellin f c = A` on the line `Re s = d`. -/
theorem signalMellin_eq_on_line (f : ℝ → ℂ) (A : ℂ → ℂ) (c d : ℝ)
    (hf : MellinConvergent f (-((d : ℂ) + (c : ℂ))))
    (hA : Integrable (fun y : ℝ => A ((d : ℂ) - 2 * Real.pi * y * Complex.I)))
    (hcont : Continuous (fun y : ℝ => A ((d : ℂ) - 2 * Real.pi * y * Complex.I)))
    (hrep : ∀ x : ℝ, 0 < x → normalizedSignal f c x =
      mellinInv (-d) (fun s => A (-s)) x) (y : ℝ) :
    signalMellin f c ((d : ℂ) - 2 * Real.pi * y * Complex.I) =
      A ((d : ℂ) - 2 * Real.pi * y * Complex.I) := by
  have hf' : MellinConvergent (normalizedSignal f c) ((-d : ℝ) : ℂ) := by
    unfold normalizedSignal
    apply MellinConvergent.cpow_smul.mpr
    convert hf using 1 <;> first | rfl | (push_cast; ring)
  have harg (y : ℝ) : -(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I) =
      (d : ℂ) - 2 * Real.pi * y * Complex.I := by push_cast; ring
  have hA' : Integrable
      (fun y : ℝ => A (-(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I))) := by
    simpa only [harg] using hA
  have hcont' : Continuous
      (fun y : ℝ => A (-(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I))) := by
    simpa only [harg] using hcont
  have hid := mellin_mellinInv_eq (-d) (fun s => A (-s))
    (normalizedSignal f c) hf' hA' hcont' hrep y
  rw [harg] at hid
  rw [← mellin_normalizedSignal]
  convert hid using 1 <;> first | rfl | (congr 1; push_cast; ring)

/-! ### Shifting vertical lines under a Gaussian bound -/

/-- Cauchy's theorem on the rectangles `[a, b] × [-T, T]`: if the horizontal sides vanish as
`T → ∞`, the integrals over the vertical lines `Re s = a` and `Re s = b` agree. -/
theorem vertical_integral_eq_of_horizontal_vanish (F : ℂ → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (ha : Integrable (fun y : ℝ => F ((a : ℂ) + y * I)))
    (hb : Integrable (fun y : ℝ => F ((b : ℂ) + y * I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I))
      atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + T * I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, F ((a : ℂ) + y * I)) = ∫ y : ℝ, F ((b : ℂ) + y * I) := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I)) -
      (∫ x : ℝ in a..b, F ((x : ℂ) + T * I)) +
      I * (∫ y : ℝ in -T..T, F ((b : ℂ) + y * I)) -
      I * (∫ y : ℝ in -T..T, F ((a : ℂ) + y * I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn F
      ((a : ℂ) + (-T) * I) ((b : ℂ) + T * I) (hhol.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      have hzre := hz.1
      simpa [uIcc_of_le hab] using hzre
  have hlim := ((hbot.sub htop).add
    ((intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id).const_mul I)).sub
    ((intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).const_mul I)
  have hzero : (0 : ℂ) - 0 + I * (∫ y : ℝ, F ((b : ℂ) + y * I)) -
      I * (∫ y : ℝ, F ((a : ℂ) + y * I)) = 0 :=
    tendsto_nhds_unique hlim (by simpa only [id_eq, hrect] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0)))
  have heq : I * (∫ y : ℝ, F ((b : ℂ) + y * I)) =
      I * (∫ y : ℝ, F ((a : ℂ) + y * I)) := by simpa using sub_eq_zero.mp hzero
  exact (mul_left_cancel₀ I_ne_zero heq).symm

/-- Under a Gaussian bound, the horizontal segments `[a, b] + iT` contribute nothing as
`T → ∞`. -/
theorem horizontal_integral_tendsto_zero (F : ℂ → ℂ) (a b C : ℝ)
    (hbound : ∀ x ∈ Set.uIcc a b, ∀ y : ℝ,
      ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-(y ^ 2))) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + T * I)) atTop (𝓝 0) := by
  have hnorm (T : ℝ) : ‖∫ x : ℝ in a..b, F ((x : ℂ) + T * I)‖ ≤
      C * Real.exp (-(T ^ 2)) * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hbound x (uIoc_subset_uIcc hx) T)
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by decide)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hnorm
    (by simpa using (hexp.const_mul C).mul_const |b-a|)

/-- A measurable function bounded by `C e^{-y²}` is integrable. -/
theorem integrable_of_gaussian_bound (f : ℝ → ℂ) (C : ℝ)
    (hmeas : AEStronglyMeasurable f) (hbound : ∀ y, ‖f y‖ ≤ C * Real.exp (-(y ^ 2))) :
    Integrable f := by
  have hg : Integrable (fun y : ℝ => C * Real.exp (-(y ^ 2))) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul C
  exact hg.mono' hmeas (ae_of_all _ hbound)

/-- **Shifting a vertical line of integration** across a strip where `F` is holomorphic and
bounded by `C e^{-t²}`. -/
theorem vertical_integral_eq_of_gaussian_bound (F : ℂ → ℂ) {a b C : ℝ}
    (hab : a ≤ b) (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ,
      ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-(y ^ 2))) :
    (∫ y : ℝ, F ((a : ℂ) + y * I)) = ∫ y : ℝ, F ((b : ℂ) + y * I) := by
  have hc (x : ℝ) (hx : x ∈ Icc a b) : Continuous (fun y : ℝ => F ((x : ℂ) + y * I)) :=
    hhol.continuousOn.comp_continuous (by fun_prop) (by intro y; simpa using hx)
  apply vertical_integral_eq_of_horizontal_vanish F hab hhol
    (integrable_of_gaussian_bound _ C (hc a ⟨le_rfl, hab⟩).aestronglyMeasurable
      (hbound a ⟨le_rfl, hab⟩))
    (integrable_of_gaussian_bound _ C (hc b ⟨hab, le_rfl⟩).aestronglyMeasurable
      (hbound b ⟨hab, le_rfl⟩))
  · have h := horizontal_integral_tendsto_zero (fun s => F ((s.re : ℂ) - s.im * I)) a b C ?_
    · simpa [sub_eq_add_neg, neg_mul] using h
    · intro x hx y
      simpa [sub_eq_add_neg, neg_mul] using hbound x (by simpa [uIcc_of_le hab] using hx) (-y)
  · exact horizontal_integral_tendsto_zero F a b C
      (by simpa [uIcc_of_le hab] using hbound)

/-- The integrand `Z^{s + c} e^{(s - 5/6)²} G(s)` of the signal. -/
def gaussianContourIntegrand (G : ℂ → ℂ) (c Z : ℝ) (s : ℂ) : ℂ :=
  (Z : ℂ) ^ (s + (c : ℂ)) * Complex.exp ((s - 5 / 6) ^ 2) * G s

/-- `|Z^{s + c} e^{(s - 5/6)²} G(s)| = Z^{x + c} e^{(x - 5/6)²} |G(s)| e^{-y²}` for
`s = x + iy`, `Z > 0`. -/
theorem norm_gaussianContourIntegrand (G : ℂ → ℂ) (c x y : ℝ) {Z : ℝ}
    (hZ : 0 < Z) :
    ‖gaussianContourIntegrand G c Z ((x : ℂ) + y * I)‖ =
      Z ^ (x + c) * Real.exp ((x - 5 / 6) ^ 2) *
        ‖G ((x : ℂ) + y * I)‖ * Real.exp (-(y ^ 2)) := by
  unfold gaussianContourIntegrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_exp]
  have hre : ((((x : ℂ) + y * I) - 5 / 6) ^ 2).re = (x - 5 / 6) ^ 2 - y ^ 2 := by
    simp [pow_two]
  rw [hre, Real.exp_sub]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, zero_mul, sub_self,
    add_zero, Real.exp_neg]
  ring

/-- The integrand is holomorphic wherever `G` is. -/
theorem gaussianContourIntegrand_differentiableOn {G : ℂ → ℂ} {U : Set ℂ}
    (hG : DifferentiableOn ℂ G U) (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    DifferentiableOn ℂ (gaussianContourIntegrand G c Z) U := by
  apply DifferentiableOn.mul _ hG
  apply DifferentiableOn.mul
  · exact ((differentiable_id.add_const (c : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).differentiableOn
  · exact (((differentiable_id.sub_const (5 / 6 : ℂ)).pow 2).cexp).differentiableOn

/-! ### The signal of a bounded holomorphic quotient -/

/-- The Gaussian amplitude `e^{(s - 5/6)²} Q(s)`. -/
def gaussianAmp (Q : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * Q s

/-- The signal `x^c · (1/2πi) ∫_{Re s = 2} x^s e^{(s - 5/6)²} Q(s) ds`, written with Mathlib's
inverse Mellin transform: `mellinInv (-2) (s ↦ A(-s)) x = (1/2πi) ∫_{Re s = 2} x^s A(s) ds`. -/
def gaussianSignalOf (Q : ℂ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (c : ℂ) * mellinInv (-2) (fun s => gaussianAmp Q (-s)) x

variable {Q : ℂ → ℂ} {M : ℝ}

/-- `x^{-c} f(x)` is the inverse Mellin transform on `(0, ∞)`. -/
theorem normalizedSignal_gaussianSignalOf (Q : ℂ → ℂ) (c : ℝ) {x : ℝ} (hx : 0 < x) :
    normalizedSignal (gaussianSignalOf Q c) c x =
      mellinInv (-2) (fun s => gaussianAmp Q (-s)) x := by
  unfold normalizedSignal gaussianSignalOf
  simp only [smul_eq_mul, ← mul_assoc]
  rw [Complex.cpow_neg, inv_mul_cancel₀]
  · simp
  · exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hx.ne'])

/-- **The signal as a contour integral** over `Re s = 2`. -/
theorem gaussianSignalOf_eq_contour (Q : ℂ → ℂ) (c : ℝ) {x : ℝ} (hx : 0 < x) :
    gaussianSignalOf Q c x = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand Q c x ((2 : ℂ) + y * I) := by
  unfold gaussianSignalOf mellinInv
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with y
  unfold gaussianContourIntegrand gaussianAmp
  have he : -(((-2 : ℝ) : ℂ) + (-y : ℝ) * I) = (2 : ℂ) + y * I := by push_cast; ring
  rw [he, ← mul_assoc, ← Complex.cpow_add]
  · ring_nf
  · exact Complex.ofReal_ne_zero.mpr hx.ne'

/-- The amplitude is continuous along every vertical line `Re s = a > 1`. -/
theorem gaussianAmp_continuous_line (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re})
    (a : ℝ) (ha : 1 < a) :
    Continuous (fun y : ℝ => gaussianAmp Q ((a : ℂ) + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd : DifferentiableAt ℂ (gaussianAmp Q) ((a : ℂ) + y * I) := by
    unfold gaussianAmp
    exact (((differentiable_id.sub_const (5 / 6 : ℂ)).pow 2).cexp.differentiableAt).mul
      (hQ.differentiableAt ((Complex.isOpen_re_gt 1).mem_nhds (by simpa using ha)))
  have hm : Continuous (fun v : ℝ => (a : ℂ) + v * I) := by fun_prop
  exact hd.continuousAt.comp (f := fun v : ℝ => (a : ℂ) + v * I) hm.continuousAt

/-- The Gaussian bound for the amplitude on `Re s = a ≥ 2`. -/
theorem norm_gaussianAmp_le (hQb : ∀ s : ℂ, 2 ≤ s.re → ‖Q s‖ ≤ M) (a y : ℝ) (ha : 2 ≤ a) :
    ‖gaussianAmp Q ((a : ℂ) + y * I)‖ ≤
      (Real.exp ((a - 5 / 6) ^ 2) * M) * Real.exp (-(y ^ 2)) := by
  have hn := norm_gaussianContourIntegrand Q 0 a y (Z := 1) zero_lt_one
  simp only [gaussianContourIntegrand, Complex.ofReal_one, Complex.ofReal_zero,
    add_zero, Complex.one_cpow, one_mul, Real.one_rpow] at hn
  change ‖gaussianAmp Q ((a : ℂ) + y * I)‖ = _ at hn
  rw [hn]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hQb _ (by simpa using ha)) (Real.exp_pos _).le)
    (Real.exp_pos _).le

/-- The amplitude is integrable along every vertical line `Re s = a ≥ 2`. -/
theorem gaussianAmp_integrable_line (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re})
    (hQb : ∀ s : ℂ, 2 ≤ s.re → ‖Q s‖ ≤ M) (a : ℝ) (ha : 2 ≤ a) :
    Integrable (fun y : ℝ => gaussianAmp Q ((a : ℂ) + y * I)) :=
  integrable_of_gaussian_bound _ _
    (gaussianAmp_continuous_line hQ a (by linarith)).aestronglyMeasurable
    (fun y => norm_gaussianAmp_le hQb a y ha)

/-- **Shifting the signal's line of integration to the right**, for `0 < x ≤ 1`. -/
theorem gaussianSignalOf_contour_shift (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re})
    (hQb : ∀ s : ℂ, 2 ≤ s.re → ‖Q s‖ ≤ M)
    (c B : ℝ) (hB : 2 ≤ B) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    gaussianSignalOf Q c x = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand Q c x ((B : ℂ) + y * I) := by
  rw [gaussianSignalOf_eq_contour Q c hx]
  congr 1
  apply vertical_integral_eq_of_gaussian_bound (C :=
    x ^ (2 + c) * Real.exp ((B - 5 / 6) ^ 2) * M) _ hB
  · apply gaussianContourIntegrand_differentiableOn _ c hx
    exact hQ.mono fun z hz => by
      have hz1 : (2 : ℝ) ≤ z.re := hz.1
      show (1 : ℝ) < z.re
      linarith
  · intro a ha y
    rw [norm_gaussianContourIntegrand _ _ _ _ hx]
    have hxpow : x ^ (a + c) ≤ x ^ (2 + c) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [ha.1])
    have hexp : Real.exp ((a - 5 / 6) ^ 2) ≤ Real.exp ((B - 5 / 6) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ha.1, ha.2]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul _ (hQb _ (by simpa using ha.1)) (norm_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)
    exact mul_le_mul hxpow hexp (Real.exp_pos _).le (Real.rpow_nonneg hx.le _)

/-- The constant of the bound `|f(x)| ≤ C x^{B + c}` on `0 < x ≤ 1`. -/
def gaussianEndpointConstant (M B : ℝ) : ℝ :=
  ‖(1 / (2 * Real.pi) : ℂ)‖ * Real.exp ((B - 5 / 6) ^ 2) * M *
    ∫ y : ℝ, Real.exp (-(y ^ 2))

theorem gaussianEndpointConstant_nonneg {M : ℝ} (hM : 0 ≤ M) (B : ℝ) :
    0 ≤ gaussianEndpointConstant M B := by
  unfold gaussianEndpointConstant
  have hg : 0 ≤ ∫ y : ℝ, Real.exp (-(y ^ 2)) := integral_nonneg (fun _ => (Real.exp_pos _).le)
  positivity

/-- **`|f(x)| ≤ C_B x^{B + c}` on `0 < x ≤ 1`** for every `B ≥ 2` (shift to `Re s = B`). -/
theorem norm_gaussianSignalOf_le (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re})
    (hQb : ∀ s : ℂ, 2 ≤ s.re → ‖Q s‖ ≤ M)
    (c B : ℝ) (hB : 2 ≤ B) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖gaussianSignalOf Q c x‖ ≤ gaussianEndpointConstant M B * x ^ (B + c) := by
  rw [gaussianSignalOf_contour_shift hQ hQb c B hB hx hx1, norm_mul]
  have hg : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hint := norm_integral_le_of_norm_le
    (hg.const_mul (x ^ (B + c) * Real.exp ((B - 5 / 6) ^ 2) * M))
    (f := fun y : ℝ => gaussianContourIntegrand Q c x ((B : ℂ) + y * I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (hQb _ (by simpa using hB))
        (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)))
  have h := mul_le_mul_of_nonneg_left hint (norm_nonneg (1 / (2 * Real.pi) : ℂ))
  rw [integral_const_mul] at h
  convert h using 1 <;> first | rfl | (unfold gaussianEndpointConstant; ring)

/-- **The signal decays rapidly at `0`.** -/
theorem gaussianSignalOf_rapidDecayAtZero (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re})
    (hQb : ∀ s : ℂ, 2 ≤ s.re → ‖Q s‖ ≤ M) (c : ℝ) :
    RapidDecayAtZero (gaussianSignalOf Q c) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hQb 2 (by norm_num))
  intro R
  let B : ℝ := max 2 (R - c)
  apply IsBigO.of_bound (gaussianEndpointConstant M B)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hx1
  have hpow : x ^ (B + c) ≤ x ^ R :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1
      (by dsimp [B]; linarith [le_max_right (2 : ℝ) (R - c)])
  have h := (norm_gaussianSignalOf_le hQ hQb c B (le_max_left _ _) hx hx1).trans
    (mul_le_mul_of_nonneg_left hpow (gaussianEndpointConstant_nonneg hM B))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le R)] using h

/-- The amplitude on `Re s = 2` in the parametrization `2 - 2πiy` of Mellin inversion is
integrable. -/
theorem gaussianAmp_integrable_reflected (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re})
    (hQb : ∀ s : ℂ, 2 ≤ s.re → ‖Q s‖ ≤ M) :
    Integrable (fun y : ℝ => gaussianAmp Q ((2 : ℂ) - 2 * Real.pi * y * I)) := by
  have h := (gaussianAmp_integrable_line hQ hQb 2 le_rfl).comp_mul_left'
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  convert h using 1 <;> first | rfl | (ext y; congr 1; push_cast; ring)

/-- The amplitude on `Re s = 2` in the parametrization `2 - 2πiy` is continuous. -/
theorem gaussianAmp_continuous_reflected (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re}) :
    Continuous (fun y : ℝ => gaussianAmp Q ((2 : ℂ) - 2 * Real.pi * y * I)) := by
  have h := (gaussianAmp_continuous_line hQ 2 (by norm_num)).comp
    (show Continuous (fun y : ℝ => -(2 * Real.pi) * y) by fun_prop)
  convert h using 1 <;> first | rfl | (ext y; congr 1; push_cast; ring)

/-- **The signal is continuous on `(0, ∞)`.** -/
theorem gaussianSignalOf_continuousOn (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re})
    (hQb : ∀ s : ℂ, 2 ≤ s.re → ‖Q s‖ ≤ M) (c : ℝ) :
    ContinuousOn (gaussianSignalOf Q c) (Ioi 0) := by
  let F : ℝ → ℂ := fun y => gaussianAmp Q (-(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I))
  have harg (y : ℝ) : -(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I) =
      (2 : ℂ) - 2 * Real.pi * y * I := by push_cast; ring
  have hF : Integrable F := by
    simpa only [F, harg] using gaussianAmp_integrable_reflected hQ hQb
  have hfour : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hF
  have hinv : Continuous (𝓕⁻ F) := by
    have heq : 𝓕⁻ F = fun w : ℝ => 𝓕 F (-w) := funext (Real.fourierInv_eq_fourier_neg F)
    rw [heq]
    exact hfour.comp continuous_neg
  have hpow (z : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ) ^ z) (Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun _ hx => Complex.ofReal_mem_slitPlane.mpr hx)
  have hlog : ContinuousOn (fun x : ℝ => -Real.log x) (Ioi 0) := by
    intro x hx
    exact (Real.continuousAt_log (ne_of_gt hx)).neg.continuousWithinAt
  apply ((hpow (c : ℂ)).mul ((hpow (2 : ℂ)).mul (hinv.comp_continuousOn hlog))).congr
  intro x hx
  unfold gaussianSignalOf
  rw [mellinInv_eq_fourierInv _ _ hx]
  simp only [smul_eq_mul, Complex.ofReal_neg, neg_neg, Complex.ofReal_ofNat,
    F, Pi.mul_apply, Function.comp_apply]

/-- **The signal is locally integrable on `(0, ∞)`.** -/
theorem gaussianSignalOf_locallyIntegrableOn (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re})
    (hQb : ∀ s : ℂ, 2 ≤ s.re → ‖Q s‖ ≤ M) (c : ℝ) :
    LocallyIntegrableOn (gaussianSignalOf Q c) (Ioi 0) :=
  (gaussianSignalOf_continuousOn hQ hQb c).locallyIntegrableOn measurableSet_Ioi

/-- **Mellin inversion on `Re s = 2`**: `signalMellin f c = e^{(s - 5/6)²} Q(s)` on the line
`Re s = 2`, if the signal is `O(x^{a + c})` at `∞` with `a < 2`. -/
theorem signalMellin_gaussianSignalOf_on_line (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re})
    (hQb : ∀ s : ℂ, 2 ≤ s.re → ‖Q s‖ ≤ M) (c a : ℝ) (ha : a < 2)
    (htop : gaussianSignalOf Q c =O[atTop] (fun x : ℝ => x ^ (a + c))) (y : ℝ) :
    signalMellin (gaussianSignalOf Q c) c ((2 : ℂ) - 2 * Real.pi * y * I) =
      gaussianAmp Q ((2 : ℂ) - 2 * Real.pi * y * I) := by
  apply signalMellin_eq_on_line _ _ c 2
    (signalMellin_convergent _ a c (gaussianSignalOf_locallyIntegrableOn hQ hQb c) htop
      (gaussianSignalOf_rapidDecayAtZero hQ hQb c) (by simpa using ha))
    (gaussianAmp_integrable_reflected hQ hQb) (gaussianAmp_continuous_reflected hQ)
  intro x hx
  exact normalizedSignal_gaussianSignalOf Q c hx

private theorem line_tendsto_punctured :
    Tendsto (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) (𝓝[≠] 0) (𝓝[≠] (2 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hy (by nlinarith [Real.pi_pos])

/-- **The Mellin transform of the signal is the amplitude** on `Re s > max a 1`, if the signal
is `O(x^{a + c})` at `∞` with `a < 2`. -/
theorem signalMellin_gaussianSignalOf (hQ : DifferentiableOn ℂ Q {s : ℂ | 1 < s.re})
    (hQb : ∀ s : ℂ, 2 ≤ s.re → ‖Q s‖ ≤ M) (c a : ℝ) (ha : a < 2)
    (htop : gaussianSignalOf Q c =O[atTop] (fun x : ℝ => x ^ (a + c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    signalMellin (gaussianSignalOf Q c) c s = gaussianAmp Q s := by
  have hF := signalMellin_analytic (gaussianSignalOf Q c) a c
    (gaussianSignalOf_locallyIntegrableOn hQ hQb c) htop
    (gaussianSignalOf_rapidDecayAtZero hQ hQb c)
  have hFa : AnalyticOnNhd ℂ (signalMellin (gaussianSignalOf Q c) c)
      {z : ℂ | max a 1 < z.re} :=
    hF.mono (fun _ hz => (le_max_left a 1).trans_lt hz)
  have hA : AnalyticOnNhd ℂ (gaussianAmp Q) {z : ℂ | max a 1 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
    intro z hz
    have hz1 : (1 : ℝ) < z.re := (le_max_right a 1).trans_lt hz
    have hq : DifferentiableAt ℂ Q z :=
      hQ.differentiableAt ((Complex.isOpen_re_gt 1).mem_nhds hz1)
    exact ((((differentiable_id.sub_const (5 / 6 : ℂ)).pow 2).cexp.differentiableAt).mul
      hq).differentiableWithinAt
  apply hFa.eqOn_of_preconnected_of_frequently_eq hA (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (2 : ℂ)) (by simpa using max_lt ha (by norm_num : (1 : ℝ) < 2)) _ hs
  apply line_tendsto_punctured.frequently
  exact Filter.Frequently.of_forall
    (fun y => signalMellin_gaussianSignalOf_on_line hQ hQb c a ha htop y)

end Analysis

/-! ### `L(s, χ)` on `Re s > 1` -/

section RayClass

open Filter Asymptotics TauCeti TauCeti.GlobalNumberFields NumberField
open IsDedekindDomain (HeightOneSpectrum)
open scoped Topology nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

open Classical in
/-- The values of a ray class character on all integral ideals: `χ(𝔞)` on the ideals prime to the
modulus, `0` on the others. -/
def rayWeightFun (χ : RayClassCharacter 𝔪) (I : Ideal (𝓞 K)) : ℂ :=
  if h : I ∈ integralIdealsPrimeTo 𝔪 then ((χ.onIdeals ⟨I, h⟩ : ℂˣ) : ℂ) else 0

theorem rayWeightFun_of_mem (χ : RayClassCharacter 𝔪) {I : Ideal (𝓞 K)}
    (h : I ∈ integralIdealsPrimeTo 𝔪) : rayWeightFun χ I = ((χ.onIdeals ⟨I, h⟩ : ℂˣ) : ℂ) := by
  unfold rayWeightFun
  rw [dif_pos h]

theorem rayWeightFun_of_notMem (χ : RayClassCharacter 𝔪) {I : Ideal (𝓞 K)}
    (h : I ∉ integralIdealsPrimeTo 𝔪) : rayWeightFun χ I = 0 := by
  unfold rayWeightFun
  rw [dif_neg h]

/-- The weight of a ray class character is bounded by `1`. -/
theorem norm_rayWeightFun_le (χ : RayClassCharacter 𝔪) (I : Ideal (𝓞 K)) :
    ‖rayWeightFun χ I‖ ≤ 1 := by
  by_cases h : I ∈ integralIdealsPrimeTo 𝔪
  · rw [rayWeightFun_of_mem χ h, RayClassCharacter.onIdeals_apply]
    exact (norm_rayClassCharacter χ _).le
  · rw [rayWeightFun_of_notMem χ h, norm_zero]
    exact zero_le_one

/-- **A ray class character as a completely multiplicative ideal weight**, so that Tau Ceti's
Euler-product API applies to `L(s, χ)`. -/
def rayWeight (χ : RayClassCharacter 𝔪) : MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun := rayWeightFun χ
      map_zero' := rayWeightFun_of_notMem χ fun h =>
        (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp h).1 Ideal.zero_eq_bot
      map_one' := by
        rw [rayWeightFun_of_mem χ (integralIdealsPrimeTo 𝔪).one_mem]
        have h1 : (⟨1, (integralIdealsPrimeTo 𝔪).one_mem⟩ : integralIdealsPrimeTo 𝔪) = 1 := rfl
        rw [h1, map_one, Units.val_one]
      map_mul' := fun I J => by
        by_cases hIJ : I * J ∈ integralIdealsPrimeTo 𝔪
        · have h2 := Ideal.isPrimeTo_mul_iff.mp
            (NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mp hIJ)
          have hI : I ∈ integralIdealsPrimeTo 𝔪 :=
            NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mpr h2.1
          have hJ : J ∈ integralIdealsPrimeTo 𝔪 :=
            NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mpr h2.2
          rw [rayWeightFun_of_mem χ hIJ, rayWeightFun_of_mem χ hI, rayWeightFun_of_mem χ hJ,
            ← Units.val_mul, ← map_mul]
          rfl
        · rw [rayWeightFun_of_notMem χ hIJ]
          by_cases hI : I ∈ integralIdealsPrimeTo 𝔪
          · have hJ : J ∉ integralIdealsPrimeTo 𝔪 := fun hJ => hIJ
              (NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mpr
                (Ideal.isPrimeTo_mul_iff.mpr
                  ⟨NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mp hI,
                    NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mp hJ⟩))
            rw [rayWeightFun_of_notMem χ hJ, mul_zero]
          · rw [rayWeightFun_of_notMem χ hI, zero_mul] }
  finite_setOf_apply_eq_zero := by
    refine 𝔪.support.finite_toSet.subset fun 𝔭 h𝔭 => ?_
    by_contra hn
    have hmem : 𝔭.asIdeal ∈ integralIdealsPrimeTo 𝔪 :=
      NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mpr
        (Ideal.isPrimeTo_asIdeal_iff.mpr hn)
    have h0 : rayWeightFun χ 𝔭.asIdeal = 0 := h𝔭
    rw [rayWeightFun_of_mem χ hmem] at h0
    exact Units.ne_zero _ h0

theorem rayWeight_apply (χ : RayClassCharacter 𝔪) (I : Ideal (𝓞 K)) :
    rayWeight χ I = rayWeightFun χ I := rfl

/-- The ideal coefficients of `L(s, χ)` are those of the weight `rayWeight χ`. -/
theorem rayCoeff_eq_rayWeight (χ : RayClassCharacter 𝔪) :
    rayCoeff χ = (rayWeight χ).toIdealArithmeticFunction := by
  funext I
  rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply, rayWeight_apply]
  unfold rayCoeff
  by_cases h : (I : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪
  · rw [dif_pos h, rayWeightFun_of_mem χ h]
  · rw [dif_neg h, rayWeightFun_of_notMem χ h]

theorem rayClassLSeries_eq_LSeries_rayWeight (χ : RayClassCharacter 𝔪) (s : ℂ) :
    rayClassLSeries χ s = LSeries (normCoeff K (rayWeight χ).toIdealArithmeticFunction) s := by
  rw [rayClassLSeries, rayCoeff_eq_rayWeight]

theorem summable_idealTerm_rayWeight (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    Summable (idealTerm K (rayWeight χ).toIdealArithmeticFunction s) := by
  rw [← rayCoeff_eq_rayWeight]
  exact summable_idealTerm_rayCoeff χ hs

/-- **`L(s, χ)` does not vanish on `Re s > 1`** (the Euler product). -/
theorem rayClassLSeries_ne_zero (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    rayClassLSeries χ s ≠ 0 := by
  rw [rayClassLSeries_eq_LSeries_rayWeight]
  exact MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm _
    (summable_idealTerm_rayWeight χ hs)

/-- **`L(s, χ)` is holomorphic on `Re s > 1`.** -/
theorem rayClassLSeries_analyticOnNhd (χ : RayClassCharacter 𝔪) :
    AnalyticOnNhd ℂ (rayClassLSeries χ) {s : ℂ | 1 < s.re} := by
  refine (LSeries_analyticOnNhd (normCoeff K (rayCoeff χ))).mono fun z hz => ?_
  have hz' : (1 : ℝ) < z.re := hz
  show LSeries.abscissaOfAbsConv (normCoeff K (rayCoeff χ)) < z.re
  calc LSeries.abscissaOfAbsConv (normCoeff K (rayCoeff χ)) ≤ 1 :=
        abscissaOfAbsConv_rayClassLSeries_le χ
    _ < z.re := by exact_mod_cast hz'

theorem rayClassLSeries_differentiableAt (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (rayClassLSeries χ) s :=
  (rayClassLSeries_analyticOnNhd χ s hs).differentiableAt

variable (K) in
/-- The bound `exp(∑_𝔭 N𝔭^{-2})` for `|1 / L(s, χ)|` on `Re s ≥ 2`. -/
def rayInvBound : ℝ :=
  Real.exp (∑' P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ))

/-- **`|1 / L(s, χ)| ≤ exp(∑_𝔭 N𝔭^{-2})` on `Re s ≥ 2`**, from the Euler product
`1 / L(s, χ) = ∏_𝔭 (1 - χ(𝔭) N𝔭^{-s})`. -/
theorem norm_inv_rayClassLSeries_le (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(rayClassLSeries χ s)⁻¹‖ ≤ rayInvBound K := by
  have hs1 : 1 < s.re := by linarith
  set w := rayWeight χ with hw
  have hsum := summable_idealTerm_rayWeight χ hs1
  have hprod := MultiplicativeIdealWeight.hasProd_eulerFactor w hsum
  have hne := MultiplicativeIdealWeight.LSeries_ne_zero_of_summable_idealTerm w hsum
  have hinv := hprod.inv₀ hne
  simp only [inv_inv] at hinv
  have hnorm := hinv.norm
  rw [rayClassLSeries_eq_LSeries_rayWeight]
  have hP2 : Summable fun P : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ) :=
    summable_absNorm_rpow_primes_of_one_lt (by norm_num)
  have ha : ∀ P : HeightOneSpectrum (𝓞 K),
      ‖w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ ≤
        (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ) := by
    intro P
    have hN : 1 < Ideal.absNorm P.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm P
    have hN1 : (1 : ℝ) ≤ (Ideal.absNorm P.asIdeal : ℝ) := by exact_mod_cast hN.le
    have hNpos : (0 : ℝ) < (Ideal.absNorm P.asIdeal : ℝ) := by linarith
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega)]
    calc ‖w P.asIdeal‖ / (Ideal.absNorm P.asIdeal : ℝ) ^ s.re
        ≤ 1 / (Ideal.absNorm P.asIdeal : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right (norm_rayWeightFun_le χ _)
            (Real.rpow_nonneg hNpos.le _)
      _ = (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
          rw [Real.rpow_neg hNpos.le, one_div]
      _ ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  refine le_of_tendsto' hnorm fun t => (Finset.norm_prod_le _ _).trans ?_
  calc ∏ P ∈ t, ‖1 - w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖
      ≤ ∏ P ∈ t, Real.exp ‖w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun P _ => ?_
        calc ‖1 - w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖
            ≤ ‖(1 : ℂ)‖ + ‖w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ := norm_sub_le _ _
          _ = ‖w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ + 1 := by
            rw [norm_one, add_comm]
          _ ≤ _ := Real.add_one_le_exp _
    _ = Real.exp (∑ P ∈ t, ‖w P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖) :=
        (Real.exp_sum _ _).symm
    _ ≤ rayInvBound K := by
        unfold rayInvBound
        refine Real.exp_le_exp.mpr ?_
        exact (Finset.sum_le_sum fun P _ => ha P).trans
          (hP2.sum_le_tsum t fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **`1 / L(s, χ)` is bounded on `Re s ≥ 2`.** -/
theorem exists_norm_inv_rayClassLSeries_le (χ : RayClassCharacter 𝔪) :
    ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(rayClassLSeries χ s)⁻¹‖ ≤ C :=
  ⟨rayInvBound K, fun _ hs => norm_inv_rayClassLSeries_le χ hs⟩

/-! ### [A]'s signal -/

/-- The quotient `H(s) / L(s, χ)`. -/
def rayQuotient (χ : RayClassCharacter 𝔪) (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  H s * (rayClassLSeries χ s)⁻¹

/-- **[A]'s signal**

`f(Z) = (1/2πi) ∫_{Re s = 2} Z^{s - 8/15} e^{(s - 5/6)²} H(s) / L(s, χ) ds`   (`Z > 0`),

written with Mathlib's inverse Mellin transform
`mellinInv σ F Z = (1/2π) ∫_ℝ Z^{-(σ + it)} F(σ + it) dt`: for
`A(s) = e^{(s - 5/6)²} H(s) / L(s, χ)`, `mellinInv (-2) (s ↦ A(-s)) Z` is
`(1/2πi) ∫_{Re s = 2} Z^s A(s) ds`, and `f(Z)` is `Z^{-8/15}` times this
(`gaussianSignal_eq_integral` states the formula). The value at `Z ≤ 0` is irrelevant. -/
def gaussianSignal (χ : RayClassCharacter 𝔪) (H : ℂ → ℂ) (Z : ℝ) : ℂ :=
  (Z : ℂ) ^ ((-8 / 15 : ℝ) : ℂ) * mellinInv (-2)
    (fun s => Complex.exp ((-s - 5 / 6) ^ 2) * (H (-s) * (rayClassLSeries χ (-s))⁻¹)) Z

/-- [A]'s signal is the signal of the quotient `H / L(·, χ)` with `c = -8/15`. -/
theorem gaussianSignal_eq_gaussianSignalOf (χ : RayClassCharacter 𝔪) (H : ℂ → ℂ) :
    gaussianSignal χ H = gaussianSignalOf (rayQuotient χ H) (-8 / 15) :=
  rfl

/-- **[A]'s signal as a contour integral** over the line `Re s = 2`, `s = 2 + it`:
`f(Z) = (1/2π) ∫_ℝ Z^{s - 8/15} e^{(s - 5/6)²} H(s) / L(s, χ) dt`. -/
theorem gaussianSignal_eq_integral (χ : RayClassCharacter 𝔪) (H : ℂ → ℂ) {Z : ℝ} (hZ : 0 < Z) :
    gaussianSignal χ H Z = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (Z : ℂ) ^ ((2 + t * Complex.I) - 8 / 15) *
        Complex.exp ((2 + t * Complex.I - 5 / 6) ^ 2) *
          (H (2 + t * Complex.I) / rayClassLSeries χ (2 + t * Complex.I)) := by
  rw [gaussianSignal_eq_gaussianSignalOf, gaussianSignalOf_eq_contour _ _ hZ]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [gaussianContourIntegrand, rayQuotient, div_eq_mul_inv]
  congr 3
  push_cast
  ring

/-- **[A]'s signal bound gives a Mellin signal** (step Z6, analytic part). Let `H` be holomorphic
and nowhere zero on `Re s > 1 - κ` and bounded on `Re s ≥ 2`. If [A]'s signal
`f = gaussianSignal χ H` satisfies `f(Z) ≪ Z^{1 - κ - 8/15}` as `Z → ∞`, then `(H, f)` is a Mellin
signal of width `κ` for `χ`: `f` is locally integrable on `(0, ∞)` and decays rapidly at `0`, and
`L(s, χ) · ∫₀^∞ f(Z) Z^{-s+8/15} dZ/Z = e^{(s-5/6)²} H(s)` on `Re s > 1`.

The hypothesis `hκ1 : κ < 1` is not needed by the proof (only `0 < κ` is); it records [A]'s
range of widths. -/
theorem hasMellinSignal_of_isBigO {𝔪 : Modulus K} {χ : RayClassCharacter 𝔪} {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H {s : ℂ | 1 - κ < s.re}) (hH0 : ∀ s : ℂ, 1 - κ < s.re → H s ≠ 0)
    (hHb : ∃ C, ∀ s : ℂ, 2 ≤ s.re → ‖H s‖ ≤ C)
    (hbound : gaussianSignal χ H =O[atTop] (fun Z : ℝ => Z ^ (1 - κ + (-8 / 15 : ℝ)))) :
    HasMellinSignal χ κ := by
  obtain ⟨C, hC⟩ := hHb
  have hQ : DifferentiableOn ℂ (rayQuotient χ H) {s : ℂ | 1 < s.re} := by
    intro s hs
    have hs1 : (1 : ℝ) < s.re := hs
    have hHd : DifferentiableAt ℂ H s :=
      (hH s (show 1 - κ < s.re by linarith)).differentiableAt
    exact (hHd.mul ((rayClassLSeries_differentiableAt χ hs1).inv
      (rayClassLSeries_ne_zero χ hs1))).differentiableWithinAt
  have hQb : ∀ s : ℂ, 2 ≤ s.re → ‖rayQuotient χ H s‖ ≤ C * rayInvBound K := by
    intro s hs
    rw [rayQuotient, norm_mul]
    exact mul_le_mul (hC s hs) (norm_inv_rayClassLSeries_le χ hs) (norm_nonneg _)
      ((norm_nonneg _).trans (hC s hs))
  rw [gaussianSignal_eq_gaussianSignalOf] at hbound
  have ha : 1 - κ < 2 := by linarith [hκ, hκ1]
  refine ⟨H, gaussianSignalOf (rayQuotient χ H) (-8 / 15), hH, hH0,
    gaussianSignalOf_locallyIntegrableOn hQ hQb _, gaussianSignalOf_rapidDecayAtZero hQ hQb _,
    hbound, fun s hs => ?_⟩
  have hmax : max (1 - κ) 1 < s.re := by
    rw [max_eq_right (by linarith)]
    exact hs
  rw [signalMellin_gaussianSignalOf hQ hQb (-8 / 15) (1 - κ) ha hbound hmax, gaussianAmp,
    rayQuotient]
  have hL := rayClassLSeries_ne_zero χ hs
  calc rayClassLSeries χ s * (Complex.exp ((s - 5 / 6) ^ 2) * (H s * (rayClassLSeries χ s)⁻¹))
      = Complex.exp ((s - 5 / 6) ^ 2) * H s * (rayClassLSeries χ s * (rayClassLSeries χ s)⁻¹) := by
        ring
    _ = Complex.exp ((s - 5 / 6) ^ 2) * H s := by rw [mul_inv_cancel₀ hL, mul_one]

end RayClass

end

end SimultaneousPrimitiveRoots.Unconditional
