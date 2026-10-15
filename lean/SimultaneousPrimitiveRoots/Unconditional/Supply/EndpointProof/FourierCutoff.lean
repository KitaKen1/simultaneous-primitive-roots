module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Fourier separation of the smooth cutoff in logarithmic size, with explicit constants

`[P-06:0723–0725]`: "Divide all factors into dyads and Fourier-separate the smooth product cutoff
in logarithmic size. … Retain only shifts of fixed log-power size."

The cutoff `ψ₁` of (cor:SM) varies with `x`; only its support `[a₁, a₂] ⊂ (0, ∞)` and bounds
`‖ψ₁^{(j)}‖ ≤ L^{Dψ j}` are fixed. So the separation is needed with constants that depend on `ψ₁`
only through `sup |ψ₁|`, `sup |ψ₁'|`, `sup |ψ₁''|`. Here it is done with a Fourier *series* in
`u = log y` on the period `[log(a₁/8), log(8a₂))`, which contains `log y` for all
`a₁/4 ≤ y ≤ 4a₂` (the range of `w/Y` in a dyadic box): the retained twists are then the finitely
many `y^{iκn}`, `|n| ≤ N`, `κ = 2π/Λ`, `Λ = log(64a₂/a₁)`.

* `norm_fourierCoeffOn_le`, `norm_fourierCoeffOn_le_of_deriv2`: `|c_n(f)| ≤ sup|f|` and, after two
  integrations by parts (`fourierCoeffOn_of_hasDerivAt`), `|c_n(f)| ≤ (b-a)² sup|f''| / n²`.
* `hasSum_fourier_of_deriv2`: the Fourier series of such an `f` converges to `f` on `[a, a+T)`
  (`has_pointwise_sum_fourier_series_of_summable`).
* `norm_sub_fourier_partial_le`: `|f(x) - ∑_{|n| ≤ N} c_n e^{2πinx/T}| ≤ 4T² sup|f''| / N`.
* `cutoff_fourier`: **the separation of the cutoff**. For `ψ` smooth with support in `[a₁, a₂]`,
  `|ψ| ≤ B₀`, `|ψ'| ≤ B₁`, `|ψ''| ≤ B₂` there are coefficients `|c_n| ≤ B₀` with
  `|ψ(y) - ∑_{|n| ≤ N} c_n y^{iκn}| ≤ K(a₁, a₂) (B₁ + B₂) / N` for `a₁/4 ≤ y ≤ 4a₂`, `N ≥ 1`
  (`cutoffFreq = κ`, `cutoffConst = K`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace FourierCutoff

/-! ### Fourier coefficients on an interval -/

/-- `|e^{2πinx/T}| = 1`. -/
theorem norm_exp_fourier (T x : ℝ) (n : ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * n * x / T)‖ = 1 := by
  rw [← fourier_coe_apply, fourier_apply, Circle.norm_coe]

/-- `|c_n(f)| ≤ sup_{[a,b]} |f|`. -/
theorem norm_fourierCoeffOn_le {a b : ℝ} (hab : a < b) {f : ℝ → ℂ} {B : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ B) (n : ℤ) : ‖fourierCoeffOn hab f n‖ ≤ B := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have h1 : ‖∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x‖ ≤ B * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le hab.le] at hx
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact hf x ⟨hx.1.le, hx.2⟩
  rw [abs_of_pos hba] at h1
  rw [fourierCoeffOn_eq_integral, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hba)]
  calc 1 / (b - a) * ‖∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x‖
      ≤ 1 / (b - a) * (B * (b - a)) := mul_le_mul_of_nonneg_left h1 (one_div_pos.mpr hba).le
    _ = B := by
        rw [one_div, mul_comm B, ← mul_assoc, inv_mul_cancel₀ hba.ne', one_mul]

/-- One integration by parts: `|c_n(f)| ≤ (b - a)/|n| · |c_n(f')|` when `f(a) = f(b)`. -/
theorem norm_fourierCoeffOn_le_of_deriv {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x) (hc' : Continuous f') (hfab : f a = f b)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn hab f n‖ ≤ (b - a) / |(n : ℝ)| * ‖fourierCoeffOn hab f' n‖ := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hnR : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
  have e1 := fourierCoeffOn_of_hasDerivAt hab hn hf (hc'.intervalIntegrable a b)
  rw [hfab, sub_self, mul_zero, zero_sub] at e1
  have hden : ‖(-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ = 2 * Real.pi * |(n : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_two, Complex.norm_I, mul_one,
      Complex.norm_real, Complex.norm_intCast, Real.norm_of_nonneg Real.pi_pos.le]
  have hden1 : |(n : ℝ)| ≤ ‖(-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ := by
    rw [hden]
    have h2 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
    exact le_mul_of_one_le_left hnR.le h2
  have hba' : ‖((b : ℂ) - (a : ℂ))‖ = b - a := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hba.le]
  have hq : 1 / ‖(-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ ≤ 1 / |(n : ℝ)| :=
    one_div_le_one_div_of_le hnR hden1
  rw [e1, norm_mul, norm_neg, norm_mul, norm_div, norm_one, hba']
  calc 1 / ‖(-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ * ((b - a) * ‖fourierCoeffOn hab f' n‖)
      ≤ 1 / |(n : ℝ)| * ((b - a) * ‖fourierCoeffOn hab f' n‖) :=
        mul_le_mul_of_nonneg_right hq (mul_nonneg hba.le (norm_nonneg _))
    _ = (b - a) / |(n : ℝ)| * ‖fourierCoeffOn hab f' n‖ := by ring

/-- Two integrations by parts: `|c_n(f)| ≤ (b - a)² sup|f''| / n²` when `f` and `f'` take the same
values at `a` and `b`. -/
theorem norm_fourierCoeffOn_le_of_deriv2 {a b : ℝ} (hab : a < b) {f f' f'' : ℝ → ℂ}
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.uIcc a b, HasDerivAt f' (f'' x) x)
    (hc' : Continuous f') (hc'' : Continuous f'') (hfab : f a = f b) (hf'ab : f' a = f' b)
    {B₂ : ℝ} (hB : ∀ x ∈ Set.Icc a b, ‖f'' x‖ ≤ B₂) {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn hab f n‖ ≤ (b - a) ^ 2 * B₂ * ((n : ℝ) ^ 2)⁻¹ := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hnR : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
  have h1 := norm_fourierCoeffOn_le_of_deriv hab hf hc' hfab hn
  have h2 := norm_fourierCoeffOn_le_of_deriv hab hf' hc'' hf'ab hn
  have h3 := norm_fourierCoeffOn_le hab hB n
  have hq : 0 ≤ (b - a) / |(n : ℝ)| := div_nonneg hba.le hnR.le
  have hsq : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
  calc ‖fourierCoeffOn hab f n‖
      ≤ (b - a) / |(n : ℝ)| * ‖fourierCoeffOn hab f' n‖ := h1
    _ ≤ (b - a) / |(n : ℝ)| * ((b - a) / |(n : ℝ)| * B₂) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hq)) hq
    _ = (b - a) ^ 2 * B₂ * ((n : ℝ) ^ 2)⁻¹ := by
        rw [hsq, div_eq_mul_inv]
        ring

/-! ### Convergence -/

/-- **The Fourier series of a `C²` function on a period**: if `f` and `f'` take the same values
at `a` and `a + T` and `|f''| ≤ B₂` on `[a, a + T]`, then
`f(x) = ∑_n c_n(f) e^{2πinx/T}` for `a ≤ x < a + T`. -/
theorem hasSum_fourier_of_deriv2 {a T : ℝ} (hT : 0 < T) {f f' f'' : ℝ → ℂ}
    (hf : ∀ x ∈ Set.uIcc a (a + T), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.uIcc a (a + T), HasDerivAt f' (f'' x) x)
    (hc : Continuous f) (hc' : Continuous f') (hc'' : Continuous f'')
    (hfab : f a = f (a + T)) (hf'ab : f' a = f' (a + T))
    {B₂ : ℝ} (hB : ∀ x ∈ Set.Icc a (a + T), ‖f'' x‖ ≤ B₂)
    {x : ℝ} (hx : x ∈ Set.Ico a (a + T)) :
    HasSum (fun n : ℤ => fourierCoeffOn (lt_add_of_pos_right a hT) f n *
        Complex.exp (2 * Real.pi * Complex.I * n * x / T)) (f x) := by
  have : Fact (0 < T) := ⟨hT⟩
  have hab : a < a + T := lt_add_of_pos_right a hT
  have hcont : Continuous (AddCircle.liftIco T a f) :=
    AddCircle.liftIco_continuous hfab hc.continuousOn
  obtain ⟨F, hF⟩ : ∃ F : C(AddCircle T, ℂ), ∀ y, F y = AddCircle.liftIco T a f y :=
    ⟨⟨AddCircle.liftIco T a f, hcont⟩, fun _ => rfl⟩
  have hcoef : ∀ n : ℤ, fourierCoeff F n = fourierCoeffOn hab f n := by
    intro n
    have hFf : (F : AddCircle T → ℂ) = AddCircle.liftIco T a f := funext hF
    rw [hFf]
    exact fourierCoeff_liftIco_eq f n
  have hbound : ∀ n : ℤ, n ≠ 0 → ‖fourierCoeff F n‖ ≤ T ^ 2 * B₂ * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    rw [hcoef n]
    have h := norm_fourierCoeffOn_le_of_deriv2 hab hf hf' hc' hc'' hfab hf'ab hB hn
    rw [add_sub_cancel_left] at h
    rw [one_div]
    exact h
  have hsummable : Summable (fourierCoeff F) := by
    have hg : Summable fun n : ℤ => T ^ 2 * B₂ * (1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_int_pow.mpr one_lt_two).mul_left _
    refine Summable.of_norm_bounded_eventually hg ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton (0 : ℤ)).subset fun n hn => ?_
    have hn' : ¬ ‖fourierCoeff F n‖ ≤ T ^ 2 * B₂ * (1 / (n : ℝ) ^ 2) := hn
    by_contra h0
    exact hn' (hbound n fun h => h0 (Set.mem_singleton_iff.mpr h))
  have hsum := has_pointwise_sum_fourier_series_of_summable hsummable (x : AddCircle T)
  have hFx : F (x : AddCircle T) = f x := by
    rw [hF]
    exact AddCircle.liftIco_coe_apply hx
  rw [hFx] at hsum
  have hfun : (fun n : ℤ => fourierCoeffOn hab f n *
      Complex.exp (2 * Real.pi * Complex.I * n * x / T)) =
        fun i : ℤ => fourierCoeff F i • fourier i (x : AddCircle T) := by
    funext n
    rw [hcoef n, fourier_coe_apply, smul_eq_mul]
  exact (congrArg (fun g : ℤ → ℂ => HasSum g (f x)) hfun).mpr hsum

/-! ### Tails -/

/-- A finite set of integers on which `natAbs` is injective and `> N`: `∑ 1/n² ≤ 2/(N+1)`. -/
theorem sum_inv_sq_natAbs_le {N : ℕ} (t : Finset ℤ) (hinj : Set.InjOn Int.natAbs (t : Set ℤ))
    (ht : ∀ n ∈ t, N < n.natAbs) : ∑ n ∈ t, ((n : ℝ) ^ 2)⁻¹ ≤ 2 / ((N : ℝ) + 1) := by
  have hcast : ∀ n : ℤ, ((n : ℝ) ^ 2)⁻¹ = (((n.natAbs : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro n
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have h1 : ∑ n ∈ t, ((n : ℝ) ^ 2)⁻¹ = ∑ m ∈ t.image Int.natAbs, (((m : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun n _ => hcast n
  have hsub : t.image Int.natAbs ⊆ Finset.Ioo N (t.sup Int.natAbs + 1) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_Ioo.mpr ⟨ht n hn, Nat.lt_succ_of_le (Finset.le_sup hn)⟩
  rw [h1]
  calc ∑ m ∈ t.image Int.natAbs, (((m : ℕ) : ℝ) ^ 2)⁻¹
      ≤ ∑ m ∈ Finset.Ioo N (t.sup Int.natAbs + 1), (((m : ℕ) : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => inv_nonneg.mpr (sq_nonneg _)
    _ ≤ 2 / ((N : ℝ) + 1) := sum_Ioo_inv_sq_le N _

/-- A finite set of integers outside `[-N, N]`: `∑ 1/n² ≤ 4/(N+1)`. -/
theorem sum_inv_sq_le_of_notMem {N : ℕ} (t : Finset ℤ)
    (ht : ∀ n ∈ t, n ∉ Finset.Icc (-(N : ℤ)) N) :
    ∑ n ∈ t, ((n : ℝ) ^ 2)⁻¹ ≤ 4 / ((N : ℝ) + 1) := by
  have habs : ∀ n ∈ t, N < n.natAbs := by
    intro n hn
    have h := ht n hn
    rw [Finset.mem_Icc] at h
    omega
  have hsplit := Finset.sum_filter_add_sum_filter_not t (fun n : ℤ => 0 ≤ n)
    (fun n : ℤ => ((n : ℝ) ^ 2)⁻¹)
  have h1 : ∑ n ∈ t.filter (fun n : ℤ => 0 ≤ n), ((n : ℝ) ^ 2)⁻¹ ≤ 2 / ((N : ℝ) + 1) := by
    refine sum_inv_sq_natAbs_le _ ?_ fun n hn => habs n (Finset.mem_filter.mp hn).1
    intro n hn m hm hnm
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2
    have hnm' : n.natAbs = m.natAbs := hnm
    omega
  have h2 : ∑ n ∈ t.filter (fun n : ℤ => ¬ 0 ≤ n), ((n : ℝ) ^ 2)⁻¹ ≤ 2 / ((N : ℝ) + 1) := by
    refine sum_inv_sq_natAbs_le _ ?_ fun n hn => habs n (Finset.mem_filter.mp hn).1
    intro n hn m hm hnm
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2
    have hnm' : n.natAbs = m.natAbs := hnm
    omega
  have e : (4 : ℝ) / ((N : ℝ) + 1) = 2 / ((N : ℝ) + 1) + 2 / ((N : ℝ) + 1) := by ring
  rw [← hsplit, e]
  exact add_le_add h1 h2

/-- The distance from the sum of a series to a partial sum, from a bound for the finite sums of
the norms of the remaining terms. -/
theorem norm_sub_sum_le_of_hasSum {f : ℤ → ℂ} {a : ℂ} (hf : HasSum f a) (s : Finset ℤ) {B : ℝ}
    (hB : ∀ t : Finset ℤ, Disjoint t s → ∑ n ∈ t, ‖f n‖ ≤ B) : ‖a - ∑ n ∈ s, f n‖ ≤ B := by
  have hf' : Filter.Tendsto (fun t : Finset ℤ => ∑ n ∈ t, f n) Filter.atTop (nhds a) := hf
  have hlim : Filter.Tendsto (fun t : Finset ℤ => ‖∑ n ∈ t, f n - ∑ n ∈ s, f n‖) Filter.atTop
      (nhds ‖a - ∑ n ∈ s, f n‖) := (hf'.sub_const _).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop s] with t hst
  have hsd : ∑ n ∈ t, f n - ∑ n ∈ s, f n = ∑ n ∈ t \ s, f n := by
    rw [← Finset.sum_sdiff (f := f) hst, add_sub_cancel_right]
  rw [hsd]
  exact (norm_sum_le _ _).trans (hB _ Finset.sdiff_disjoint)

/-- **The truncated Fourier series**: under the hypotheses of `hasSum_fourier_of_deriv2`,
`|f(x) - ∑_{|n| ≤ N} c_n e^{2πinx/T}| ≤ 4 T² B₂ / N` for `N ≥ 1`. -/
theorem norm_sub_fourier_partial_le {a T : ℝ} (hT : 0 < T) {f f' f'' : ℝ → ℂ}
    (hf : ∀ x ∈ Set.uIcc a (a + T), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.uIcc a (a + T), HasDerivAt f' (f'' x) x)
    (hc : Continuous f) (hc' : Continuous f') (hc'' : Continuous f'')
    (hfab : f a = f (a + T)) (hf'ab : f' a = f' (a + T))
    {B₂ : ℝ} (hB₂0 : 0 ≤ B₂) (hB : ∀ x ∈ Set.Icc a (a + T), ‖f'' x‖ ≤ B₂)
    {x : ℝ} (hx : x ∈ Set.Ico a (a + T)) {N : ℕ} (hN : 0 < N) :
    ‖f x - ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierCoeffOn (lt_add_of_pos_right a hT) f n *
        Complex.exp (2 * Real.pi * Complex.I * n * x / T)‖ ≤ 4 * T ^ 2 * B₂ / N := by
  have hab : a < a + T := lt_add_of_pos_right a hT
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsum := hasSum_fourier_of_deriv2 hT hf hf' hc hc' hc'' hfab hf'ab hB hx
  refine norm_sub_sum_le_of_hasSum hsum _ fun t ht => ?_
  have hnot : ∀ n ∈ t, n ∉ Finset.Icc (-(N : ℤ)) N := fun n hn hmem =>
    Finset.disjoint_left.mp ht hn hmem
  have hne : ∀ n ∈ t, n ≠ 0 := by
    intro n hn h0
    refine hnot n hn (Finset.mem_Icc.mpr ?_)
    rw [h0]
    constructor <;> omega
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have h4 : (4 : ℝ) / ((N : ℝ) + 1) ≤ 4 / N := by
    rw [div_le_div_iff₀ hN1 hN']
    linarith
  calc ∑ n ∈ t, ‖fourierCoeffOn hab f n * Complex.exp (2 * Real.pi * Complex.I * n * x / T)‖
      ≤ ∑ n ∈ t, T ^ 2 * B₂ * ((n : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum fun n hn => by
        rw [norm_mul, norm_exp_fourier, mul_one]
        have h := norm_fourierCoeffOn_le_of_deriv2 hab hf hf' hc' hc'' hfab hf'ab hB (hne n hn)
        rw [add_sub_cancel_left] at h
        exact h
    _ = T ^ 2 * B₂ * ∑ n ∈ t, ((n : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ T ^ 2 * B₂ * (4 / ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le_of_notMem t hnot)
          (mul_nonneg (sq_nonneg T) hB₂0)
    _ ≤ T ^ 2 * B₂ * (4 / N) :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg (sq_nonneg T) hB₂0)
    _ = 4 * T ^ 2 * B₂ / N := by ring

end FourierCutoff

/-! ### The cutoff -/

/-- The period `Λ = log(8a₂) - log(a₁/8) = log(64 a₂/a₁)` of the logarithmic variable. -/
def cutoffPeriod (a₁ a₂ : ℝ) : ℝ := Real.log (8 * a₂) - Real.log (a₁ / 8)

/-- The spacing `κ = 2π/Λ` of the retained twists `y^{iκn}`. -/
def cutoffFreq (a₁ a₂ : ℝ) : ℝ := 2 * Real.pi / cutoffPeriod a₁ a₂

/-- The constant `K(a₁, a₂) = 4Λ²(8a₂ + 64a₂²)` of the truncation error. -/
def cutoffConst (a₁ a₂ : ℝ) : ℝ := 4 * cutoffPeriod a₁ a₂ ^ 2 * (8 * a₂ + 64 * a₂ ^ 2)

theorem cutoffPeriod_pos {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha : a₁ ≤ a₂) : 0 < cutoffPeriod a₁ a₂ := by
  unfold cutoffPeriod
  have h : a₁ / 8 < 8 * a₂ := by linarith
  exact sub_pos.mpr (Real.log_lt_log (div_pos ha₁ (by norm_num)) h)

theorem cutoffFreq_pos {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha : a₁ ≤ a₂) : 0 < cutoffFreq a₁ a₂ := by
  unfold cutoffFreq
  exact div_pos (mul_pos two_pos Real.pi_pos) (cutoffPeriod_pos ha₁ ha)

theorem cutoffConst_nonneg {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha : a₁ ≤ a₂) : 0 ≤ cutoffConst a₁ a₂ := by
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha
  unfold cutoffConst
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (add_nonneg (mul_nonneg (by norm_num) ha₂.le) (mul_nonneg (by norm_num) (sq_nonneg _)))

/-- **Fourier separation of the cutoff in logarithmic size** (`[P-06:0723–0725]`), with explicit
constants: for a smooth `ψ` supported in `[a₁, a₂] ⊂ (0, ∞)` with `|ψ| ≤ B₀`, `|ψ'| ≤ B₁`,
`|ψ''| ≤ B₂`, there are coefficients `|c_n| ≤ B₀` such that, for all `N ≥ 1` and
`a₁/4 ≤ y ≤ 4a₂`,

`|ψ(y) - ∑_{|n| ≤ N} c_n y^{iκn}| ≤ K (B₁ + B₂) / N`, `κ = cutoffFreq a₁ a₂`,
`K = cutoffConst a₁ a₂`.

(`y^{iκn}` is written `exp(i κ n log y)`.) -/
theorem cutoff_fourier {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha : a₁ ≤ a₂) {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hsupp : Function.support ψ ⊆ Set.Icc a₁ a₂) {B₀ B₁ B₂ : ℝ}
    (h0 : ∀ u, ‖ψ u‖ ≤ B₀) (h1 : ∀ u, ‖deriv ψ u‖ ≤ B₁) (h2 : ∀ u, ‖deriv (deriv ψ) u‖ ≤ B₂) :
    ∃ c : ℤ → ℂ, (∀ n, ‖c n‖ ≤ B₀) ∧
      ∀ N : ℕ, 0 < N → ∀ y : ℝ, a₁ / 4 ≤ y → y ≤ 4 * a₂ →
        ‖ψ y - ∑ n ∈ Finset.Icc (-(N : ℤ)) N, c n *
            Complex.exp (((cutoffFreq a₁ a₂ * n * Real.log y : ℝ) : ℂ) * Complex.I)‖ ≤
          cutoffConst a₁ a₂ * (B₁ + B₂) / N := by
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha
  have h8a₂ : 0 < 8 * a₂ := mul_pos (by norm_num) ha₂
  have ha₁8 : 0 < a₁ / 8 := div_pos ha₁ (by norm_num)
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = cutoffPeriod a₁ a₂ := ⟨_, rfl⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ℝ, u₀ = Real.log (a₁ / 8) := ⟨_, rfl⟩
  have hTpos : 0 < T := by
    rw [hTdef]
    exact cutoffPeriod_pos ha₁ ha
  have hu₁ : u₀ + T = Real.log (8 * a₂) := by
    rw [hu₀, hTdef]
    unfold cutoffPeriod
    ring
  -- regularity
  have hd1 : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv ψ)) := (contDiff_infty_iff_deriv.mp hd1).2
  have hdiff : Differentiable ℝ ψ := (contDiff_infty_iff_deriv.mp hψ).1
  have hdiff1 : Differentiable ℝ (deriv ψ) := (contDiff_infty_iff_deriv.mp hd1).1
  -- vanishing outside the support
  have hts : tsupport ψ ⊆ Set.Icc a₁ a₂ := closure_minimal hsupp isClosed_Icc
  have hψ0 : ∀ y : ℝ, y ∉ Set.Icc a₁ a₂ → ψ y = 0 := fun y hy => by
    by_contra h
    exact hy (hsupp h)
  have hψ1 : ∀ y : ℝ, y ∉ Set.Icc a₁ a₂ → deriv ψ y = 0 := fun y hy =>
    deriv_of_notMem_tsupport fun h => hy (hts h)
  -- the function in the logarithmic variable and its two derivatives
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℂ, φ = fun u => ψ (Real.exp u) := ⟨_, rfl⟩
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : ℝ → ℂ, φ₁ = fun u => Real.exp u • deriv ψ (Real.exp u) := ⟨_, rfl⟩
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : ℝ → ℂ, φ₂ = fun u =>
      Real.exp u • (Real.exp u • deriv (deriv ψ) (Real.exp u)) +
        Real.exp u • deriv ψ (Real.exp u) := ⟨_, rfl⟩
  have hD : ∀ u : ℝ, HasDerivAt φ (φ₁ u) u := by
    intro u
    rw [hφ, hφ₁]
    exact (hdiff (Real.exp u)).hasDerivAt.scomp u (Real.hasDerivAt_exp u)
  have hD1 : ∀ u : ℝ, HasDerivAt φ₁ (φ₂ u) u := by
    intro u
    rw [hφ₁, hφ₂]
    exact (Real.hasDerivAt_exp u).fun_smul
      ((hdiff1 (Real.exp u)).hasDerivAt.scomp u (Real.hasDerivAt_exp u))
  have hcφ : Continuous φ := by
    rw [hφ]
    exact hψ.continuous.comp Real.continuous_exp
  have hcφ₁ : Continuous φ₁ := by
    rw [hφ₁]
    exact Real.continuous_exp.smul (hd1.continuous.comp Real.continuous_exp)
  have hcφ₂ : Continuous φ₂ := by
    rw [hφ₂]
    exact (Real.continuous_exp.smul
      (Real.continuous_exp.smul (hd2.continuous.comp Real.continuous_exp))).add
        (Real.continuous_exp.smul (hd1.continuous.comp Real.continuous_exp))
  -- the endpoints of the period lie outside the support
  have he0 : Real.exp u₀ = a₁ / 8 := by rw [hu₀, Real.exp_log ha₁8]
  have he1 : Real.exp (u₀ + T) = 8 * a₂ := by rw [hu₁, Real.exp_log h8a₂]
  have hout0 : a₁ / 8 ∉ Set.Icc a₁ a₂ := fun h => by linarith [h.1]
  have hout1 : 8 * a₂ ∉ Set.Icc a₁ a₂ := fun h => by linarith [h.2]
  have hφab : φ u₀ = φ (u₀ + T) := by
    rw [hφ]
    show ψ (Real.exp u₀) = ψ (Real.exp (u₀ + T))
    rw [he0, he1, hψ0 _ hout0, hψ0 _ hout1]
  have hφ₁ab : φ₁ u₀ = φ₁ (u₀ + T) := by
    rw [hφ₁]
    show Real.exp u₀ • deriv ψ (Real.exp u₀) =
      Real.exp (u₀ + T) • deriv ψ (Real.exp (u₀ + T))
    rw [he0, he1, hψ1 _ hout0, hψ1 _ hout1, smul_zero, smul_zero]
  -- the bound for the second derivative on the period
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (h1 0)
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (h2 0)
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = (8 * a₂ + 64 * a₂ ^ 2) * (B₁ + B₂) := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂]
    exact mul_nonneg
      (add_nonneg h8a₂.le (mul_nonneg (by norm_num) (sq_nonneg _))) (add_nonneg hB₁0 hB₂0)
  have hφ₂le : ∀ u ∈ Set.Icc u₀ (u₀ + T), ‖φ₂ u‖ ≤ K₂ := by
    intro u hu
    have hexp0 : 0 < Real.exp u := Real.exp_pos u
    have hexp1 : Real.exp u ≤ 8 * a₂ := by
      rw [← he1]
      exact Real.exp_le_exp.mpr hu.2
    have hn1 : ‖Real.exp u • deriv ψ (Real.exp u)‖ ≤ 8 * a₂ * B₁ := by
      rw [norm_smul, Real.norm_of_nonneg hexp0.le]
      exact mul_le_mul hexp1 (h1 _) (norm_nonneg _) h8a₂.le
    have hn2 : ‖Real.exp u • (Real.exp u • deriv (deriv ψ) (Real.exp u))‖ ≤
        8 * a₂ * (8 * a₂ * B₂) := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hexp0.le]
      exact mul_le_mul hexp1 (mul_le_mul hexp1 (h2 _) (norm_nonneg _) h8a₂.le)
        (mul_nonneg hexp0.le (norm_nonneg _)) h8a₂.le
    have e : (8 * a₂ + 64 * a₂ ^ 2) * (B₁ + B₂) =
        8 * a₂ * (8 * a₂ * B₂) + 8 * a₂ * B₁ + (8 * a₂ * B₂ + 64 * a₂ ^ 2 * B₁) := by ring
    have hrest : 0 ≤ 8 * a₂ * B₂ + 64 * a₂ ^ 2 * B₁ :=
      add_nonneg (mul_nonneg h8a₂.le hB₂0)
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hB₁0)
    rw [hφ₂, hK₂]
    show ‖Real.exp u • (Real.exp u • deriv (deriv ψ) (Real.exp u)) +
        Real.exp u • deriv ψ (Real.exp u)‖ ≤ (8 * a₂ + 64 * a₂ ^ 2) * (B₁ + B₂)
    have h3 := (norm_add_le (Real.exp u • (Real.exp u • deriv (deriv ψ) (Real.exp u)))
      (Real.exp u • deriv ψ (Real.exp u))).trans (add_le_add hn2 hn1)
    rw [e]
    linarith
  refine ⟨fun n => fourierCoeffOn (lt_add_of_pos_right u₀ hTpos) φ n, fun n => ?_, ?_⟩
  · refine FourierCutoff.norm_fourierCoeffOn_le _ (fun x _ => ?_) n
    rw [hφ]
    exact h0 _
  · intro N hN y hy1 hy2
    have hy0 : 0 < y := lt_of_lt_of_le (div_pos ha₁ (by norm_num)) hy1
    have hx : Real.log y ∈ Set.Ico u₀ (u₀ + T) := by
      rw [hu₁, hu₀]
      exact ⟨Real.log_le_log ha₁8 (by linarith), Real.log_lt_log hy0 (by linarith)⟩
    have hmain := FourierCutoff.norm_sub_fourier_partial_le hTpos (fun u _ => hD u)
      (fun u _ => hD1 u) hcφ hcφ₁ hcφ₂ hφab hφ₁ab hK₂0 hφ₂le hx hN
    have hφy : φ (Real.log y) = ψ y := by
      rw [hφ]
      show ψ (Real.exp (Real.log y)) = ψ y
      rw [Real.exp_log hy0]
    have hexp : ∀ n : ℤ,
        Complex.exp (2 * Real.pi * Complex.I * n * (Real.log y : ℝ) / T) =
          Complex.exp (((cutoffFreq a₁ a₂ * n * Real.log y : ℝ) : ℂ) * Complex.I) := by
      intro n
      congr 1
      unfold cutoffFreq
      rw [← hTdef]
      push_cast
      ring
    have hsum : ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          fourierCoeffOn (lt_add_of_pos_right u₀ hTpos) φ n *
            Complex.exp (2 * Real.pi * Complex.I * n * (Real.log y : ℝ) / T) =
        ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          fourierCoeffOn (lt_add_of_pos_right u₀ hTpos) φ n *
            Complex.exp (((cutoffFreq a₁ a₂ * n * Real.log y : ℝ) : ℂ) * Complex.I) :=
      Finset.sum_congr rfl fun n _ => by rw [hexp n]
    rw [hφy, hsum] at hmain
    refine hmain.trans (le_of_eq ?_)
    rw [hK₂, hTdef]
    unfold cutoffConst
    ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
