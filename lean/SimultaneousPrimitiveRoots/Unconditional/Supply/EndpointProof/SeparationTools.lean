module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ConstantProductTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.LowMainTermProof

/-!
# Tools for the separation of the extracted parts: energies and shifted polynomials

The separation `[P-06:0717–0737]` writes the endpoint polynomial of an extracted part as a finite
combination of *uncut* polynomials at shifted times plus a tail. This file contains the calculus
of the energies `HighEnergyLe` and the algebra of the endpoint polynomials used for that.

* `HighEnergyLe.mono`, `HighEnergyLe.shift`: monotonicity; a shift `τ ↦ τ + s`, `|s| ≤ S`, moves
  the range `{lo + S ≤ |τ| ≤ hi - S}` into `{lo ≤ |τ| ≤ hi}` ("Retain only shifts of fixed
  log-power size … At the remaining times all retained shifts of `t` are comparable in magnitude
  to `t`").
* `HighEnergyLe.sum_weighted`: Cauchy–Schwarz for a finite combination,
  `∫ |∑ z_i f_i|² ≤ (∑ |z_i|)² · max_i ∫ |f_i|²` ("polynomial-in-`k` total cost", "a fixed
  log-power number of boxes").
* `endpointPolynomial_add`, `endpointPolynomial_finset_sum`,
  `integral_normSq_endpointPolynomial_add_le`: linearity.
* `truncCutoff`, `endpointPolynomial_truncated`: for the truncated Fourier expansion
  `ψ_N(y) = ∑_{|n| ≤ N} c_n y^{iκn}` of the cutoff,
  `Y⁻¹ ∑_w ψ_N(w/Y) w^{iσ} v F(w) e(hw/k) w^{iτ} = ∑_{|n| ≤ N} v c_n Y^{-iκn} Q(τ + σ + κn)` with
  `Q(t) = Y⁻¹ ∑_w F(w) e(hw/k) w^{it}`: the twists are incorporated in the time variable.
* `eventually_log_rpow_le`: `L^b ≤ x` for large `x`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-! ### The calculus of `HighEnergyLe` -/

/-- `HighEnergyLe` is monotone in the three parameters. -/
theorem HighEnergyLe.mono {E : ℝ → ℂ} {lo lo' hi hi' bd bd' : ℝ} (h : HighEnergyLe E lo hi bd)
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) (hbd : bd ≤ bd') : HighEnergyLe E lo' hi' bd' := by
  intro a b hab hr
  refine (h a b hab ?_).trans hbd
  rcases hr with hr | hr
  · exact Or.inl ⟨hlo.trans hr.1, hr.2.trans hhi⟩
  · exact Or.inr ⟨(neg_le_neg hhi).trans hr.1, hr.2.trans (neg_le_neg hlo)⟩

/-- **A shift of the time**: if `|s| ≤ S`, the times `lo + S ≤ |τ| ≤ hi - S` are shifted into
`lo ≤ |τ + s| ≤ hi`, on the same side. -/
theorem HighEnergyLe.shift {E : ℝ → ℂ} {lo hi bd S s : ℝ} (h : HighEnergyLe E lo hi bd)
    (hs : |s| ≤ S) : HighEnergyLe (fun τ => E (τ + s)) (lo + S) (hi - S) bd := by
  intro a b hab hr
  have hs1 : -S ≤ s := (abs_le.mp hs).1
  have hs2 : s ≤ S := (abs_le.mp hs).2
  have e : ∫ τ in a..b, ‖E (τ + s)‖ ^ 2 = ∫ τ in (a + s)..(b + s), ‖E τ‖ ^ 2 :=
    intervalIntegral.integral_comp_add_right (fun τ => ‖E τ‖ ^ 2) s
  rw [e]
  refine h (a + s) (b + s) (by linarith) ?_
  rcases hr with hr | hr
  · exact Or.inl ⟨by linarith [hr.1], by linarith [hr.2]⟩
  · exact Or.inr ⟨by linarith [hr.1], by linarith [hr.2]⟩

/-- Cauchy–Schwarz with weights: `|∑ z_i g_i|² ≤ (∑ |z_i|) ∑ |z_i| |g_i|²`. -/
theorem norm_sq_sum_mul_le {ι : Type*} (s : Finset ι) (z g : ι → ℂ) :
    ‖∑ i ∈ s, z i * g i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) * ∑ i ∈ s, ‖z i‖ * ‖g i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, z i * g i‖ ≤ ∑ i ∈ s, ‖z i‖ * ‖g i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
  have h2 : (∑ i ∈ s, ‖z i‖ * ‖g i‖) ^ 2 ≤ (∑ i ∈ s, ‖z i‖) * ∑ i ∈ s, ‖z i‖ * ‖g i‖ ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => norm_nonneg _)
      (fun i _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- **The energy of a finite combination**: if every `f_i` has energy `≤ bd` on the intervals of
`{lo ≤ |τ| ≤ hi}` and `∑ |z_i| ≤ Z`, then `∑ z_i f_i` has energy `≤ Z² bd` there. -/
theorem HighEnergyLe.sum_weighted {ι : Type*} (s : Finset ι) (z : ι → ℂ) (f : ι → ℝ → ℂ)
    {lo hi bd Z : ℝ} (hc : ∀ i ∈ s, Continuous (f i))
    (hE : ∀ i ∈ s, HighEnergyLe (f i) lo hi bd) (hbd : 0 ≤ bd) (hZ : ∑ i ∈ s, ‖z i‖ ≤ Z) :
    HighEnergyLe (fun t => ∑ i ∈ s, z i * f i t) lo hi (Z ^ 2 * bd) := by
  intro a b hab hr
  have hZ0 : 0 ≤ ∑ i ∈ s, ‖z i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hpt : ∀ t : ℝ, ‖∑ i ∈ s, z i * f i t‖ ^ 2 ≤
      ∑ i ∈ s, (∑ j ∈ s, ‖z j‖) * ‖z i‖ * ‖f i t‖ ^ 2 := by
    intro t
    refine (norm_sq_sum_mul_le s z (fun i => f i t)).trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcl : Continuous fun t : ℝ => ‖∑ i ∈ s, z i * f i t‖ ^ 2 :=
    (continuous_finsetSum s fun i hi => continuous_const.mul (hc i hi)).norm.pow 2
  have hcr : ∀ i ∈ s, Continuous fun t : ℝ => (∑ j ∈ s, ‖z j‖) * ‖z i‖ * ‖f i t‖ ^ 2 :=
    fun i hi => continuous_const.mul ((hc i hi).norm.pow 2)
  have hcsum : Continuous fun t : ℝ => ∑ i ∈ s, (∑ j ∈ s, ‖z j‖) * ‖z i‖ * ‖f i t‖ ^ 2 :=
    continuous_finsetSum s hcr
  calc ∫ t in a..b, ‖∑ i ∈ s, z i * f i t‖ ^ 2
      ≤ ∫ t in a..b, ∑ i ∈ s, (∑ j ∈ s, ‖z j‖) * ‖z i‖ * ‖f i t‖ ^ 2 :=
        intervalIntegral.integral_mono_on hab (hcl.intervalIntegrable _ _)
          (hcsum.intervalIntegrable _ _) fun t _ => hpt t
    _ = ∑ i ∈ s, ∫ t in a..b, (∑ j ∈ s, ‖z j‖) * ‖z i‖ * ‖f i t‖ ^ 2 :=
        intervalIntegral.integral_finsetSum fun i hi => (hcr i hi).intervalIntegrable _ _
    _ = ∑ i ∈ s, (∑ j ∈ s, ‖z j‖) * ‖z i‖ * ∫ t in a..b, ‖f i t‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
    _ ≤ ∑ i ∈ s, (∑ j ∈ s, ‖z j‖) * ‖z i‖ * bd :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (hE i hi a b hab hr) (mul_nonneg hZ0 (norm_nonneg _))
    _ = (∑ j ∈ s, ‖z j‖) ^ 2 * bd := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
    _ ≤ Z ^ 2 * bd := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hZ0 hZ 2) hbd

/-! ### Linearity of the endpoint polynomial -/

/-- The endpoint polynomial of a sequence supported on `1 ≤ w ≤ W` is continuous. -/
theorem continuous_endpointPolynomial_Icc {U : ℕ → ℂ} {W : ℕ}
    (hU : ∀ w, U w ≠ 0 → w ∈ Finset.Icc 1 W) (Y : ℝ) (h : ℤ) (k : ℕ) :
    Continuous fun τ : ℝ => endpointPolynomial U Y h k τ := by
  have h0 : U 0 = 0 := by
    by_contra h'
    have h1 := (Finset.mem_Icc.mp (hU 0 h')).1
    omega
  exact continuous_endpointPolynomial hU h0 Y h k

/-- The support of a sum of two sequences. -/
theorem mem_of_add_ne_zero {U₁ U₂ : ℕ → ℂ} {s : Finset ℕ} (h₁ : ∀ w, U₁ w ≠ 0 → w ∈ s)
    (h₂ : ∀ w, U₂ w ≠ 0 → w ∈ s) (w : ℕ) (hw : U₁ w + U₂ w ≠ 0) : w ∈ s := by
  by_cases h1 : U₁ w = 0
  · refine h₂ w fun h2 => hw ?_
    rw [h1, h2, add_zero]
  · exact h₁ w h1

theorem endpointPolynomial_add {U₁ U₂ : ℕ → ℂ} {s : Finset ℕ} (h₁ : ∀ w, U₁ w ≠ 0 → w ∈ s)
    (h₂ : ∀ w, U₂ w ≠ 0 → w ∈ s) (Y : ℝ) (h : ℤ) (k : ℕ) (τ : ℝ) :
    endpointPolynomial (fun w => U₁ w + U₂ w) Y h k τ =
      endpointPolynomial U₁ Y h k τ + endpointPolynomial U₂ Y h k τ := by
  have h₁₂ : ∀ w, (fun w => U₁ w + U₂ w) w ≠ 0 → w ∈ s := mem_of_add_ne_zero h₁ h₂
  rw [endpointPolynomial_eq_sum h₁₂, endpointPolynomial_eq_sum h₁, endpointPolynomial_eq_sum h₂,
    ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  show (U₁ w + U₂ w) * _ * _ = _
  ring

theorem endpointPolynomial_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℂ) {W : ℕ}
    (hF : ∀ i ∈ s, ∀ w, F i w ≠ 0 → w ∈ Finset.Icc 1 W) (Y : ℝ) (h : ℤ) (k : ℕ) (t : ℝ) :
    endpointPolynomial (fun w => ∑ i ∈ s, F i w) Y h k t =
      ∑ i ∈ s, endpointPolynomial (F i) Y h k t := by
  have hsum : ∀ w, (fun w => ∑ i ∈ s, F i w) w ≠ 0 → w ∈ Finset.Icc 1 W := by
    intro w hw
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    exact hF i hi w hne
  have hR : ∑ i ∈ s, endpointPolynomial (F i) Y h k t =
      ∑ i ∈ s, (Y : ℂ)⁻¹ * ∑ w ∈ Finset.Icc 1 W,
        F i w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) * (w : ℂ) ^ ((t : ℂ) * Complex.I) :=
    Finset.sum_congr rfl fun i hi => endpointPolynomial_eq_sum (hF i hi) Y h k t
  rw [endpointPolynomial_eq_sum hsum Y h k t, hR, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  show (∑ i ∈ s, F i w) * _ * _ = _
  rw [Finset.sum_mul, Finset.sum_mul]

/-- `∫ |E_{U₁ + U₂}|² ≤ 2 ∫ |E_{U₁}|² + 2 ∫ |E_{U₂}|²`. -/
theorem integral_normSq_endpointPolynomial_add_le {U₁ U₂ : ℕ → ℂ} {W : ℕ}
    (h₁ : ∀ w, U₁ w ≠ 0 → w ∈ Finset.Icc 1 W) (h₂ : ∀ w, U₂ w ≠ 0 → w ∈ Finset.Icc 1 W)
    (Y : ℝ) (h : ℤ) (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∫ τ in a..b, ‖endpointPolynomial (fun w => U₁ w + U₂ w) Y h k τ‖ ^ 2 ≤
      2 * (∫ τ in a..b, ‖endpointPolynomial U₁ Y h k τ‖ ^ 2) +
        2 * ∫ τ in a..b, ‖endpointPolynomial U₂ Y h k τ‖ ^ 2 := by
  have h₁₂ : ∀ w, (fun w => U₁ w + U₂ w) w ≠ 0 → w ∈ Finset.Icc 1 W :=
    mem_of_add_ne_zero h₁ h₂
  have hc₁ := continuous_normSq_endpointPolynomial h₁ Y h k
  have hc₂ := continuous_normSq_endpointPolynomial h₂ Y h k
  have hc₁₂ := continuous_normSq_endpointPolynomial h₁₂ Y h k
  have hpt : ∀ τ : ℝ, ‖endpointPolynomial (fun w => U₁ w + U₂ w) Y h k τ‖ ^ 2 ≤
      2 * ‖endpointPolynomial U₁ Y h k τ‖ ^ 2 + 2 * ‖endpointPolynomial U₂ Y h k τ‖ ^ 2 := by
    intro τ
    rw [endpointPolynomial_add h₁ h₂]
    exact normSq_add_le_two_mul _ _
  have hi₁ : IntervalIntegrable (fun τ => 2 * ‖endpointPolynomial U₁ Y h k τ‖ ^ 2)
      MeasureTheory.volume a b := (continuous_const.mul hc₁).intervalIntegrable a b
  have hi₂ : IntervalIntegrable (fun τ => 2 * ‖endpointPolynomial U₂ Y h k τ‖ ^ 2)
      MeasureTheory.volume a b := (continuous_const.mul hc₂).intervalIntegrable a b
  have e₁ : ∫ τ in a..b, (2 * ‖endpointPolynomial U₁ Y h k τ‖ ^ 2 +
        2 * ‖endpointPolynomial U₂ Y h k τ‖ ^ 2) =
      (∫ τ in a..b, 2 * ‖endpointPolynomial U₁ Y h k τ‖ ^ 2) +
        ∫ τ in a..b, 2 * ‖endpointPolynomial U₂ Y h k τ‖ ^ 2 :=
    intervalIntegral.integral_add hi₁ hi₂
  have e₂ : ∫ τ in a..b, 2 * ‖endpointPolynomial U₁ Y h k τ‖ ^ 2 =
      2 * ∫ τ in a..b, ‖endpointPolynomial U₁ Y h k τ‖ ^ 2 :=
    intervalIntegral.integral_const_mul 2 _
  have e₃ : ∫ τ in a..b, 2 * ‖endpointPolynomial U₂ Y h k τ‖ ^ 2 =
      2 * ∫ τ in a..b, ‖endpointPolynomial U₂ Y h k τ‖ ^ 2 :=
    intervalIntegral.integral_const_mul 2 _
  have hmono : ∫ τ in a..b, ‖endpointPolynomial (fun w => U₁ w + U₂ w) Y h k τ‖ ^ 2 ≤
      ∫ τ in a..b, (2 * ‖endpointPolynomial U₁ Y h k τ‖ ^ 2 +
        2 * ‖endpointPolynomial U₂ Y h k τ‖ ^ 2) :=
    intervalIntegral.integral_mono_on hab (hc₁₂.intervalIntegrable a b) (hi₁.add hi₂)
      (fun τ _ => hpt τ)
  rw [e₁, e₂, e₃] at hmono
  exact hmono

/-! ### The truncated expansion of the cutoff and the shifted polynomials -/

/-- The truncated Fourier expansion `∑_{|n| ≤ N} c_n y^{iκn}` of a cutoff
(`y^{iκn} = exp(iκn log y)`). -/
def truncCutoff (c : ℤ → ℂ) (κ : ℝ) (N : ℕ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    c n * Complex.exp (((κ * n * Real.log y : ℝ) : ℂ) * Complex.I)

/-- `(w/Y)^{iκn} w^{iσ} w^{iτ} = Y^{-iκn} w^{i(τ + σ + κn)}`: a twist of the cutoff is a shift of
the time. -/
theorem twist_term {w : ℕ} (hw : w ≠ 0) {Y : ℝ} (hY : 0 < Y) (σ κ τ : ℝ) (n : ℤ) :
    Complex.exp (((κ * n * Real.log ((w : ℝ) / Y) : ℝ) : ℂ) * Complex.I) *
        (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (w : ℂ) ^ ((τ : ℂ) * Complex.I) =
      Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I) *
        (w : ℂ) ^ (((τ + (σ + κ * n) : ℝ) : ℂ) * Complex.I) := by
  have hw0 : (0 : ℝ) < (w : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hw)
  rw [natCast_cpow_mul_I hw, natCast_cpow_mul_I hw, natCast_cpow_mul_I hw,
    Real.log_div hw0.ne' hY.ne', ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The truncated part is a combination of shifted uncut polynomials**: with
`Q(t) = Y⁻¹ ∑_w F(w) e(hw/k) w^{it}`,

`Y⁻¹ ∑_w ψ_N(w/Y) w^{iσ} v F(w) e(hw/k) w^{iτ} = ∑_{|n| ≤ N} v c_n Y^{-iκn} Q(τ + (σ + κn))`. -/
theorem endpointPolynomial_truncated {F : ℕ → ℂ} {W : ℕ}
    (hF : ∀ w, F w ≠ 0 → w ∈ Finset.Icc 1 W) {Y : ℝ} (hY : 0 < Y) (h : ℤ) (k : ℕ) (σ κ : ℝ)
    (v : ℂ) (c : ℤ → ℂ) (N : ℕ) (τ : ℝ) :
    endpointPolynomial (fun w : ℕ => truncCutoff c κ N ((w : ℝ) / Y) *
        (w : ℂ) ^ ((σ : ℂ) * Complex.I) * v * F w) Y h k τ =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        (v * c n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I)) *
          endpointPolynomial F Y h k (τ + (σ + κ * n)) := by
  have hsupp : ∀ w : ℕ, (fun w : ℕ => truncCutoff c κ N ((w : ℝ) / Y) *
      (w : ℂ) ^ ((σ : ℂ) * Complex.I) * v * F w) w ≠ 0 → w ∈ Finset.Icc 1 W := by
    intro w hw
    refine hF w fun h0 => hw ?_
    show truncCutoff c κ N ((w : ℝ) / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * v * F w = 0
    rw [h0, mul_zero]
  have hterm : ∀ w ∈ Finset.Icc 1 W,
      truncCutoff c κ N ((w : ℝ) / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * v * F w *
          addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) * (w : ℂ) ^ ((τ : ℂ) * Complex.I) =
        ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          (v * c n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I)) *
            (F w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
              (w : ℂ) ^ (((τ + (σ + κ * n) : ℝ) : ℂ) * Complex.I)) := by
    intro w hw
    have hw0 : w ≠ 0 := by
      have h1 := (Finset.mem_Icc.mp hw).1
      omega
    unfold truncCutoff
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    have ht := twist_term hw0 hY σ κ τ n
    calc c n * Complex.exp (((κ * n * Real.log ((w : ℝ) / Y) : ℝ) : ℂ) * Complex.I) *
            (w : ℂ) ^ ((σ : ℂ) * Complex.I) * v * F w *
            addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) * (w : ℂ) ^ ((τ : ℂ) * Complex.I)
        = v * c n * F w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
            (Complex.exp (((κ * n * Real.log ((w : ℝ) / Y) : ℝ) : ℂ) * Complex.I) *
              (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (w : ℂ) ^ ((τ : ℂ) * Complex.I)) := by ring
      _ = v * c n * F w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
            (Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I) *
              (w : ℂ) ^ (((τ + (σ + κ * n) : ℝ) : ℂ) * Complex.I)) := by rw [ht]
      _ = (v * c n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I)) *
            (F w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
              (w : ℂ) ^ (((τ + (σ + κ * n) : ℝ) : ℂ) * Complex.I)) := by ring
  have hR : ∀ n ∈ Finset.Icc (-(N : ℤ)) N,
      (v * c n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I)) *
          endpointPolynomial F Y h k (τ + (σ + κ * n)) =
        (Y : ℂ)⁻¹ * ∑ w ∈ Finset.Icc 1 W,
          (v * c n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I)) *
            (F w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
              (w : ℂ) ^ (((τ + (σ + κ * n) : ℝ) : ℂ) * Complex.I)) := by
    intro n _
    rw [endpointPolynomial_eq_sum hF Y h k (τ + (σ + κ * n)), ← Finset.mul_sum]
    ring
  rw [endpointPolynomial_eq_sum hsupp Y h k τ, Finset.sum_congr rfl hR, ← Finset.mul_sum,
    Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl hterm

/-! ### A power of `L` is at most `x` -/

/-- `L^b ≤ x` for large `x`. -/
theorem eventually_log_rpow_le (b : ℝ) : ∀ᶠ x : ℝ in atTop, Real.log x ^ b ≤ x := by
  filter_upwards [eventually_rpow_mul_exp_neg_le_one b, eventually_ge_atTop (Real.exp 1)]
    with x hx hxe
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hL1 : 1 ≤ Real.log x := by
    have h1 := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h1
  have h1 := mul_le_mul_of_nonneg_right hx (Real.exp_pos (Real.log x ^ (0.27 : ℝ))).le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at h1
  have h3 : Real.log x ^ (0.27 : ℝ) ≤ Real.log x := by
    have h4 := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (0.27 : ℝ) ≤ 1)
    rw [Real.rpow_one] at h4
    exact h4
  calc Real.log x ^ b ≤ Real.exp (Real.log x ^ (0.27 : ℝ)) := h1
    _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr h3
    _ = x := Real.exp_log hx0

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
