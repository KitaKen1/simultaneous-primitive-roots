module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SmoothSum
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# (cor:low-main-term)

`lowMainTerm : SmoothProgressionSum → LowMainTerm` (`[P-06:0652–0667]`): for `(m, k) = 1`,

`∑_{v ≥ 1} ψ_1(m v / Y) (m v)^{iu} e(h m v / k)
  = (Y/m) ((1/k) ∑_{a mod k} e(ha/k)) ∫ ψ_1(z) (Yz)^{iu} dz + O(L^C)`, `u = τ + σ`,

uniformly in `m` and in `Y > 0`.

* The phase `(Yz)^{iu}` is `mellinPhase Y u z = exp(i u log(Yz))` for `z > 0`; the integrand
  `G(z) = ψ_1(z) exp(i u log(Yz))` is `C¹` on `ℝ` (it vanishes for `z < a₁`), and for `z > 0`
  `|G'(z)| ≤ |ψ_1'(z)| + |u| |ψ_1(z)| / z` (`norm_deriv_cutoff_mul_le`), so
  `∫ |G'| ≤ (a₂ - a₁/2) (sup|ψ_1'| + (2|u|/a₁) sup|ψ_1|)` (`integral_norm_deriv_cutoff_mul_le`).
* `F(y) = G(m y / Y)`: `∫ F = (Y/m) ∫ G` and `∫ |F'| = ∫ |G'|`, independent of `m` and `Y`.
* The sum over `v` is split into the residue classes `b` modulo `k`; on each class
  `e(h m v / k) = e(h m b / k)` (`addChar_mod`), and `SmoothProgressionSum` gives
  `|∑_{v ≡ b (k)} F(v) - (1/k) ∫ F| ≤ ∫ |F'|`. Summing the `k` classes
  (`norm_sub_main_le`): the error is `≤ k ∫ |F'|`.
* `∑_{b < k} e(h m b / k) = ∑_{a < k} e(h a / k)` because `b ↦ m b mod k` permutes the residues
  (`sum_addChar_mul_coprime`).

With `P = |D₁| + |D₀| + |B'| + |Cσ|`: `C = C₆ + P`, `M = (1 + 4/a₁)(a₂ - a₁/2)`, for `x ≥ e`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open scoped ContDiff

noncomputable section

/-! ### Additive characters -/

/-- `e(θ + n) = e(θ)` for an integer `n`. -/
theorem addChar_add_intCast (θ : ℝ) (n : ℤ) : addChar (θ + (n : ℝ)) = addChar θ := by
  unfold addChar
  have h : 2 * (Real.pi : ℂ) * ((θ + (n : ℝ) : ℝ) : ℂ) * Complex.I =
      2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [Complex.ofReal_add, Complex.ofReal_intCast]
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `e(h (r + k q) / k) = e(h r / k)`. -/
theorem addChar_add_mul (h : ℤ) {k : ℕ} (hk : 0 < k) (r q : ℕ) :
    addChar ((h : ℝ) * ((r + k * q : ℕ) : ℝ) / (k : ℝ)) =
      addChar ((h : ℝ) * (r : ℝ) / (k : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have e : (h : ℝ) * ((r + k * q : ℕ) : ℝ) / (k : ℝ) =
      (h : ℝ) * (r : ℝ) / (k : ℝ) + ((h * (q : ℤ) : ℤ) : ℝ) := by
    rw [div_add' _ _ _ hk0]
    congr 1
    push_cast
    ring
  rw [e, addChar_add_intCast]

/-- `e(h n / k) = e(h (n mod k) / k)`. -/
theorem addChar_mod (h : ℤ) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    addChar ((h : ℝ) * (n : ℝ) / (k : ℝ)) =
      addChar ((h : ℝ) * ((n % k : ℕ) : ℝ) / (k : ℝ)) := by
  have h1 := addChar_add_mul h hk (n % k) (n / k)
  rw [Nat.mod_add_div] at h1
  exact h1

/-- For `(m, k) = 1`, `∑_{b < k} e(h m b / k) = ∑_{a < k} e(h a / k)`: multiplication by `m`
permutes the residues modulo `k`. -/
theorem sum_addChar_mul_coprime (h : ℤ) {m k : ℕ} (hk : 0 < k) (hmk : m.Coprime k) :
    ∑ b ∈ Finset.range k, addChar ((h : ℝ) * ((m * b : ℕ) : ℝ) / (k : ℝ)) =
      ∑ a ∈ Finset.range k, addChar ((h : ℝ) * (a : ℝ) / (k : ℝ)) := by
  have hinj : Set.InjOn (fun b : ℕ => m * b % k) (Finset.range k : Set ℕ) := by
    intro b hb b' hb' hbb'
    have hb1 : b < k := Finset.mem_range.mp (Finset.mem_coe.mp hb)
    have hb2 : b' < k := Finset.mem_range.mp (Finset.mem_coe.mp hb')
    have h1 : m * b ≡ m * b' [MOD k] := hbb'
    exact (Nat.ModEq.cancel_left_of_coprime hmk.symm h1).eq_of_lt_of_lt hb1 hb2
  have himg : (Finset.range k).image (fun b : ℕ => m * b % k) = Finset.range k := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro a ha
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_range.mpr (Nat.mod_lt _ hk)
    · exact le_of_eq (Finset.card_image_of_injOn hinj).symm
  calc ∑ b ∈ Finset.range k, addChar ((h : ℝ) * ((m * b : ℕ) : ℝ) / (k : ℝ))
      = ∑ b ∈ Finset.range k, addChar ((h : ℝ) * ((m * b % k : ℕ) : ℝ) / (k : ℝ)) :=
        Finset.sum_congr rfl fun b _ => addChar_mod h hk (m * b)
    _ = ∑ a ∈ (Finset.range k).image (fun b : ℕ => m * b % k),
          addChar ((h : ℝ) * (a : ℝ) / (k : ℝ)) :=
        (Finset.sum_image (f := fun a : ℕ => addChar ((h : ℝ) * (a : ℝ) / (k : ℝ))) hinj).symm
    _ = ∑ a ∈ Finset.range k, addChar ((h : ℝ) * (a : ℝ) / (k : ℝ)) := by rw [himg]

/-- The algebra of the residue classes: if `S = ∑_{b < k} χ_b S_b`, `|χ_b| = 1`,
`|S_b - J/k| ≤ E` and `∑_b χ_b = T`, then `|S - (1/k) T J| ≤ k E`. -/
theorem norm_sub_main_le {k : ℕ} {χ Sb : ℕ → ℂ} {S J T : ℂ} {E : ℝ}
    (hS : S = ∑ b ∈ Finset.range k, χ b * Sb b) (hχ : ∀ b, ‖χ b‖ = 1)
    (hSb : ∀ b, ‖Sb b - (k : ℂ)⁻¹ * J‖ ≤ E) (hT : ∑ b ∈ Finset.range k, χ b = T) :
    ‖S - (k : ℂ)⁻¹ * T * J‖ ≤ (k : ℝ) * E := by
  have hR : ∑ b ∈ Finset.range k, χ b * (Sb b - (k : ℂ)⁻¹ * J) =
      (∑ b ∈ Finset.range k, χ b * Sb b) -
        (∑ b ∈ Finset.range k, χ b) * ((k : ℂ)⁻¹ * J) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => mul_sub _ _ _
  have hdecomp : S - (k : ℂ)⁻¹ * T * J =
      ∑ b ∈ Finset.range k, χ b * (Sb b - (k : ℂ)⁻¹ * J) := by
    rw [hR, hT, hS]
    ring
  rw [hdecomp]
  calc ‖∑ b ∈ Finset.range k, χ b * (Sb b - (k : ℂ)⁻¹ * J)‖
      ≤ ∑ b ∈ Finset.range k, ‖χ b * (Sb b - (k : ℂ)⁻¹ * J)‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ Finset.range k, E := Finset.sum_le_sum fun b _ => by
        rw [norm_mul, hχ b, one_mul]
        exact hSb b
    _ = (k : ℝ) * E := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The phase -/

/-- The phase `exp(i u log(Yz))`; it is `(Yz)^{iu}` for `Yz > 0` (`cpow_eq_mellinPhase`). -/
def mellinPhase (Y u z : ℝ) : ℂ :=
  Complex.exp (((u * Real.log (Y * z) : ℝ) : ℂ) * Complex.I)

theorem norm_mellinPhase (Y u z : ℝ) : ‖mellinPhase Y u z‖ = 1 := by
  unfold mellinPhase
  exact Complex.norm_exp_ofReal_mul_I _

theorem cpow_eq_mellinPhase {Y z : ℝ} (h : 0 < Y * z) (u : ℝ) :
    ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I) = mellinPhase Y u z := by
  have hne : ((Y * z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.ne'
  unfold mellinPhase
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log h.le]
  congr 1
  rw [Complex.ofReal_mul]
  ring

/-- `d/dz exp(i u log(Yz)) = exp(i u log(Yz)) · i u / z` for `z ≠ 0`. -/
theorem hasDerivAt_mellinPhase {Y z : ℝ} (hY : Y ≠ 0) (hz : z ≠ 0) (u : ℝ) :
    HasDerivAt (mellinPhase Y u)
      (mellinPhase Y u z * (((u * z⁻¹ : ℝ) : ℂ) * Complex.I)) z := by
  have hYz : Y * z ≠ 0 := mul_ne_zero hY hz
  have h1 : HasDerivAt (fun y : ℝ => Y * y) (Y * 1) z := (hasDerivAt_id' z).const_mul Y
  have h2 : HasDerivAt (fun y : ℝ => Real.log (Y * y)) (Y * 1 / (Y * z)) z := h1.log hYz
  have h3 : HasDerivAt (fun y : ℝ => u * Real.log (Y * y)) (u * (Y * 1 / (Y * z))) z :=
    h2.const_mul u
  have e : u * (Y * 1 / (Y * z)) = u * z⁻¹ := by
    rw [mul_one, div_eq_mul_inv, mul_inv, ← mul_assoc Y, mul_inv_cancel₀ hY, one_mul]
  rw [e] at h3
  have h4 : HasDerivAt (fun y : ℝ => ((u * Real.log (Y * y) : ℝ) : ℂ))
      ((u * z⁻¹ : ℝ) : ℂ) z := h3.ofReal_comp
  have h5 : HasDerivAt (fun y : ℝ => ((u * Real.log (Y * y) : ℝ) : ℂ) * Complex.I)
      (((u * z⁻¹ : ℝ) : ℂ) * Complex.I) z := h4.mul_const Complex.I
  exact h5.cexp

theorem contDiffAt_mellinPhase {Y z : ℝ} (hY : Y ≠ 0) (hz : z ≠ 0) (u : ℝ) :
    ContDiffAt ℝ 1 (mellinPhase Y u) z := by
  have hYz : Y * z ≠ 0 := mul_ne_zero hY hz
  have h1 : ContDiffAt ℝ 1 (fun y : ℝ => Y * y) z := contDiffAt_const.mul contDiffAt_id
  have h2 : ContDiffAt ℝ 1 (fun y : ℝ => Real.log (Y * y)) z := h1.log hYz
  have h3 : ContDiffAt ℝ 1 (fun y : ℝ => u * Real.log (Y * y)) z := contDiffAt_const.mul h2
  have h4' : ContDiffAt ℝ 1 (fun y : ℝ => Complex.ofRealCLM (u * Real.log (Y * y))) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z h3
  have h4 : ContDiffAt ℝ 1 (fun y : ℝ => ((u * Real.log (Y * y) : ℝ) : ℂ)) z := by
    simpa only [Complex.ofRealCLM_apply] using h4'
  have h5 : ContDiffAt ℝ 1 (fun y : ℝ => ((u * Real.log (Y * y) : ℝ) : ℂ) * Complex.I) z :=
    h4.mul contDiffAt_const
  exact h5.cexp

/-! ### The integrand `ψ₁(z) exp(i u log(Yz))` -/

section Integrand

variable {ψ₁ : ℝ → ℂ} {a₁ a₂ Y : ℝ}

theorem eq_zero_of_notMem_Icc (hsupp : Function.support ψ₁ ⊆ Set.Icc a₁ a₂) {z : ℝ}
    (hz : z ∉ Set.Icc a₁ a₂) : ψ₁ z = 0 := by
  by_contra h
  exact hz (hsupp (Function.mem_support.mpr h))

/-- `ψ₁(z) (Yz)^{iu} = ψ₁(z) exp(i u log(Yz))` for every real `z`: both sides vanish for
`z ≤ 0`. -/
theorem cutoff_mul_cpow_eq (hsupp : Function.support ψ₁ ⊆ Set.Icc a₁ a₂) (ha₁ : 0 < a₁)
    (hY : 0 < Y) (u z : ℝ) :
    ψ₁ z * ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I) = ψ₁ z * mellinPhase Y u z := by
  by_cases hz : 0 < z
  · rw [cpow_eq_mellinPhase (mul_pos hY hz)]
  · have h0 : ψ₁ z = 0 :=
      eq_zero_of_notMem_Icc hsupp fun h => hz (lt_of_lt_of_le ha₁ h.1)
    rw [h0, zero_mul, zero_mul]

theorem support_cutoff_mul_subset (hsupp : Function.support ψ₁ ⊆ Set.Icc a₁ a₂) (u : ℝ) :
    Function.support (fun z => ψ₁ z * mellinPhase Y u z) ⊆ Set.Icc a₁ a₂ := by
  intro z hz
  have hz' : ψ₁ z * mellinPhase Y u z ≠ 0 := Function.mem_support.mp hz
  by_contra hmem
  exact hz' (by rw [eq_zero_of_notMem_Icc hsupp hmem, zero_mul])

/-- The integrand is `C¹` on `ℝ`: it vanishes near `0`, and the phase is smooth away from `0`. -/
theorem contDiff_cutoff_mul (hψ : ContDiff ℝ 1 ψ₁) (hsupp : Function.support ψ₁ ⊆ Set.Icc a₁ a₂)
    (ha₁ : 0 < a₁) (hY : Y ≠ 0) (u : ℝ) :
    ContDiff ℝ 1 (fun z => ψ₁ z * mellinPhase Y u z) := by
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  by_cases hz : z = 0
  · have hmem : Set.Iio a₁ ∈ nhds z := Iio_mem_nhds (by rw [hz]; exact ha₁)
    have hev : (fun z => ψ₁ z * mellinPhase Y u z) =ᶠ[nhds z] fun _ => (0 : ℂ) := by
      filter_upwards [hmem] with y hy
      have hy0 : ψ₁ y = 0 :=
        eq_zero_of_notMem_Icc hsupp fun h => absurd h.1 (not_le.mpr (Set.mem_Iio.mp hy))
      rw [hy0, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact hψ.contDiffAt.mul (contDiffAt_mellinPhase hY hz u)

/-- `|G'(z)| ≤ |ψ₁'(z)| + |ψ₁(z)| |u| / z` for `z > 0`. -/
theorem norm_deriv_cutoff_mul_le (hψ : Differentiable ℝ ψ₁) (hY : Y ≠ 0) (u : ℝ) {z : ℝ}
    (hz : 0 < z) :
    ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖ ≤
      ‖deriv ψ₁ z‖ + ‖ψ₁ z‖ * (|u| * z⁻¹) := by
  have hd : HasDerivAt (fun y => ψ₁ y * mellinPhase Y u y)
      (deriv ψ₁ z * mellinPhase Y u z +
        ψ₁ z * (mellinPhase Y u z * (((u * z⁻¹ : ℝ) : ℂ) * Complex.I))) z :=
    (hψ z).hasDerivAt.fun_mul (hasDerivAt_mellinPhase hY hz.ne' u)
  have hP : ‖mellinPhase Y u z‖ = 1 := norm_mellinPhase Y u z
  have hI : ‖((u * z⁻¹ : ℝ) : ℂ) * Complex.I‖ = |u| * z⁻¹ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (inv_pos.mpr hz)]
  have h1 : ‖deriv ψ₁ z * mellinPhase Y u z‖ = ‖deriv ψ₁ z‖ := by
    rw [norm_mul, hP, mul_one]
  have h2 : ‖ψ₁ z * (mellinPhase Y u z * (((u * z⁻¹ : ℝ) : ℂ) * Complex.I))‖ =
      ‖ψ₁ z‖ * (|u| * z⁻¹) := by
    rw [norm_mul, norm_mul, hP, one_mul, hI]
  rw [hd.deriv]
  calc ‖deriv ψ₁ z * mellinPhase Y u z +
        ψ₁ z * (mellinPhase Y u z * (((u * z⁻¹ : ℝ) : ℂ) * Complex.I))‖
      ≤ ‖deriv ψ₁ z * mellinPhase Y u z‖ +
        ‖ψ₁ z * (mellinPhase Y u z * (((u * z⁻¹ : ℝ) : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ = ‖deriv ψ₁ z‖ + ‖ψ₁ z‖ * (|u| * z⁻¹) := by rw [h1, h2]

/-- `∫ |G'| ≤ (sup|ψ₁'| + (2|u|/a₁) sup|ψ₁|) (a₂ - a₁/2)`. -/
theorem integral_norm_deriv_cutoff_mul_le (hψ : Differentiable ℝ ψ₁)
    (hsupp : Function.support ψ₁ ⊆ Set.Icc a₁ a₂) (ha₁ : 0 < a₁) (ha₁₂ : a₁ ≤ a₂) (hY : Y ≠ 0)
    (u : ℝ) {A₀ A₁ : ℝ} (hb0 : ∀ z : ℝ, ‖ψ₁ z‖ ≤ A₀) (hb1 : ∀ z : ℝ, ‖deriv ψ₁ z‖ ≤ A₁) :
    ∫ z : ℝ, ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖ ≤
      (A₁ + A₀ * (|u| * (2 / a₁))) * (a₂ - a₁ / 2) := by
  have hA₀ : 0 ≤ A₀ := (norm_nonneg (ψ₁ 0)).trans (hb0 0)
  have hle : a₁ / 2 ≤ a₂ := by linarith
  have hlen : 0 ≤ a₂ - a₁ / 2 := by linarith
  have hhalf : 0 < a₁ / 2 := by linarith
  have htsupp : tsupport (fun z => ψ₁ z * mellinPhase Y u z) ⊆ Set.Icc a₁ a₂ :=
    closure_minimal (support_cutoff_mul_subset hsupp u) isClosed_Icc
  have hsuppD : Function.support
      (fun z => ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖) ⊆ Set.Ioc (a₁ / 2) a₂ := by
    intro z hz
    have hz1 : ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖ ≠ 0 := Function.mem_support.mp hz
    have hz2 : z ∈ Function.support (deriv fun z => ψ₁ z * mellinPhase Y u z) :=
      Function.mem_support.mpr (norm_ne_zero_iff.mp hz1)
    have hmem : z ∈ Set.Icc a₁ a₂ := htsupp (support_deriv_subset hz2)
    exact ⟨by linarith [hmem.1], hmem.2⟩
  have hint : ∫ z in (a₁ / 2)..a₂, ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖ =
      ∫ z : ℝ, ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖ :=
    intervalIntegral.integral_eq_integral_of_support_subset hsuppD
  have hbound : ∀ z ∈ Set.uIoc (a₁ / 2) a₂,
      ‖‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖‖ ≤ A₁ + A₀ * (|u| * (2 / a₁)) := by
    intro z hz
    rw [Set.uIoc_of_le hle] at hz
    have hzpos : 0 < z := lt_trans hhalf hz.1
    have hzinv : z⁻¹ ≤ 2 / a₁ := by
      have h3 : z⁻¹ ≤ (a₁ / 2)⁻¹ := inv_anti₀ hhalf hz.1.le
      rw [inv_div] at h3
      exact h3
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖
        ≤ ‖deriv ψ₁ z‖ + ‖ψ₁ z‖ * (|u| * z⁻¹) := norm_deriv_cutoff_mul_le hψ hY u hzpos
      _ ≤ A₁ + A₀ * (|u| * (2 / a₁)) :=
          add_le_add (hb1 z) (mul_le_mul (hb0 z)
            (mul_le_mul_of_nonneg_left hzinv (abs_nonneg u))
            (mul_nonneg (abs_nonneg u) (inv_nonneg.mpr hzpos.le)) hA₀)
  have h3 : ‖∫ z in (a₁ / 2)..a₂, ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖‖ ≤
      (A₁ + A₀ * (|u| * (2 / a₁))) * |a₂ - a₁ / 2| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg hlen] at h3
  rw [← hint]
  exact (Real.le_norm_self _).trans h3

end Integrand

/-! ### The final bound -/

/-- The error `k ∫|F'|` is at most a fixed power of `L`. -/
theorem low_error_bound {L a₁ a₂ D₀ D₁ Cσ C₆ B' : ℝ} (hL : 1 ≤ L) (ha₁ : 0 < a₁)
    (ha₁₂ : a₁ ≤ a₂) {kR σ τ : ℝ} (hk : kR ≤ L ^ C₆) (hσ : |σ| ≤ L ^ Cσ)
    (hτ : |τ| ≤ L ^ B') :
    kR * ((L ^ D₁ + L ^ D₀ * (|τ + σ| * (2 / a₁))) * (a₂ - a₁ / 2)) ≤
      (1 + 4 / a₁) * (a₂ - a₁ / 2) * L ^ (C₆ + (|D₁| + |D₀| + |B'| + |Cσ|)) := by
  have hL0 : 0 < L := by linarith
  have hD1 : D₁ ≤ |D₁| + |D₀| + |B'| + |Cσ| := by
    linarith [le_abs_self D₁, abs_nonneg D₀, abs_nonneg B', abs_nonneg Cσ]
  have hD2 : D₀ + B' ≤ |D₁| + |D₀| + |B'| + |Cσ| := by
    linarith [abs_nonneg D₁, le_abs_self D₀, le_abs_self B', abs_nonneg Cσ]
  have hD3 : D₀ + Cσ ≤ |D₁| + |D₀| + |B'| + |Cσ| := by
    linarith [abs_nonneg D₁, le_abs_self D₀, abs_nonneg B', le_abs_self Cσ]
  have hP1 : L ^ D₁ ≤ L ^ (|D₁| + |D₀| + |B'| + |Cσ|) :=
    Real.rpow_le_rpow_of_exponent_le hL hD1
  have hP2 : L ^ D₀ * L ^ B' ≤ L ^ (|D₁| + |D₀| + |B'| + |Cσ|) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL hD2
  have hP3 : L ^ D₀ * L ^ Cσ ≤ L ^ (|D₁| + |D₀| + |B'| + |Cσ|) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL hD3
  have hu : |τ + σ| ≤ L ^ B' + L ^ Cσ := (abs_add_le τ σ).trans (add_le_add hτ hσ)
  have hD0 : 0 ≤ L ^ D₀ := Real.rpow_nonneg hL0.le _
  have hD10 : 0 ≤ L ^ D₁ := Real.rpow_nonneg hL0.le _
  have h2a : 0 ≤ 2 / a₁ := (div_pos two_pos ha₁).le
  have hlen : 0 ≤ a₂ - a₁ / 2 := by linarith
  have h1 : L ^ D₀ * |τ + σ| ≤ 2 * L ^ (|D₁| + |D₀| + |B'| + |Cσ|) :=
    calc L ^ D₀ * |τ + σ| ≤ L ^ D₀ * (L ^ B' + L ^ Cσ) := mul_le_mul_of_nonneg_left hu hD0
      _ = L ^ D₀ * L ^ B' + L ^ D₀ * L ^ Cσ := mul_add _ _ _
      _ ≤ 2 * L ^ (|D₁| + |D₀| + |B'| + |Cσ|) := by linarith
  have h2 : L ^ D₁ + L ^ D₀ * (|τ + σ| * (2 / a₁)) ≤
      (1 + 4 / a₁) * L ^ (|D₁| + |D₀| + |B'| + |Cσ|) :=
    calc L ^ D₁ + L ^ D₀ * (|τ + σ| * (2 / a₁))
        = L ^ D₁ + L ^ D₀ * |τ + σ| * (2 / a₁) := by ring
      _ ≤ L ^ (|D₁| + |D₀| + |B'| + |Cσ|) +
            2 * L ^ (|D₁| + |D₀| + |B'| + |Cσ|) * (2 / a₁) :=
          add_le_add hP1 (mul_le_mul_of_nonneg_right h1 h2a)
      _ = (1 + 4 / a₁) * L ^ (|D₁| + |D₀| + |B'| + |Cσ|) := by ring
  have h20 : 0 ≤ L ^ D₁ + L ^ D₀ * (|τ + σ| * (2 / a₁)) :=
    add_nonneg hD10 (mul_nonneg hD0 (mul_nonneg (abs_nonneg _) h2a))
  calc kR * ((L ^ D₁ + L ^ D₀ * (|τ + σ| * (2 / a₁))) * (a₂ - a₁ / 2))
      ≤ L ^ C₆ * ((1 + 4 / a₁) * L ^ (|D₁| + |D₀| + |B'| + |Cσ|) * (a₂ - a₁ / 2)) :=
        mul_le_mul hk (mul_le_mul_of_nonneg_right h2 hlen) (mul_nonneg h20 hlen)
          (Real.rpow_nonneg hL0.le _)
    _ = (1 + 4 / a₁) * (a₂ - a₁ / 2) * (L ^ C₆ * L ^ (|D₁| + |D₀| + |B'| + |Cσ|)) := by ring
    _ = (1 + 4 / a₁) * (a₂ - a₁ / 2) * L ^ (C₆ + (|D₁| + |D₀| + |B'| + |Cσ|)) := by
        rw [← Real.rpow_add hL0]

/-! ### The comparison -/

/-- **(cor:low-main-term) with explicit error**: for a `C¹` cutoff `ψ₁` supported in `[a₁, a₂]`
with `|ψ₁| ≤ A₀`, `|ψ₁'| ≤ A₁`, a frequency `u`, a modulus `k ≥ 1` and `m ≥ 1` coprime to `k`,
the error of (cor:low-main-term) is at most `k (A₁ + 2 A₀ |u| / a₁) (a₂ - a₁/2)`, for every
`Y > 0`. -/
theorem lowMainTerm_core (hSPS : SmoothProgressionSum) {a₁ a₂ : ℝ} (ha₁ : 0 < a₁)
    (ha₁₂ : a₁ ≤ a₂) {Y : ℝ} (hY : 0 < Y) {ψ₁ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ₁)
    (hsupp : Function.support ψ₁ ⊆ Set.Icc a₁ a₂) {A₀ A₁ : ℝ} (hb0 : ∀ z : ℝ, ‖ψ₁ z‖ ≤ A₀)
    (hb1 : ∀ z : ℝ, ‖deriv ψ₁ z‖ ≤ A₁) (u : ℝ) {k : ℕ} (hk : 0 < k) (h : ℤ) {m : ℕ}
    (hm : 0 < m) (hmk : m.Coprime k) :
    ‖(∑ᶠ v : ℕ, ψ₁ (((m * v : ℕ) : ℝ) / Y) * ((m * v : ℕ) : ℂ) ^ ((u : ℂ) * Complex.I) *
          addChar ((h : ℝ) * ((m * v : ℕ) : ℝ) / (k : ℝ))) -
        ((Y : ℂ) / (m : ℂ) *
          ((k : ℂ)⁻¹ * ∑ a ∈ Finset.range k, addChar ((h : ℝ) * (a : ℝ) / (k : ℝ))) *
          ∫ z in a₁..a₂, ψ₁ z * ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I))‖ ≤
      (k : ℝ) * ((A₁ + A₀ * (|u| * (2 / a₁))) * (a₂ - a₁ / 2)) := by
  obtain ⟨hψd, -⟩ := contDiff_one_iff_deriv.mp hψ
  have hY0 : Y ≠ 0 := hY.ne'
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  -- the scaling `c = m / Y`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (m : ℝ) / Y := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hc]
    exact div_pos hmR hY
  have hYc : ∀ y : ℝ, Y * (c * y) = (m : ℝ) * y := by
    intro y
    rw [hc, ← mul_assoc, mul_comm Y, div_mul_cancel₀ _ hY0]
  -- the function `F(y) = G(c y)`, `G(z) = ψ₁(z) exp(i u log(Yz))`
  have hG : ContDiff ℝ 1 (fun z => ψ₁ z * mellinPhase Y u z) :=
    contDiff_cutoff_mul hψ hsupp ha₁ hY0 u
  have hlin : ContDiff ℝ 1 (fun y : ℝ => c * y) := contDiff_const.mul contDiff_id
  have hF : ContDiff ℝ 1 (fun y : ℝ => ψ₁ (c * y) * mellinPhase Y u (c * y)) := hG.comp hlin
  have hzero : ∀ y : ℝ, c * y ∉ Set.Icc a₁ a₂ →
      ψ₁ (c * y) * mellinPhase Y u (c * y) = 0 := by
    intro y hy
    rw [eq_zero_of_notMem_Icc hsupp hy, zero_mul]
  have hF0 : ∀ y : ℝ, y ≤ 0 → ψ₁ (c * y) * mellinPhase Y u (c * y) = 0 := by
    intro y hy
    refine hzero y fun hmem => ?_
    have h2 : c * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0.le hy
    have h3 : a₁ ≤ c * y := hmem.1
    linarith
  have hFc : HasCompactSupport (fun y : ℝ => ψ₁ (c * y) * mellinPhase Y u (c * y)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := a₁ / c) (b := a₂ / c)) fun y hy => ?_
    refine hzero y fun hmem => hy ⟨?_, ?_⟩
    · rw [div_le_iff₀ hc0, mul_comm]
      exact hmem.1
    · rw [le_div_iff₀ hc0, mul_comm]
      exact hmem.2
  -- the integral of `F`
  have hIG : ∫ z : ℝ, ψ₁ z * mellinPhase Y u z =
      ∫ z in a₁..a₂, ψ₁ z * ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I) := by
    have hfun : (fun z : ℝ => ψ₁ z * ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I)) =
        fun z : ℝ => ψ₁ z * mellinPhase Y u z :=
      funext fun z => cutoff_mul_cpow_eq hsupp ha₁ hY u z
    have hset : ∫ z in Set.Icc a₁ a₂, ψ₁ z * mellinPhase Y u z =
        ∫ z : ℝ, ψ₁ z * mellinPhase Y u z :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [eq_zero_of_notMem_Icc hsupp hz, zero_mul]
    rw [hfun, intervalIntegral.integral_of_le ha₁₂,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc, hset]
  have hIF : ∫ y : ℝ, ψ₁ (c * y) * mellinPhase Y u (c * y) =
      (Y : ℂ) / (m : ℂ) *
        ∫ z in a₁..a₂, ψ₁ z * ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I) := by
    have h1 : ∫ y : ℝ, ψ₁ (c * y) * mellinPhase Y u (c * y) =
        |c⁻¹| • ∫ z : ℝ, ψ₁ z * mellinPhase Y u z :=
      MeasureTheory.Measure.integral_comp_mul_left (fun z => ψ₁ z * mellinPhase Y u z) c
    have h2 : |c⁻¹| = Y / (m : ℝ) := by
      rw [abs_of_pos (inv_pos.mpr hc0), hc, inv_div]
    have h3 : (Y / (m : ℝ) : ℝ) •
          (∫ z in a₁..a₂, ψ₁ z * ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I)) =
        (Y : ℂ) / (m : ℂ) *
          ∫ z in a₁..a₂, ψ₁ z * ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_div]
      exact Complex.real_smul
    rw [h1, h2, hIG, h3]
  -- the derivative of `F`
  have hErr : ∫ y : ℝ, ‖deriv (fun y : ℝ => ψ₁ (c * y) * mellinPhase Y u (c * y)) y‖ ≤
      (A₁ + A₀ * (|u| * (2 / a₁))) * (a₂ - a₁ / 2) := by
    have hfun : (fun y : ℝ => ‖deriv (fun y : ℝ => ψ₁ (c * y) * mellinPhase Y u (c * y)) y‖) =
        fun y : ℝ => c * ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) (c * y)‖ := by
      funext y
      have hd : deriv (fun y : ℝ => ψ₁ (c * y) * mellinPhase Y u (c * y)) y =
          c • deriv (fun z => ψ₁ z * mellinPhase Y u z) (c * y) :=
        deriv_comp_mul_left c (fun z => ψ₁ z * mellinPhase Y u z) y
      rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    have h3 : ∫ y : ℝ, ‖deriv (fun y : ℝ => ψ₁ (c * y) * mellinPhase Y u (c * y)) y‖ =
        ∫ z : ℝ, ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖ := by
      rw [hfun, MeasureTheory.integral_const_mul,
        MeasureTheory.Measure.integral_comp_mul_left
          (fun z => ‖deriv (fun z => ψ₁ z * mellinPhase Y u z) z‖) c,
        abs_of_pos (inv_pos.mpr hc0), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc0.ne',
        one_mul]
    rw [h3]
    exact integral_norm_deriv_cutoff_mul_le hψd hsupp ha₁ ha₁₂ hY0 u hb0 hb1
  -- the comparison on each residue class
  have hclass : ∀ b : ℕ, ‖(∑ᶠ n : ℕ, if n ≡ b [MOD k] then
        ψ₁ (c * (n : ℝ)) * mellinPhase Y u (c * (n : ℝ)) else 0) -
      (k : ℂ)⁻¹ * ((Y : ℂ) / (m : ℂ) *
        ∫ z in a₁..a₂, ψ₁ z * ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I))‖ ≤
      (A₁ + A₀ * (|u| * (2 / a₁))) * (a₂ - a₁ / 2) := by
    intro b
    have h2 : ‖(∑ᶠ n : ℕ, if n ≡ b [MOD k] then
          ψ₁ (c * (n : ℝ)) * mellinPhase Y u (c * (n : ℝ)) else 0) -
        (k : ℂ)⁻¹ * ∫ y : ℝ, ψ₁ (c * y) * mellinPhase Y u (c * y)‖ ≤
        ∫ y : ℝ, ‖deriv (fun y : ℝ => ψ₁ (c * y) * mellinPhase Y u (c * y)) y‖ :=
      hSPS (fun y : ℝ => ψ₁ (c * y) * mellinPhase Y u (c * y)) hF hFc hF0 k hk b
    rw [hIF] at h2
    exact h2.trans hErr
  -- the summand in terms of `F`
  have hterm : ∀ v : ℕ,
      ψ₁ (((m * v : ℕ) : ℝ) / Y) * ((m * v : ℕ) : ℂ) ^ ((u : ℂ) * Complex.I) =
        ψ₁ (c * (v : ℝ)) * mellinPhase Y u (c * (v : ℝ)) := by
    intro v
    have e1 : ((m * v : ℕ) : ℝ) / Y = c * (v : ℝ) := by
      rw [Nat.cast_mul, hc, mul_div_right_comm]
    have e2 : ((m * v : ℕ) : ℂ) = ((Y * (c * (v : ℝ)) : ℝ) : ℂ) := by
      rw [hYc, ← Nat.cast_mul, Complex.ofReal_natCast]
    rw [e1, e2]
    exact cutoff_mul_cpow_eq hsupp ha₁ hY u (c * (v : ℝ))
  have hχ : ∀ v : ℕ, addChar ((h : ℝ) * ((m * v : ℕ) : ℝ) / (k : ℝ)) =
      addChar ((h : ℝ) * ((m * (v % k) : ℕ) : ℝ) / (k : ℝ)) := by
    intro v
    rw [addChar_mod h hk (m * v), addChar_mod h hk (m * (v % k)), Nat.mul_mod_mod]
  -- the support of `v ↦ F(v)` is finite
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v : ℕ,
      ψ₁ (c * (v : ℝ)) * mellinPhase Y u (c * (v : ℝ)) ≠ 0 → v ∈ Finset.range N := by
    refine ⟨⌊a₂ / c⌋₊ + 1, fun v hv => ?_⟩
    have hmem : c * (v : ℝ) ∈ Set.Icc a₁ a₂ := by
      by_contra hcon
      exact hv (hzero (v : ℝ) hcon)
    have hle : (v : ℝ) ≤ a₂ / c := by
      rw [le_div_iff₀ hc0, mul_comm]
      exact hmem.2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hle))
  have hSb : ∀ b : ℕ, (∑ᶠ n : ℕ, if n ≡ b [MOD k] then
        ψ₁ (c * (n : ℝ)) * mellinPhase Y u (c * (n : ℝ)) else 0) =
      ∑ n ∈ Finset.range N, if n ≡ b [MOD k] then
        ψ₁ (c * (n : ℝ)) * mellinPhase Y u (c * (n : ℝ)) else 0 := by
    intro b
    refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
    have hn' : (if n ≡ b [MOD k] then
        ψ₁ (c * (n : ℝ)) * mellinPhase Y u (c * (n : ℝ)) else 0) ≠ 0 :=
      Function.mem_support.mp hn
    by_cases hb : n ≡ b [MOD k]
    · rw [if_pos hb] at hn'
      exact Finset.mem_coe.mpr (hN n hn')
    · exact absurd (if_neg hb) hn'
  -- the sum over `v` is the sum over the residue classes
  have hS : (∑ᶠ v : ℕ, ψ₁ (((m * v : ℕ) : ℝ) / Y) *
        ((m * v : ℕ) : ℂ) ^ ((u : ℂ) * Complex.I) *
        addChar ((h : ℝ) * ((m * v : ℕ) : ℝ) / (k : ℝ))) =
      ∑ b ∈ Finset.range k, addChar ((h : ℝ) * ((m * b : ℕ) : ℝ) / (k : ℝ)) *
        ∑ᶠ n : ℕ, if n ≡ b [MOD k] then
          ψ₁ (c * (n : ℝ)) * mellinPhase Y u (c * (n : ℝ)) else 0 := by
    have hcongr : (∑ᶠ v : ℕ, ψ₁ (((m * v : ℕ) : ℝ) / Y) *
          ((m * v : ℕ) : ℂ) ^ ((u : ℂ) * Complex.I) *
          addChar ((h : ℝ) * ((m * v : ℕ) : ℝ) / (k : ℝ))) =
        ∑ᶠ v : ℕ, ψ₁ (c * (v : ℝ)) * mellinPhase Y u (c * (v : ℝ)) *
          addChar ((h : ℝ) * ((m * (v % k) : ℕ) : ℝ) / (k : ℝ)) :=
      finsum_congr fun v => by rw [hterm v, hχ v]
    have hfs : (∑ᶠ v : ℕ, ψ₁ (c * (v : ℝ)) * mellinPhase Y u (c * (v : ℝ)) *
          addChar ((h : ℝ) * ((m * (v % k) : ℕ) : ℝ) / (k : ℝ))) =
        ∑ v ∈ Finset.range N, ψ₁ (c * (v : ℝ)) * mellinPhase Y u (c * (v : ℝ)) *
          addChar ((h : ℝ) * ((m * (v % k) : ℕ) : ℝ) / (k : ℝ)) := by
      refine finsum_eq_sum_of_support_subset _ fun v hv => ?_
      have hv' : ψ₁ (c * (v : ℝ)) * mellinPhase Y u (c * (v : ℝ)) *
          addChar ((h : ℝ) * ((m * (v % k) : ℕ) : ℝ) / (k : ℝ)) ≠ 0 :=
        Function.mem_support.mp hv
      exact Finset.mem_coe.mpr (hN v fun h0 => hv' (by rw [h0, zero_mul]))
    have hsplit : ∀ v ∈ Finset.range N,
        ψ₁ (c * (v : ℝ)) * mellinPhase Y u (c * (v : ℝ)) *
          addChar ((h : ℝ) * ((m * (v % k) : ℕ) : ℝ) / (k : ℝ)) =
        ∑ b ∈ Finset.range k, addChar ((h : ℝ) * ((m * b : ℕ) : ℝ) / (k : ℝ)) *
          (if v ≡ b [MOD k] then
            ψ₁ (c * (v : ℝ)) * mellinPhase Y u (c * (v : ℝ)) else 0) := by
      intro v _
      rw [Finset.sum_eq_single (v % k)]
      · rw [if_pos (Nat.mod_modEq v k).symm, mul_comm]
      · intro b hb hbv
        have hnot : ¬ v ≡ b [MOD k] := fun hvb =>
          hbv ((Nat.mod_eq_of_lt (Finset.mem_range.mp hb)).symm.trans hvb.symm)
        rw [if_neg hnot, mul_zero]
      · intro hnot
        exact absurd (Finset.mem_range.mpr (Nat.mod_lt v hk)) hnot
    rw [hcongr, hfs, Finset.sum_congr rfl hsplit, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hSb b, Finset.mul_sum]
  -- the main term in the form `(1/k) T J`
  have hmainEq : (Y : ℂ) / (m : ℂ) *
        ((k : ℂ)⁻¹ * ∑ a ∈ Finset.range k, addChar ((h : ℝ) * (a : ℝ) / (k : ℝ))) *
        ∫ z in a₁..a₂, ψ₁ z * ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I) =
      (k : ℂ)⁻¹ * (∑ a ∈ Finset.range k, addChar ((h : ℝ) * (a : ℝ) / (k : ℝ))) *
        ((Y : ℂ) / (m : ℂ) *
          ∫ z in a₁..a₂, ψ₁ z * ((Y * z : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I)) := by
    ring
  rw [hmainEq]
  exact norm_sub_main_le
    (χ := fun b : ℕ => addChar ((h : ℝ) * ((m * b : ℕ) : ℝ) / (k : ℝ)))
    (Sb := fun b : ℕ => ∑ᶠ n : ℕ, if n ≡ b [MOD k] then
      ψ₁ (c * (n : ℝ)) * mellinPhase Y u (c * (n : ℝ)) else 0)
    hS (fun b => norm_addChar _) hclass (sum_addChar_mul_coprime h hk hmk)

/-! ### The statement -/

/-- **(cor:low-main-term)** (`[P-06:0652–0667]`), from the first-order sum–integral comparison on
a progression. -/
theorem lowMainTerm : SmoothProgressionSum → LowMainTerm := by
  intro hSPS a₁ a₂ ha₁ ha₁₂ D₀ D₁ Cσ C₆ B'
  refine ⟨C₆ + (|D₁| + |D₀| + |B'| + |Cσ|), (1 + 4 / a₁) * (a₂ - a₁ / 2), Real.exp 1,
    fun x hx Y hY ψ₁ hψ hsupp hψ0 hψ1 σ τ hσ hτ k hk hkL h m hm hmk => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hL : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  obtain ⟨hψd, hψ2⟩ := contDiff_infty_iff_deriv.mp hψ
  have hψC1 : ContDiff ℝ 1 ψ₁ := contDiff_one_iff_deriv.mpr ⟨hψd, hψ2.continuous⟩
  have hcore := lowMainTerm_core hSPS ha₁ ha₁₂ hY hψC1 hsupp hψ0 hψ1 (τ + σ) hk h hm hmk
  exact hcore.trans (low_error_bound hL ha₁ ha₁₂ hkL hσ hτ)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
