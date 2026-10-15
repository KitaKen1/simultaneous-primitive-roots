module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ClassicalInputs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# First-order sum–integral comparison on a progression

`smoothProgressionSum : SmoothProgressionSum` (`EndpointProof/ClassicalInputs.lean`; the tool of
`[P-06:0653–0667]` and of `[P-02:0169–0173]`): for a `C¹` compactly supported `F : ℝ → ℂ` vanishing
on `(-∞, 0]`, a modulus `k ≥ 1` and a residue `a`,

`‖∑_{n ≥ 0, n ≡ a (k)} F(n) - (1/k) ∫ F‖ ≤ ∫ ‖F'‖`.

The proof is written for functions with values in a real Banach space `E`
(`norm_progression_sum_sub_integral_le`), so that the real-valued count of [P] §7
(`Extraction.SmoothProgressionCount`, `Extraction/SmoothCount.lean`) is the same lemma.

* One cell (`norm_smul_sub_integral_le`): for `h ≥ 0`,
  `‖h F(c) - ∫_c^{c+h} F‖ ≤ h ∫_c^{c+h} ‖F'‖`, because
  `∫_c^{c+h} (F(u) - F(c)) du` has an integrand `F(u) - F(c) = ∫_c^u F'` of norm at most
  `∫_c^{c+h} ‖F'‖`.
* A chain of cells (`norm_sum_sub_integral_le`): for nodes `t_{j+1} = t_j + h`, `h > 0`,
  `‖∑_{j < n} F(t_j) - (1/h) ∫_{t_0}^{t_n} F‖ ≤ ∫_{t_0}^{t_n} ‖F'‖`.
* The progression: with `r = a mod k` the nodes are `t_j = r - k + j k`, `0 ≤ j ≤ N + 1`. The
  first node `t_0 = r - k` is negative, so `F(t_0) = 0`; `t_{j+1} = r + j k` runs through the
  integers `n ≡ a (mod k)`; and `t_{N+1} ≥ N` is beyond the support of `F`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open MeasureTheory

noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **One cell**: `‖h F(c) - ∫_c^{c+h} F‖ ≤ h ∫_c^{c+h} ‖F'‖` for `h ≥ 0`. -/
theorem norm_smul_sub_integral_le {F : ℝ → E} (hFd : Differentiable ℝ F)
    (hF' : Continuous (deriv F)) (c : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ‖h • F c - ∫ u in c..(c + h), F u‖ ≤ h * ∫ u in c..(c + h), ‖deriv F u‖ := by
  have hcd : c ≤ c + h := by linarith
  have hFc : Continuous F := hFd.continuous
  have hnorm : Continuous fun u => ‖deriv F u‖ := hF'.norm
  have hpt : ∀ u ∈ Set.uIoc c (c + h), ‖F u - F c‖ ≤ ∫ y in c..(c + h), ‖deriv F y‖ := by
    intro u hu
    rw [Set.uIoc_of_le hcd] at hu
    have hcu : c ≤ u := hu.1.le
    have hud : u ≤ c + h := hu.2
    have hftc : ∫ y in c..u, deriv F y = F u - F c :=
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hFd.differentiableAt)
        (hF'.intervalIntegrable c u)
    calc ‖F u - F c‖ = ‖∫ y in c..u, deriv F y‖ := by rw [hftc]
      _ ≤ ∫ y in c..u, ‖deriv F y‖ := intervalIntegral.norm_integral_le_integral_norm hcu
      _ ≤ ∫ y in c..(c + h), ‖deriv F y‖ :=
          intervalIntegral.integral_mono_interval le_rfl hcu hud
            (Filter.Eventually.of_forall fun y => norm_nonneg (deriv F y))
            (hnorm.intervalIntegrable c (c + h))
  have hsub : ∫ u in c..(c + h), (F u - F c) = (∫ u in c..(c + h), F u) - h • F c := by
    have h1 : ∫ u in c..(c + h), (F u - F c) =
        (∫ u in c..(c + h), F u) - ∫ _u in c..(c + h), F c :=
      intervalIntegral.integral_sub (hFc.intervalIntegrable c (c + h))
        (continuous_const.intervalIntegrable c (c + h))
    rw [h1, intervalIntegral.integral_const, add_sub_cancel_left]
  have hbound : ‖∫ u in c..(c + h), (F u - F c)‖ ≤
      (∫ y in c..(c + h), ‖deriv F y‖) * |c + h - c| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [hsub, add_sub_cancel_left, abs_of_nonneg hh] at hbound
  rw [norm_sub_rev, mul_comm h]
  exact hbound

/-- **A chain of cells**: for nodes `t_{j+1} = t_j + h` with `h > 0`,
`‖∑_{j < n} F(t_j) - (1/h) ∫_{t_0}^{t_n} F‖ ≤ ∫_{t_0}^{t_n} ‖F'‖`. -/
theorem norm_sum_sub_integral_le {F : ℝ → E} (hFd : Differentiable ℝ F)
    (hF' : Continuous (deriv F)) {h : ℝ} (hh : 0 < h) (t : ℕ → ℝ)
    (ht : ∀ j : ℕ, t (j + 1) = t j + h) (n : ℕ) :
    ‖(∑ j ∈ Finset.range n, F (t j)) - h⁻¹ • ∫ u in (t 0)..(t n), F u‖ ≤
      ∫ u in (t 0)..(t n), ‖deriv F u‖ := by
  have hFc : Continuous F := hFd.continuous
  have hnorm : Continuous fun u => ‖deriv F u‖ := hF'.norm
  have hsumF : ∑ j ∈ Finset.range n, ∫ u in (t j)..(t (j + 1)), F u =
      ∫ u in (t 0)..(t n), F u :=
    intervalIntegral.sum_integral_adjacent_intervals fun j _ => hFc.intervalIntegrable _ _
  have hsumD : ∑ j ∈ Finset.range n, ∫ u in (t j)..(t (j + 1)), ‖deriv F u‖ =
      ∫ u in (t 0)..(t n), ‖deriv F u‖ :=
    intervalIntegral.sum_integral_adjacent_intervals fun j _ => hnorm.intervalIntegrable _ _
  have hinv : 0 < h⁻¹ := inv_pos.mpr hh
  have hcell : ∀ j : ℕ, ‖F (t j) - h⁻¹ • ∫ u in (t j)..(t (j + 1)), F u‖ ≤
      ∫ u in (t j)..(t (j + 1)), ‖deriv F u‖ := by
    intro j
    have h1 := norm_smul_sub_integral_le hFd hF' (t j) hh.le
    rw [← ht j] at h1
    have h2 : F (t j) - h⁻¹ • ∫ u in (t j)..(t (j + 1)), F u =
        h⁻¹ • (h • F (t j) - ∫ u in (t j)..(t (j + 1)), F u) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
    calc h⁻¹ * ‖h • F (t j) - ∫ u in (t j)..(t (j + 1)), F u‖
        ≤ h⁻¹ * (h * ∫ u in (t j)..(t (j + 1)), ‖deriv F u‖) :=
          mul_le_mul_of_nonneg_left h1 hinv.le
      _ = ∫ u in (t j)..(t (j + 1)), ‖deriv F u‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
  have hsplit : ∑ j ∈ Finset.range n, (F (t j) - h⁻¹ • ∫ u in (t j)..(t (j + 1)), F u) =
      (∑ j ∈ Finset.range n, F (t j)) - h⁻¹ • ∫ u in (t 0)..(t n), F u := by
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hsumF]
  rw [← hsplit]
  calc ‖∑ j ∈ Finset.range n, (F (t j) - h⁻¹ • ∫ u in (t j)..(t (j + 1)), F u)‖
      ≤ ∑ j ∈ Finset.range n, ‖F (t j) - h⁻¹ • ∫ u in (t j)..(t (j + 1)), F u‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n, ∫ u in (t j)..(t (j + 1)), ‖deriv F u‖ :=
        Finset.sum_le_sum fun j _ => hcell j
    _ = ∫ u in (t 0)..(t n), ‖deriv F u‖ := hsumD

/-- **First-order sum–integral comparison on a progression**, for a differentiable function with
continuous derivative and compact support, vanishing on `(-∞, 0]`, with values in a real Banach
space:

`‖∑_{n ≥ 0, n ≡ a (k)} F(n) - (1/k) ∫ F‖ ≤ ∫ ‖F'‖`. -/
theorem norm_progression_sum_sub_integral_le {F : ℝ → E} (hFd : Differentiable ℝ F)
    (hF' : Continuous (deriv F)) (hc : HasCompactSupport F) (h0 : ∀ u : ℝ, u ≤ 0 → F u = 0)
    {k : ℕ} (hk : 0 < k) (a : ℕ) :
    ‖(∑ᶠ n : ℕ, if n ≡ a [MOD k] then F (n : ℝ) else 0) - (k : ℝ)⁻¹ • ∫ u : ℝ, F u‖ ≤
      ∫ u : ℝ, ‖deriv F u‖ := by
  -- the support of `F` is bounded above
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ u : ℝ, R < u → F u = 0 := by
    obtain ⟨R, hR⟩ := hc.isCompact.bddAbove
    exact ⟨R, fun u hu => image_eq_zero_of_notMem_tsupport fun hmem =>
      absurd (hR hmem) (not_le.mpr hu)⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, R < (N : ℝ) := exists_nat_gt R
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = a % k := ⟨_, rfl⟩
  have hrk : r < k := by
    rw [hr]
    exact Nat.mod_lt a hk
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hrkR : (r : ℝ) < (k : ℝ) := by exact_mod_cast hrk
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  -- the nodes `t j = r - k + j k`
  obtain ⟨t, ht_def⟩ : ∃ t : ℕ → ℝ, ∀ j : ℕ, t j = (r : ℝ) - (k : ℝ) + (j : ℝ) * (k : ℝ) :=
    ⟨fun j => (r : ℝ) - (k : ℝ) + (j : ℝ) * (k : ℝ), fun _ => rfl⟩
  have ht0 : t 0 = (r : ℝ) - (k : ℝ) := by
    rw [ht_def, Nat.cast_zero, zero_mul, add_zero]
  have htsucc : ∀ j : ℕ, t (j + 1) = (r : ℝ) + (j : ℝ) * (k : ℝ) := by
    intro j
    rw [ht_def, Nat.cast_add, Nat.cast_one]
    ring
  have ht : ∀ j : ℕ, t (j + 1) = t j + (k : ℝ) := by
    intro j
    rw [htsucc, ht_def]
    ring
  have hFt0 : F (t 0) = 0 := h0 _ (by rw [ht0]; linarith)
  have hNk : (N : ℝ) ≤ (N : ℝ) * (k : ℝ) := le_mul_of_one_le_right (Nat.cast_nonneg N) hk1
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- the integrals over `ℝ` are integrals over `(t 0, t (N + 1)]`
  have hsuppF : Function.support F ⊆ Set.Ioc (t 0) (t (N + 1)) := by
    intro u hu
    have hu' : F u ≠ 0 := Function.mem_support.mp hu
    have hupos : 0 < u := by
      by_contra hcon
      exact hu' (h0 u (not_lt.mp hcon))
    have huR : u ≤ R := by
      by_contra hcon
      exact hu' (hR u (not_le.mp hcon))
    refine ⟨?_, ?_⟩
    · rw [ht0]
      linarith
    · rw [htsucc]
      linarith
  have hle : t 0 ≤ t (N + 1) := by
    rw [ht0, htsucc]
    linarith
  have hIF : ∫ u in (t 0)..(t (N + 1)), F u = ∫ u : ℝ, F u :=
    intervalIntegral.integral_eq_integral_of_support_subset hsuppF
  have hDint : Integrable (fun u : ℝ => ‖deriv F u‖) volume :=
    (hF'.integrable_of_hasCompactSupport hc.deriv).norm
  have hID : ∫ u in (t 0)..(t (N + 1)), ‖deriv F u‖ ≤ ∫ u : ℝ, ‖deriv F u‖ := by
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_le_integral hDint
      (Filter.Eventually.of_forall fun u => norm_nonneg (deriv F u))
  -- the sum over the progression is the sum over the nodes
  have hinj : Function.Injective fun j : ℕ => r + k * j := fun i j hij =>
    Nat.eq_of_mul_eq_mul_left hk (Nat.add_left_cancel hij)
  have hmodj : ∀ j : ℕ, r + k * j ≡ a [MOD k] := by
    intro j
    show (r + k * j) % k = a % k
    rw [Nat.add_mul_mod_self_left, hr, Nat.mod_mod]
  have hfin : (∑ᶠ n : ℕ, if n ≡ a [MOD k] then F (n : ℝ) else 0) =
      ∑ j ∈ Finset.range N, F ((r + k * j : ℕ) : ℝ) := by
    have hsupp : (Function.support fun n : ℕ => if n ≡ a [MOD k] then F (n : ℝ) else 0) ⊆
        (((Finset.range N).image fun j : ℕ => r + k * j : Finset ℕ) : Set ℕ) := by
      intro n hn
      have hn' : (if n ≡ a [MOD k] then F (n : ℝ) else 0) ≠ 0 := Function.mem_support.mp hn
      have hmod : n ≡ a [MOD k] := by
        by_contra hcon
        exact hn' (if_neg hcon)
      have hFn : F (n : ℝ) ≠ 0 := by
        rw [if_pos hmod] at hn'
        exact hn'
      have hnr : n % k = r := by
        rw [hr]
        exact hmod
      have hdecomp : r + k * (n / k) = n := by
        rw [← hnr]
        exact Nat.mod_add_div n k
      have hlt : n / k < N := by
        by_contra hcon
        have h1 : N ≤ n := (not_lt.mp hcon).trans (Nat.div_le_self n k)
        have h2 : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h1
        exact hFn (hR _ (lt_of_lt_of_le hN h2))
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨n / k, Finset.mem_range.mpr hlt, hdecomp⟩)
    refine (finsum_eq_sum_of_support_subset _ hsupp).trans ?_
    refine (Finset.sum_image hinj.injOn).trans ?_
    exact Finset.sum_congr rfl fun j _ => if_pos (hmodj j)
  have hsumt : ∑ j ∈ Finset.range (N + 1), F (t j) =
      ∑ j ∈ Finset.range N, F ((r + k * j : ℕ) : ℝ) := by
    rw [Finset.sum_range_succ', hFt0, add_zero]
    refine Finset.sum_congr rfl fun j _ => congrArg F ?_
    rw [htsucc, Nat.cast_add, Nat.cast_mul]
    ring
  have hmain := norm_sum_sub_integral_le hFd hF' hkR t ht (N + 1)
  rw [hsumt, hIF] at hmain
  rw [hfin]
  exact hmain.trans hID

end General

/-- **First-order sum–integral comparison on a progression** (`SmoothProgressionSum`): for a
`C¹` compactly supported `F : ℝ → ℂ` vanishing on `(-∞, 0]`,
`‖∑_{n ≥ 0, n ≡ a (k)} F(n) - (1/k) ∫ F‖ ≤ ∫ ‖F'‖`. -/
theorem smoothProgressionSum : SmoothProgressionSum := by
  intro F hF hc h0 k hk a
  obtain ⟨hFd, hF'⟩ := contDiff_one_iff_deriv.mp hF
  have h : ‖(∑ᶠ n : ℕ, if n ≡ a [MOD k] then F (n : ℝ) else 0) -
      ((k : ℝ)⁻¹ : ℝ) • ∫ u : ℝ, F u‖ ≤ ∫ u : ℝ, ‖deriv F u‖ :=
    norm_progression_sum_sub_integral_le hFd hF' hc h0 hk a
  have hsm : ((k : ℝ)⁻¹ : ℝ) • (∫ u : ℝ, F u) = (k : ℂ)⁻¹ * ∫ u : ℝ, F u := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    exact Complex.real_smul
  rw [hsm] at h
  exact h

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
