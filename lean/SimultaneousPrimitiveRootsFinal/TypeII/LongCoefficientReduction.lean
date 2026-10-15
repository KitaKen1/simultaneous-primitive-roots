import ArtinPrimitiveRoots.TypeII.Marked
import SimultaneousPrimitiveRoots.Unconditional.Supply.TypeII
import SimultaneousPrimitiveRootsFinal.TypeII.MarkedTransferReduction

/-!
# [P] Lemma 5.2 (the long coefficient) from the vendored formalization of [A]

`Supply.PrimeMinusRoughLongCoefficient` (`Supply/TypeII.lean`) is [P] Lemma 5.2
(`[P-05:0044–0055]`): the coefficient test for the prime-minus-rough coefficient
`α_m = m^{iv} (1_{m prime} - 1_{m rough} / (V(W) log m))` on every interval of `[H_m, 2H_m]`.

The vendored formalization of [A] proves the same cancellation for the coefficient of [A]
Proposition `prop:rough-type-ii`,

`roughCoefficient x γ v m =
  e^{iv log m} (1_{P⁻(m) > x^γ} - D_γ(log m / log x) / (log x · V(W)) · 1_{m rough})`,

when `log H_m / log x` and `log (2H_m) / log x` lie in a window `[wMin, wMax]` with
`γ < wMin < wMax < 1`: `ArtinPrimitiveRoots.TypeII.Rough.low_frequency` for `|t| ≤ L^{B₂}` and
`ArtinPrimitiveRoots.TypeII.Rough.high_frequency` for `L^{B₂} ≤ |t| ≤ 2 X L^B`
(`vendor/ArtinPrimitiveRoots/TypeII/Rough.lean`). That file is at the end of a long import chain,
so this file does not import it: the two theorems are stated as the propositions
`VendoredRoughLowFrequency`, `VendoredRoughHighFrequency` (with `vendoredRoughCoefficient`, a copy
of the definition of `roughCoefficient`), and this file proves

`primeMinusRoughLongCoefficient_of_vendored :
  VendoredRoughLowFrequency → VendoredRoughHighFrequency → Supply.PrimeMinusRoughLongCoefficient`.

`TypeII/LongCoefficientBridge.lean` discharges the two hypotheses.

## The argument

* On a window with `wMax < 2γ` the two coefficients are *equal* on `[H_m, 2H_m]`
  (`vendoredRoughCoefficient_eq_primeMinusRough`): an integer `x^γ < m < x^{2γ}` has `P⁻(m) > x^γ`
  if and only if it is prime (`roughAbove_iff_prime`), and the rough density is
  `D_γ(u) = 1/u` for `u < 2γ` (`roughDensity_eq_one_div`), so that
  `D_γ(log m / log x) / (log x · V(W)) = 1 / (V(W) log m)`.
* For one such window the two vendored theorems give the coefficient test
  (`longCoefficient_window`); `high_frequency` is stated for `x/2 ≤ H_m H_n ≤ 2x`, and is applied
  at the scales `(H_m, x / H_m)` with `B + 1`, as in the vendored
  `ArtinPrimitiveRoots.Proofs.c_typeii_sol.twisted_rough_long_cancellation`.
* The exponents `log H_m / log x ∈ [δ, 1 - δ + o(1)]` are covered by the finitely many windows
  `[a_j, a_j + δ/4]`, `a_j = δ/2 + j δ/8`, `j ≤ 8/δ`, with `γ_j = a_j - δ/16` (`exists_window`); the
  constants of the lemma are the sums over `j` of the constants of the windows. (Only the windows
  with `a_j + δ/4 < 1` occur; if `δ > 1/2` there are no scales at large `x` and nothing to prove.)
-/

namespace SimultaneousPrimitiveRoots.Unconditional

open ArtinPrimitiveRoots.TypeII in
open _root_.Classical in
/-- A copy of the definition of `ArtinPrimitiveRoots.TypeII.Rough.roughCoefficient`
(`vendor/ArtinPrimitiveRoots/TypeII/Rough.lean`), the coefficient of [A]
`eq:rough-type-ii-coefficient`; `roughDensity` there abbreviates
`ArtinPrimitiveRoots.Sieve.roughDensity`. -/
noncomputable def vendoredRoughCoefficient (x γ v : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (Complex.I * v * Real.log (m : ℝ)) *
    (((if roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0) -
        ArtinPrimitiveRoots.Sieve.roughDensity γ (Real.log (m : ℝ) / Real.log x) /
          (Real.log x * roughSieveProduct (roughCutoff x)) *
            (if roughAbove m (roughCutoff x) then (1 : ℝ) else 0)) : ℂ)

open ArtinPrimitiveRoots.TypeII in
open _root_.Classical in
/-- **The statement of the vendored theorem** `ArtinPrimitiveRoots.TypeII.Rough.low_frequency`
(`vendor/ArtinPrimitiveRoots/TypeII/Rough.lean`), with the same binders in the same order (the
hypotheses are written as arrows) and `vendoredRoughCoefficient` for `roughCoefficient`. It is
discharged in `TypeII/LongCoefficientBridge.lean`. -/
def VendoredRoughLowFrequency : Prop :=
  ∀ (γ wMin wMax C δ : ℝ),
    0 < γ → γ < wMin → wMin < wMax → 0 < δ →
    0 < C →
    ∀ A₀ A B₂ : ℝ, 0 < A₀ → 0 < A → 0 < B₂ →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x δ ≤ M →
            Real.log M / Real.log x ∈ Set.Icc wMin wMax →
            ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
              ∀ v t : ℝ, |v| ≤ Real.rpow (Real.log x) C →
                |t| ≤ Real.rpow (Real.log x) B₂ →
                  ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                    ∀ χ : DirichletCharacter ℂ k,
                      ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                          vendoredRoughCoefficient x γ v m * χ (m : ZMod k) *
                            Complex.exp (Complex.I * t * Real.log (m : ℝ))) / M‖ ≤
                        C₀ * Real.rpow (Real.log x) (-A)

open ArtinPrimitiveRoots.TypeII in
open _root_.Classical in
/-- **The statement of the vendored theorem** `ArtinPrimitiveRoots.TypeII.Rough.high_frequency`
(`vendor/ArtinPrimitiveRoots/TypeII/Rough.lean`), with the same binders in the same order (the
hypotheses are written as arrows) and `vendoredRoughCoefficient` for `roughCoefficient`. It is
discharged in `TypeII/LongCoefficientBridge.lean`. -/
def VendoredRoughHighFrequency : Prop :=
  ∀ (γ wMin wMax δ C A : ℝ), 0 < γ → γ < wMin →
    wMin < wMax → wMax < 1 → 0 < δ →
    0 < C → 0 < A →
    ∀ B : ℝ, 0 < B →
      ∃ B₂ C₀ x₀ : ℝ, 0 < B₂ ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ Hm Hn : ℝ, Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
            x / 2 ≤ Hm * Hn → Hm * Hn ≤ 2 * x →
            Real.log Hm / Real.log x ∈ Set.Icc wMin wMax →
            Real.log (2 * Hm) / Real.log x ∈ Set.Icc wMin wMax →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) C →
              ∀ χ : DirichletCharacter ℂ k, ∀ v t : ℝ,
                Real.rpow (Real.log x) B₂ ≤ |t| →
                |t| ≤ 2 * (Hm * Hn) * Real.rpow (Real.log x) B →
                |v| ≤ Real.rpow (Real.log x) C →
                  ∀ l r : ℝ, Hm ≤ l → l ≤ r → r ≤ 2 * Hm →
                    ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                          l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                        vendoredRoughCoefficient x γ v m * χ (m : ZMod k) *
                          Complex.exp (Complex.I * t * Real.log (m : ℝ))) / Hm‖ ≤
                      C₀ * Real.rpow (Real.log x) (-A)

namespace Supply.LongCoefficientBridge

open Supply.MarkedBridge

/-! ### The two coefficients agree on a window with `wMax < 2γ` -/

/-- An integer `m ≥ 2` with `y < m ≤ y²` has least prime factor `> y` if and only if it is
prime. -/
theorem roughAbove_iff_prime {y : ℝ} {m : ℕ} (hy : 0 ≤ y) (hm : 2 ≤ m) (h1 : y < (m : ℝ))
    (h2 : (m : ℝ) ≤ y * y) : ArtinPrimitiveRoots.TypeII.roughAbove m y ↔ m.Prime := by
  constructor
  · intro h
    by_contra hnp
    have hsq : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
    have hp : y < (m.minFac : ℝ) :=
      h m.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd m)
    have hsq' : ((m.minFac : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hsq
    have hlt : y * y < (m.minFac : ℝ) * (m.minFac : ℝ) := mul_self_lt_mul_self hy hp
    rw [pow_two] at hsq'
    linarith
  · intro hp p hpp hdvd
    rw [(Nat.prime_dvd_prime_iff_eq hpp hp).mp hdvd]
    exact h1

/-- The rough density `D_γ(u)` is `1/u` below `2γ`: only the term of one prime factor is
present. -/
theorem roughDensity_eq_one_div {γ u : ℝ} (hγ : 0 < γ) (hu : u < 2 * γ) :
    ArtinPrimitiveRoots.Sieve.roughDensity γ u = 1 / u := by
  have hcut : u < ((2 : ℕ) : ℝ) * γ := by simpa using hu
  rw [ArtinPrimitiveRoots.Sieve.b_density_sol.roughDensity_eq_sum_range_of_lt_mul hγ le_rfl hcut,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp [ArtinPrimitiveRoots.Sieve.roughDensityTerm]

/-- `D_γ(log m / log x) / (log x · V) · R = R / (V log m)` when `D_γ(u) = 1/u`. -/
theorem proxy_algebra {a b V R : ℝ} (hb : b ≠ 0) : 1 / (a / b) / (b * V) * R = R / (V * a) := by
  by_cases ha : a = 0
  · rw [ha]
    simp
  by_cases hV : V = 0
  · rw [hV]
    simp
  rw [one_div_div, div_div, div_mul_eq_mul_div,
    div_eq_div_iff (mul_ne_zero ha (mul_ne_zero hb hV)) (mul_ne_zero hV ha)]
  ring

open _root_.Classical in
/-- The vendored coefficient with the real factor under one cast. -/
theorem vendoredRoughCoefficient_apply (x γ v : ℝ) (m : ℕ) :
    vendoredRoughCoefficient x γ v m =
      Complex.exp (Complex.I * (v : ℂ) * (Real.log (m : ℝ) : ℂ)) *
        (((if ArtinPrimitiveRoots.TypeII.roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0) -
          ArtinPrimitiveRoots.Sieve.roughDensity γ (Real.log (m : ℝ) / Real.log x) /
            (Real.log x * ArtinPrimitiveRoots.TypeII.roughSieveProduct
              (ArtinPrimitiveRoots.TypeII.roughCutoff x)) *
            (if ArtinPrimitiveRoots.TypeII.roughAbove m (ArtinPrimitiveRoots.TypeII.roughCutoff x)
              then (1 : ℝ) else 0) : ℝ) : ℂ) := by
  unfold vendoredRoughCoefficient
  push_cast
  ring

/-- The prime-minus-rough coefficient vanishes outside its interval. -/
theorem primeMinusRough_eq_zero {x v lo hi : ℝ} {m : ℕ}
    (h : ¬ (lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi)) : Supply.primeMinusRough x v lo hi m = 0 := by
  unfold Supply.primeMinusRough
  exact if_neg h

open _root_.Classical in
/-- **The coefficient identity.** For `x^γ < m < x^{2γ}` in the interval `[lo, hi]`, the vendored
coefficient is the prime-minus-rough coefficient of [P] Theorem 3.1. -/
theorem vendoredRoughCoefficient_eq_primeMinusRough {x γ v lo hi : ℝ} {m : ℕ} (hx : 1 < x)
    (hγ : 0 < γ) (h1 : x ^ γ < (m : ℝ)) (h2 : (m : ℝ) < x ^ (2 * γ))
    (hlo : lo ≤ (m : ℝ)) (hhi : (m : ℝ) ≤ hi) :
    vendoredRoughCoefficient x γ v m = Supply.primeMinusRough x v lo hi m := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hm1 : (1 : ℝ) < m := (Real.one_lt_rpow hx hγ).trans h1
  have hm1' : 1 < m := by exact_mod_cast hm1
  have hm0 : m ≠ 0 := by omega
  have hmpos : (0 : ℝ) < m := by linarith
  -- `P⁻(m) > x^γ` if and only if `m` is prime
  have hprime : ArtinPrimitiveRoots.TypeII.roughAbove m (Real.rpow x γ) ↔ m.Prime := by
    refine roughAbove_iff_prime (Real.rpow_nonneg hx0.le γ) hm1' h1 ?_
    rw [Real.rpow_eq_pow, ← Real.rpow_add hx0, show γ + γ = 2 * γ by ring]
    exact h2.le
  -- the density at `u = log m / log x < 2γ`
  have hu : Real.log (m : ℝ) / Real.log x < 2 * γ := by
    rw [div_lt_iff₀ hlogx]
    have h := Real.log_lt_log hmpos h2
    rwa [Real.log_rpow hx0] at h
  -- the real factor
  have hreal :
      (if ArtinPrimitiveRoots.TypeII.roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0) -
          ArtinPrimitiveRoots.Sieve.roughDensity γ (Real.log (m : ℝ) / Real.log x) /
            (Real.log x * ArtinPrimitiveRoots.TypeII.roughSieveProduct
              (ArtinPrimitiveRoots.TypeII.roughCutoff x)) *
            (if ArtinPrimitiveRoots.TypeII.roughAbove m (ArtinPrimitiveRoots.TypeII.roughCutoff x)
              then (1 : ℝ) else 0) =
        (if m.Prime then (1 : ℝ) else 0) -
          (if Supply.IsRough (Supply.roughCutoff x) m then (1 : ℝ) else 0) /
            (Supply.mertensProduct (Supply.roughCutoff x) * Real.log (m : ℝ)) := by
    rw [if_congr hprime rfl rfl, roughDensity_eq_one_div hγ hu, roughCutoff_eq,
      proxy_algebra hlogx.ne']
    rfl
  rw [vendoredRoughCoefficient_apply, hreal, ← natCast_cpow_mul_I hm0]
  unfold Supply.primeMinusRough
  rw [if_pos (⟨hlo, hhi⟩ : lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi)]
  congr 1
  by_cases hp : m.Prime <;> by_cases hr : Supply.IsRough (Supply.roughCutoff x) m <;>
    simp [hp, hr]

/-- **The long coefficient sums agree.** If `x^γ < H_m` and `2H_m < x^{2γ}`, the twisted sum of the
prime-minus-rough coefficient on `[lo, hi] ⊆ [H_m, 2H_m]` is the sum of the vendored theorems. -/
theorem twistedSum_primeMinusRough_eq {x γ v lo hi Hm : ℝ} (hx : 1 < x) (hγ : 0 < γ)
    (hHm : 0 < Hm) (hlo : Hm ≤ lo) (hhi : hi ≤ 2 * Hm) (h1 : x ^ γ < Hm)
    (h2 : 2 * Hm < x ^ (2 * γ)) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) :
    Supply.twistedSum Hm (Supply.primeMinusRough x v lo hi) χ t =
      ∑ m ∈ (Finset.range (⌊hi⌋₊ + 1)).filter (fun (m : ℕ) => lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi),
        vendoredRoughCoefficient x γ v m * χ (m : ZMod k) *
          Complex.exp (Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ)) := by
  unfold Supply.twistedSum
  have hsub : (Finset.range (⌊hi⌋₊ + 1)).filter (fun (m : ℕ) => lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi) ⊆
      Supply.dyad Hm := by
    intro m hm
    obtain ⟨-, hm1, hm2⟩ := Finset.mem_filter.mp hm
    exact (Supply.mem_dyad hHm.le).mpr ⟨hlo.trans hm1, hm2.trans hhi⟩
  have hzero : ∀ m ∈ Supply.dyad Hm,
      m ∉ (Finset.range (⌊hi⌋₊ + 1)).filter (fun (m : ℕ) => lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi) →
      Supply.primeMinusRough x v lo hi m * χ (m : ZMod k) *
        (m : ℂ) ^ ((t : ℂ) * Complex.I) = 0 := by
    intro m _ hm
    have hnot : ¬ (lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi) := fun h =>
      hm (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor h.2)), h⟩)
    rw [primeMinusRough_eq_zero hnot, zero_mul, zero_mul]
  have hcongr : ∀ m ∈ (Finset.range (⌊hi⌋₊ + 1)).filter
        (fun (m : ℕ) => lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi),
      Supply.primeMinusRough x v lo hi m * χ (m : ZMod k) *
          (m : ℂ) ^ ((t : ℂ) * Complex.I) =
        vendoredRoughCoefficient x γ v m * χ (m : ZMod k) *
          Complex.exp (Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ)) := by
    intro m hm
    obtain ⟨-, hm1, hm2⟩ := Finset.mem_filter.mp hm
    have hmHm : Hm ≤ (m : ℝ) := hlo.trans hm1
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [Nat.cast_zero] at hmHm
      exact absurd hHm (not_lt.mpr hmHm)
    rw [vendoredRoughCoefficient_eq_primeMinusRough hx hγ (h1.trans_le hmHm)
      (lt_of_le_of_lt (hm2.trans hhi) h2) hm1 hm2, natCast_cpow_mul_I hm0]
  exact (Finset.sum_subset hsub hzero).symm.trans (Finset.sum_congr rfl hcongr)

/-! ### One window -/

/-- **The coefficient test on one window.** For `γ < wMin < wMax < min 1 (2γ)`, the two vendored
theorems give the bound of [P] Lemma 5.2 at all scales with `log H_m / log x` and
`log (2H_m) / log x` in `[wMin, wMax]`. -/
theorem longCoefficient_window (hlow : VendoredRoughLowFrequency)
    (hhigh : VendoredRoughHighFrequency) {γ wMin wMax δ C κ A₀ B A : ℝ} (hγ : 0 < γ)
    (hγw : γ < wMin) (hw : wMin < wMax) (hwMax : wMax < 1) (hwγ : wMax < 2 * γ) (hδ : 0 < δ)
    (hC : 0 < C) (hA₀ : 0 < A₀) (hB : 0 < B) (hA : 0 < A) :
    ∃ M x₀ : ℝ, 0 ≤ M ∧ ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ, x ^ δ ≤ Hm → Hm * Hn ≤ κ * x →
      Real.log Hm / Real.log x ∈ Set.Icc wMin wMax →
      Real.log (2 * Hm) / Real.log x ∈ Set.Icc wMin wMax →
      ∀ v : ℝ, |v| ≤ Real.log x ^ C → ∀ lo hi : ℝ, Hm ≤ lo → hi ≤ 2 * Hm →
        Supply.LongCoefficientBound x Hm Hn A₀ B A M (Supply.primeMinusRough x v lo hi) := by
  -- the auxiliary exponents of the vendored proof
  have hmin : 0 < min δ (1 - wMax) := lt_min hδ (by linarith)
  have hσ : 0 < min δ (1 - wMax) / 2 := half_pos hmin
  have hσδ : min δ (1 - wMax) / 2 ≤ δ := by
    have := min_le_left δ (1 - wMax)
    linarith
  have hσw : min δ (1 - wMax) / 2 ≤ 1 - wMax := by
    have := min_le_right δ (1 - wMax)
    linarith
  have hE : 0 < max C (A₀ + 1) := lt_of_lt_of_le hC (le_max_left _ _)
  have hA₀E : A₀ ≤ max C (A₀ + 1) := (by linarith : A₀ ≤ A₀ + 1).trans (le_max_right _ _)
  obtain ⟨B₂, CH, xH, hB₂, hCH, hxH, hHigh⟩ :=
    hhigh γ wMin wMax (min δ (1 - wMax) / 2) (max C (A₀ + 1)) A hγ hγw hw hwMax hσ hE hA
      (B + 1) (by linarith)
  obtain ⟨CL, xL, hCL, -, hLow⟩ :=
    hlow γ wMin wMax (max C (A₀ + 1)) δ hγ hγw hw hδ hE A₀ A B₂ hA₀ hA hB₂
  refine ⟨CL + CH, max (max xH xL) (Real.exp (max 1 κ)), (add_pos hCL hCH).le, ?_⟩
  intro x hx Hm Hn hm hprod hw₁ hw₂ v hv lo hi hlo hhi k hk hkL χ t ht
  have hxH' : xH ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxL' : xL ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx2 : (2 : ℝ) ≤ x := hxH.trans hxH'
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hLκ : max 1 κ ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hx)
    rwa [Real.log_exp] at h
  have hL1 : 1 ≤ Real.log x := (le_max_left _ _).trans hLκ
  have hκL : κ ≤ Real.log x := (le_max_right _ _).trans hLκ
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hHm : 0 < Hm := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 δ) hm
  have hLA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL0.le _
  have hLB : 0 ≤ Real.log x ^ B := Real.rpow_nonneg hL0.le _
  have hCHA : 0 ≤ CH * (Hm * Real.log x ^ (-A)) := mul_nonneg hCH.le (mul_nonneg hHm.le hLA)
  have hCLA : 0 ≤ CL * (Hm * Real.log x ^ (-A)) := mul_nonneg hCL.le (mul_nonneg hHm.le hLA)
  -- an empty interval
  rcases lt_or_ge hi lo with hlohi | hlohi
  · have hzero : Supply.twistedSum Hm (Supply.primeMinusRough x v lo hi) χ t = 0 := by
      unfold Supply.twistedSum
      refine Finset.sum_eq_zero fun m _ => ?_
      have hnot : ¬ (lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi) := fun h =>
        absurd (h.1.trans h.2) (not_le.mpr hlohi)
      rw [primeMinusRough_eq_zero hnot, zero_mul, zero_mul]
    rw [hzero, norm_zero]
    linarith
  -- the window in multiplicative form
  have hlogHm_lo : wMin * Real.log x ≤ Real.log Hm := (le_div_iff₀ hL0).mp hw₁.1
  have hlogHm_hi : Real.log Hm ≤ wMax * Real.log x := (div_le_iff₀ hL0).mp hw₁.2
  have hlog2Hm_hi : Real.log (2 * Hm) ≤ wMax * Real.log x := (div_le_iff₀ hL0).mp hw₂.2
  have hγL : γ * Real.log x < wMin * Real.log x := mul_lt_mul_of_pos_right hγw hL0
  have hwL : wMax * Real.log x < 2 * γ * Real.log x := mul_lt_mul_of_pos_right hwγ hL0
  have h1 : x ^ γ < Hm := by
    rw [Real.rpow_def_of_pos hx0, ← Real.lt_log_iff_exp_lt hHm]
    linarith
  have h2Hm : 0 < 2 * Hm := by linarith
  have h2 : 2 * Hm < x ^ (2 * γ) := by
    rw [Real.rpow_def_of_pos hx0, ← Real.log_lt_iff_lt_exp h2Hm]
    linarith
  have hHmUpper : Hm ≤ x ^ wMax := by
    rw [Real.rpow_def_of_pos hx0, ← Real.log_le_iff_le_exp hHm]
    linarith
  have hvE : |v| ≤ Real.log x ^ max C (A₀ + 1) :=
    hv.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
  rw [twistedSum_primeMinusRough_eq hx1 hγ hHm hlo hhi h1 h2 χ t]
  by_cases htLow : |t| ≤ Real.log x ^ B₂
  · -- low frequencies
    have hb := hLow x hxL' Hm hm hw₁ lo hi hlo hlohi hhi v t hvE htLow k hk hkL χ
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hHm.le, div_le_iff₀ hHm] at hb
    simp only [Real.rpow_eq_pow] at hb
    refine hb.trans ?_
    linarith
  · -- high frequencies, at the scales `(Hm, x / Hm)`
    have htHigh : Real.log x ^ B₂ ≤ |t| := le_of_lt (not_le.mp htLow)
    have hScaleM : x ^ (min δ (1 - wMax) / 2) ≤ Hm :=
      (Real.rpow_le_rpow_of_exponent_le hx1.le hσδ).trans hm
    have hScaleN : x ^ (min δ (1 - wMax) / 2) ≤ x / Hm :=
      calc x ^ (min δ (1 - wMax) / 2) ≤ x ^ (1 - wMax) :=
            Real.rpow_le_rpow_of_exponent_le hx1.le hσw
        _ = x / x ^ wMax := by rw [Real.rpow_sub hx0, Real.rpow_one]
        _ ≤ x / Hm := div_le_div_of_nonneg_left hx0.le hHm hHmUpper
    have hprodEq : Hm * (x / Hm) = x := mul_div_cancel₀ x hHm.ne'
    have hkE : (k : ℝ) ≤ Real.log x ^ max C (A₀ + 1) :=
      hkL.trans (Real.rpow_le_rpow_of_exponent_le hL1 hA₀E)
    have htUp : |t| ≤ 2 * (Hm * (x / Hm)) * Real.log x ^ (B + 1) := by
      rw [hprodEq]
      calc |t| ≤ 2 * (Hm * Hn) * Real.log x ^ B := ht
        _ ≤ 2 * (κ * x) * Real.log x ^ B :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod zero_le_two) hLB
        _ ≤ 2 * (Real.log x * x) * Real.log x ^ B :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hκL hx0.le) zero_le_two) hLB
        _ = 2 * x * Real.log x ^ (B + 1) := by
            rw [Real.rpow_add_one hL0.ne']
            ring
    have hb := hHigh x hxH' Hm (x / Hm) hScaleM hScaleN (by rw [hprodEq]; linarith)
      (by rw [hprodEq]; linarith) hw₁ hw₂ k hk hkE χ v t htHigh htUp hvE lo hi hlo hlohi hhi
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hHm.le, div_le_iff₀ hHm] at hb
    simp only [Real.rpow_eq_pow] at hb
    refine hb.trans ?_
    linarith

/-! ### The covering by windows -/

/-- **The windows cover the scales.** For large `x` and scales with `TypeIIScales δ κ x Hm Hn`,
both `log H_m / log x` and `log (2H_m) / log x` lie in one of the windows
`[a_j, a_j + δ/4]`, `a_j = δ/2 + j δ/8`, with `j ≤ 8/δ` and `a_j + δ/4 < 1`. -/
theorem exists_window {δ κ : ℝ} (hδ : 0 < δ) (hκ : 1 ≤ κ) :
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∀ Hm Hn : ℝ, Supply.TypeIIScales δ κ x Hm Hn →
      ∃ j : ℕ, j ≤ ⌊8 / δ⌋₊ ∧ δ / 2 + j * (δ / 8) + δ / 4 < 1 ∧
        Real.log Hm / Real.log x ∈
          Set.Icc (δ / 2 + j * (δ / 8)) (δ / 2 + j * (δ / 8) + δ / 4) ∧
        Real.log (2 * Hm) / Real.log x ∈
          Set.Icc (δ / 2 + j * (δ / 8)) (δ / 2 + j * (δ / 8) + δ / 4) := by
  have h8 : 0 < δ / 8 := by positivity
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos hκ
  refine ⟨max 2 (Real.exp (Real.log (2 * κ) / (δ / 8))), fun x hx Hm Hn hs => ?_⟩
  have hx2 : (2 : ℝ) ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLκ : Real.log (2 * κ) ≤ δ / 8 * Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hx)
    rw [Real.log_exp] at h
    exact (div_le_iff₀' h8).mp h
  have hlog2 : Real.log 2 ≤ Real.log (2 * κ) := Real.log_le_log zero_lt_two (by linarith)
  have hlogκ : Real.log κ ≤ Real.log (2 * κ) := Real.log_le_log hκ0 (by linarith)
  have hpow : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
  have hHm : 0 < Hm := hpow.trans_le hs.le_left
  have hHn : 0 < Hn := hpow.trans_le hs.le_right
  have hloHm : δ * Real.log x ≤ Real.log Hm := by
    have h := Real.log_le_log hpow hs.le_left
    rwa [Real.log_rpow hx0] at h
  have hloHn : δ * Real.log x ≤ Real.log Hn := by
    have h := Real.log_le_log hpow hs.le_right
    rwa [Real.log_rpow hx0] at h
  have hsum : Real.log Hm + Real.log Hn ≤ Real.log κ + Real.log x := by
    rw [← Real.log_mul hHm.ne' hHn.ne', ← Real.log_mul hκ0.ne' hx0.ne']
    exact Real.log_le_log (mul_pos hHm hHn) hs.upper
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = Real.log Hm / Real.log x := ⟨_, rfl⟩
  obtain ⟨s, hs2⟩ : ∃ s : ℝ, s = Real.log 2 / Real.log x := ⟨_, rfl⟩
  have hwlo : δ ≤ w := by
    rw [hw, le_div_iff₀ hL0]
    exact hloHm
  have hwup : w ≤ 1 - δ + δ / 8 := by
    rw [hw, div_le_iff₀ hL0]
    linarith
  have hs0 : 0 ≤ s := by
    rw [hs2]
    exact div_nonneg (Real.log_nonneg one_le_two) hL0.le
  have hs8 : s ≤ δ / 8 := by
    rw [hs2, div_le_iff₀ hL0]
    linarith
  have hw' : Real.log (2 * Hm) / Real.log x = w + s := by
    rw [Real.log_mul two_ne_zero hHm.ne', hw, hs2]
    ring
  -- the index of the window
  have hq0 : 0 ≤ (w - δ / 2) / (δ / 8) := div_nonneg (by linarith) h8.le
  have hj1 : ((⌊(w - δ / 2) / (δ / 8)⌋₊ : ℕ) : ℝ) * (δ / 8) ≤ w - δ / 2 :=
    (le_div_iff₀ h8).mp (Nat.floor_le hq0)
  have hj2 : w - δ / 2 < (((⌊(w - δ / 2) / (δ / 8)⌋₊ : ℕ) : ℝ) + 1) * (δ / 8) :=
    (div_lt_iff₀ h8).mp (Nat.lt_floor_add_one _)
  refine ⟨⌊(w - δ / 2) / (δ / 8)⌋₊, Nat.le_floor ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hδ]
    linarith
  · linarith
  · rw [← hw]
    exact ⟨by linarith, by linarith⟩
  · rw [hw']
    exact ⟨by linarith, by linarith⟩

end Supply.LongCoefficientBridge

open Supply.LongCoefficientBridge in
/-- **[P] Lemma 5.2** (the long coefficient, `[P-05:0044–0055]`) follows from the vendored theorems
`ArtinPrimitiveRoots.TypeII.Rough.low_frequency` and
`ArtinPrimitiveRoots.TypeII.Rough.high_frequency`. -/
theorem primeMinusRoughLongCoefficient_of_vendored (hlow : VendoredRoughLowFrequency)
    (hhigh : VendoredRoughHighFrequency) : Supply.PrimeMinusRoughLongCoefficient := by
  intro δ C κ hδ hC hκ A₀ B A hA₀ hB hA
  -- the bound on each window
  have hwin : ∀ j : ℕ, ∃ M x₀ : ℝ, 0 ≤ M ∧ ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ, x ^ δ ≤ Hm →
      Hm * Hn ≤ κ * x → δ / 2 + j * (δ / 8) + δ / 4 < 1 →
      Real.log Hm / Real.log x ∈
        Set.Icc (δ / 2 + j * (δ / 8)) (δ / 2 + j * (δ / 8) + δ / 4) →
      Real.log (2 * Hm) / Real.log x ∈
        Set.Icc (δ / 2 + j * (δ / 8)) (δ / 2 + j * (δ / 8) + δ / 4) →
      ∀ v : ℝ, |v| ≤ Real.log x ^ C → ∀ lo hi : ℝ, Hm ≤ lo → hi ≤ 2 * Hm →
        Supply.LongCoefficientBound x Hm Hn A₀ B A M (Supply.primeMinusRough x v lo hi) := by
    intro j
    have hj0 : (0 : ℝ) ≤ (j : ℝ) * (δ / 8) := mul_nonneg (Nat.cast_nonneg j) (by positivity)
    by_cases hj : δ / 2 + j * (δ / 8) + δ / 4 < 1
    · obtain ⟨M, x₀, hM, h⟩ := longCoefficient_window hlow hhigh (κ := κ)
        (γ := δ / 2 + j * (δ / 8) - δ / 16) (wMin := δ / 2 + j * (δ / 8))
        (wMax := δ / 2 + j * (δ / 8) + δ / 4) (by linarith) (by linarith) (by linarith) hj
        (by linarith) hδ hC hA₀ hB hA
      exact ⟨M, x₀, hM, fun x hx Hm Hn h1 h2 _ => h x hx Hm Hn h1 h2⟩
    · exact ⟨0, 0, le_rfl, fun x _ Hm Hn _ _ h => absurd h hj⟩
  choose Mj xj hMj hbound using hwin
  obtain ⟨x₁, hx₁⟩ := exists_window hδ hκ
  refine ⟨∑ j ∈ Finset.range (⌊8 / δ⌋₊ + 1), Mj j,
    max (max x₁ 1) (∑ j ∈ Finset.range (⌊8 / δ⌋₊ + 1), |xj j|),
    fun x hx Hm Hn hs v hv lo hi hlo hhi k hk hkL χ t ht => ?_⟩
  have hxx₁ : x₁ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx1 : (1 : ℝ) ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  obtain ⟨j, hjJ, hlt, hw, hw'⟩ := hx₁ x hxx₁ Hm Hn hs
  have hjmem : j ∈ Finset.range (⌊8 / δ⌋₊ + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hjJ)
  have hxj : xj j ≤ x :=
    (le_abs_self _).trans
      ((Finset.single_le_sum (f := fun i => |xj i|) (fun i _ => abs_nonneg (xj i)) hjmem).trans
        ((le_max_right _ _).trans hx))
  have hMle : Mj j ≤ ∑ i ∈ Finset.range (⌊8 / δ⌋₊ + 1), Mj i :=
    Finset.single_le_sum (f := Mj) (fun i _ => hMj i) hjmem
  have hHm : 0 ≤ Hm := (Real.rpow_nonneg (zero_le_one.trans hx1) δ).trans hs.le_left
  refine (hbound j x hxj Hm Hn hs.le_left hs.upper hlt hw hw' v hv lo hi hlo hhi k hk hkL χ t
    ht).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMle hHm)
    (Real.rpow_nonneg (Real.log_nonneg hx1) _)

end SimultaneousPrimitiveRoots.Unconditional
