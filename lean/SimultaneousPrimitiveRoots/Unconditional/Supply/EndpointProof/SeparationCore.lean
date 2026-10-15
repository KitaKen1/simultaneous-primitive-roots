module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SeparationBoxes
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.FourierCutoff
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ScaleFacts

/-!
# The separation of an extracted part: from the uncut polynomial to the endpoint polynomial

`[P-06:0723–0737]`: "Fourier-separate the smooth product cutoff in logarithmic size. … This
applies also to the uncut product of all factors, so Dirichlet mean squares uniformly on
translated time intervals justify discarding the Fourier tails with arbitrary log saving. Retain
only shifts of fixed log-power size. Enlarge the low-time exponent `B'` beyond these shifts and
any later prime thresholds. … At the remaining times all retained shifts of `t` are comparable in
magnitude to `t`."

`separation_core` is the part of the two links `tupleSeparation`, `constantSeparation` that does
not depend on the arithmetic of the extracted part. An extracted part is
`𝒰(w) = ψ₁(w/Y) w^{iσ} v X(w)`; let `F` be an *uncut* coefficient with `X = F` wherever
`ψ₁(w/Y) ≠ 0`, supported on `a₁Y/4 ≤ w ≤ 4a₂Y`, with `|F| ≤ L^{CF}`. If the uncut polynomial
`Q(t) = Y⁻¹ ∑_w F(w) e(hw/k) w^{it}` has energy `≤ M₀ L^{-A₀}` on the intervals of
`{L^{B₀} ≤ |t| ≤ 2T₀}`, then the endpoint polynomial of `𝒰` has energy `≤ M L^{-A}` on the
intervals of `{L^{B'} ≤ |τ| ≤ T₀}`.

With `N = ⌈L^E⌉`, `E = (A+1)/2 + |Dψ 1| + |Dψ 2| + |CF|`, and the expansion `cutoff_fourier`
(`ψ₁(y) = ∑_{|n| ≤ N} c_n y^{iκn} + O(K (L^{Dψ 1} + L^{Dψ 2})/N)` on `a₁/4 ≤ y ≤ 4a₂`):

* `energy_truncated`: the retained part is `∑_{|n| ≤ N} v c_n Y^{-iκn} Q(τ + σ + κn)`; the shifts
  are at most `S = L^{Cσ} + κN`, and `L^{B₀} + S ≤ L^{B'}`, `T₀ + S ≤ 2T₀` (`shift_numeric`); its
  energy is at most `((2N+1) v₋⁻¹ L^{Dψ 0})² M₀ L^{-A₀}`, which is `≤ 25 v₋⁻² |M₀| L^{-A}` for
  `A₀ = A + 2E + 2|Dψ 0|` (`trunc_numeric`).
* `energy_tail`: the tail is a Dirichlet polynomial of length `≤ 4a₂Y` with coefficients
  `≤ δ v₋⁻¹ L^{CF}`; the mean-value theorem at the original times, `T₀ ≤ Y` and
  `4W(1 + log W) ≤ C_s Y L` (`scaleFacts` with `a₂` replaced by `4a₂`) give
  `≤ (1 + |C_s|) 4a₂ (2K v₋⁻¹)² L^{-A}` (`tail_numeric`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology ContDiff

noncomputable section

/-! ### The two parts -/

/-- **The retained twists**: the energy of the truncated part on `{lo + S ≤ |τ| ≤ hi - S}` from
the energy of the uncut polynomial on `{lo ≤ |t| ≤ hi}`, when all shifts `σ + κn`, `|n| ≤ N`, are
at most `S`. -/
theorem energy_truncated {F : ℕ → ℂ} {W : ℕ} (hF : ∀ w, F w ≠ 0 → w ∈ Finset.Icc 1 W) {Y : ℝ}
    (hY : 0 < Y) (h : ℤ) (k : ℕ) {σ κ S vm Bc lo hi bd : ℝ} (v : ℝ) (cf : ℤ → ℂ) (N : ℕ)
    (hκ : 0 ≤ κ) (hS : |σ| + κ * N ≤ S) (hv : |v| ≤ vm) (hcf : ∀ n, ‖cf n‖ ≤ Bc) (hbd : 0 ≤ bd)
    (hQ : HighEnergyLe (endpointPolynomial F Y h k) lo hi bd) :
    HighEnergyLe (endpointPolynomial (fun w : ℕ => truncCutoff cf κ N ((w : ℝ) / Y) *
        (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (v : ℂ) * F w) Y h k)
      (lo + S) (hi - S) (((2 * (N : ℝ) + 1) * (vm * Bc)) ^ 2 * bd) := by
  have hvm0 : 0 ≤ vm := (abs_nonneg v).trans hv
  have heq : endpointPolynomial (fun w : ℕ => truncCutoff cf κ N ((w : ℝ) / Y) *
        (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (v : ℂ) * F w) Y h k =
      fun τ : ℝ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        ((v : ℂ) * cf n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I)) *
          endpointPolynomial F Y h k (τ + (σ + κ * n)) :=
    funext fun τ => endpointPolynomial_truncated hF hY h k σ κ (v : ℂ) cf N τ
  have hcard : ((Finset.Icc (-(N : ℤ)) N).card : ℝ) = 2 * (N : ℝ) + 1 := by
    have h1 : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
      rw [Int.card_Icc]
      omega
    rw [h1]
    push_cast
    ring
  have hterm : ∀ n ∈ Finset.Icc (-(N : ℤ)) N,
      ‖(v : ℂ) * cf n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I)‖ ≤
        vm * Bc := by
    intro n _
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul hv (hcf n) (norm_nonneg _) hvm0
  have hZ : ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      ‖(v : ℂ) * cf n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I)‖ ≤
        (2 * (N : ℝ) + 1) * (vm * Bc) :=
    calc ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          ‖(v : ℂ) * cf n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I)‖
        ≤ ∑ _n ∈ Finset.Icc (-(N : ℤ)) N, vm * Bc := Finset.sum_le_sum hterm
      _ = (2 * (N : ℝ) + 1) * (vm * Bc) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hmain : HighEnergyLe (fun τ : ℝ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        ((v : ℂ) * cf n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I)) *
          endpointPolynomial F Y h k (τ + (σ + κ * n)))
      (lo + S) (hi - S) (((2 * (N : ℝ) + 1) * (vm * Bc)) ^ 2 * bd) := by
    refine HighEnergyLe.sum_weighted (Finset.Icc (-(N : ℤ)) N)
      (fun n => (v : ℂ) * cf n * Complex.exp (((-(κ * n * Real.log Y) : ℝ) : ℂ) * Complex.I))
      (fun n => fun t : ℝ => endpointPolynomial F Y h k (t + (σ + κ * n))) ?_ ?_ hbd hZ
    · intro n _
      exact (continuous_endpointPolynomial_Icc hF Y h k).comp
        (continuous_id.add continuous_const)
    · intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
      have hnabs : |(n : ℝ)| ≤ (N : ℝ) := by
        rw [abs_le]
        constructor
        · exact_mod_cast hn1
        · exact_mod_cast hn2
      have hs : |σ + κ * (n : ℝ)| ≤ S := by
        have h1 : |σ + κ * (n : ℝ)| ≤ |σ| + |κ * (n : ℝ)| := abs_add_le _ _
        have h2 : |κ * (n : ℝ)| = κ * |(n : ℝ)| := by rw [abs_mul, abs_of_nonneg hκ]
        have h3 : κ * |(n : ℝ)| ≤ κ * (N : ℝ) := mul_le_mul_of_nonneg_left hnabs hκ
        linarith
      exact hQ.shift hs
  rw [heq]
  exact hmain

/-- **The Fourier tail**: the mean-value theorem for the polynomial of the remainder `r` of the
cutoff, `|r| ≤ δ` on the support of `F`. -/
theorem energy_tail {F : ℕ → ℂ} {W : ℕ} (hF : ∀ w, F w ≠ 0 → w ∈ Finset.Icc 1 W) (Y : ℝ) (h : ℤ)
    (k : ℕ) (σ v : ℝ) (r : ℕ → ℂ) {δ vm Fm : ℝ} (hr : ∀ w, F w ≠ 0 → ‖r w‖ ≤ δ) (hδ : 0 ≤ δ)
    (hv : |v| ≤ vm) (hFm : ∀ w, ‖F w‖ ≤ Fm) {a b : ℝ} (hab : a ≤ b) :
    ∫ τ in a..b, ‖endpointPolynomial (fun w : ℕ => r w * (w : ℂ) ^ ((σ : ℂ) * Complex.I) *
        (v : ℂ) * F w) Y h k τ‖ ^ 2 ≤
      (Y ^ 2)⁻¹ * (((b - a) + 4 * (W : ℝ) * (1 + Real.log (W : ℝ))) *
        ((W : ℝ) * (δ * vm * Fm) ^ 2)) := by
  have hvm0 : 0 ≤ vm := (abs_nonneg v).trans hv
  have hsupp : ∀ w : ℕ, (fun w : ℕ => r w * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (v : ℂ) * F w) w ≠ 0 →
      w ∈ Finset.Icc 1 W := by
    intro w hw
    refine hF w fun h0 => hw ?_
    show r w * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (v : ℂ) * F w = 0
    rw [h0, mul_zero]
  have h1 := endpointPolynomial_energy_le hsupp Y h k hab
  have hterm : ∀ w ∈ Finset.Icc 1 W,
      ‖r w * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (v : ℂ) * F w‖ ^ 2 ≤ (δ * vm * Fm) ^ 2 := by
    intro w hw
    have hw1 : 0 < w := by
      have h2 := (Finset.mem_Icc.mp hw).1
      omega
    by_cases hF0 : F w = 0
    · rw [hF0, mul_zero, norm_zero, zero_pow two_ne_zero]
      exact sq_nonneg _
    · refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [norm_mul, norm_mul, norm_mul, norm_natCast_cpow_mul_I hw1, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul (hr w hF0) hv (abs_nonneg _) hδ) (hFm w) (norm_nonneg _)
        (mul_nonneg hδ hvm0)
  have hsum : ∑ w ∈ Finset.Icc 1 W,
      ‖r w * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (v : ℂ) * F w‖ ^ 2 ≤
        (W : ℝ) * (δ * vm * Fm) ^ 2 :=
    calc ∑ w ∈ Finset.Icc 1 W, ‖r w * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (v : ℂ) * F w‖ ^ 2
        ≤ ∑ _w ∈ Finset.Icc 1 W, (δ * vm * Fm) ^ 2 := Finset.sum_le_sum hterm
      _ = (W : ℝ) * (δ * vm * Fm) ^ 2 := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hlen0 : 0 ≤ (b - a) + 4 * (W : ℝ) * (1 + Real.log (W : ℝ)) := by
    have h3 : 0 ≤ Real.log (W : ℝ) := Real.log_natCast_nonneg W
    have h4 : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg W
    have h5 : 0 ≤ 4 * (W : ℝ) * (1 + Real.log (W : ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) h4) (by linarith)
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hlen0)
    (inv_nonneg.mpr (sq_nonneg _)))

/-! ### The powers of `L` -/

/-- The retained part: `((2N+1) v L^{d₀})² · M' L^{-(A + 2E + 2|d₀|)} ≤ 25 v² M' L^{-A}` for
`N ≤ 2 L^E`. -/
theorem trunc_numeric {L E d0 A vm M' : ℝ} {N : ℕ} (hL : 1 ≤ L) (hE : 0 ≤ E) (hvm : 0 ≤ vm)
    (hM' : 0 ≤ M') (hN : (N : ℝ) ≤ 2 * L ^ E) :
    ((2 * (N : ℝ) + 1) * (vm * L ^ d0)) ^ 2 * (M' * L ^ (-(A + 2 * E + 2 * |d0|))) ≤
      25 * vm ^ 2 * M' * L ^ (-A) := by
  have hL0 : 0 < L := by linarith
  have hLE1 : 1 ≤ L ^ E := Real.one_le_rpow hL hE
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : 2 * (N : ℝ) + 1 ≤ 5 * L ^ E := by linarith
  have h2 : L ^ d0 ≤ L ^ |d0| := Real.rpow_le_rpow_of_exponent_le hL (le_abs_self d0)
  have hd0 : 0 ≤ L ^ d0 := Real.rpow_nonneg hL0.le _
  have h3 : (2 * (N : ℝ) + 1) * (vm * L ^ d0) ≤ 5 * L ^ E * (vm * L ^ |d0|) :=
    mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hvm) (mul_nonneg hvm hd0) (by linarith)
  have h0 : 0 ≤ (2 * (N : ℝ) + 1) * (vm * L ^ d0) :=
    mul_nonneg (by linarith) (mul_nonneg hvm hd0)
  have h4 : ((2 * (N : ℝ) + 1) * (vm * L ^ d0)) ^ 2 ≤ (5 * L ^ E * (vm * L ^ |d0|)) ^ 2 :=
    pow_le_pow_left₀ h0 h3 2
  have hr0 : 0 ≤ M' * L ^ (-(A + 2 * E + 2 * |d0|)) :=
    mul_nonneg hM' (Real.rpow_nonneg hL0.le _)
  have e1 : (L ^ E) ^ 2 * (L ^ |d0|) ^ 2 * L ^ (-(A + 2 * E + 2 * |d0|)) = L ^ (-A) := by
    rw [pow_two, pow_two, ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
      ← Real.rpow_add hL0]
    congr 1
    ring
  calc ((2 * (N : ℝ) + 1) * (vm * L ^ d0)) ^ 2 * (M' * L ^ (-(A + 2 * E + 2 * |d0|)))
      ≤ (5 * L ^ E * (vm * L ^ |d0|)) ^ 2 * (M' * L ^ (-(A + 2 * E + 2 * |d0|))) :=
        mul_le_mul_of_nonneg_right h4 hr0
    _ = 25 * vm ^ 2 * M' *
          ((L ^ E) ^ 2 * (L ^ |d0|) ^ 2 * L ^ (-(A + 2 * E + 2 * |d0|))) := by ring
    _ = 25 * vm ^ 2 * M' * L ^ (-A) := by rw [e1]

/-- The retained shifts are below the enlarged low-time exponent:
`L^{B₀} + L^{Cσ} + κN ≤ L^{m+1}` for `m ≥ B₀, Cσ, E`, `N ≤ 2L^E`, `L ≥ 2 + 2κ`. -/
theorem shift_numeric {L B₀ Cσ E κ m : ℝ} {N : ℕ} (hL1 : 1 ≤ L) (hκ : 0 ≤ κ)
    (hLκ : 2 + 2 * κ ≤ L) (hm1 : B₀ ≤ m) (hm2 : Cσ ≤ m) (hm3 : E ≤ m)
    (hN : (N : ℝ) ≤ 2 * L ^ E) : L ^ B₀ + (L ^ Cσ + κ * N) ≤ L ^ (m + 1) := by
  have hL0 : 0 < L := by linarith
  have hm0 : 0 ≤ L ^ m := Real.rpow_nonneg hL0.le _
  have h1 : L ^ B₀ ≤ L ^ m := Real.rpow_le_rpow_of_exponent_le hL1 hm1
  have h2 : L ^ Cσ ≤ L ^ m := Real.rpow_le_rpow_of_exponent_le hL1 hm2
  have h3 : L ^ E ≤ L ^ m := Real.rpow_le_rpow_of_exponent_le hL1 hm3
  have h4 : κ * (N : ℝ) ≤ κ * (2 * L ^ m) :=
    mul_le_mul_of_nonneg_left (hN.trans (by linarith)) hκ
  have h5 : L ^ (m + 1) = L ^ m * L := by rw [Real.rpow_add hL0, Real.rpow_one]
  have h6 : (2 + 2 * κ) * L ^ m ≤ L * L ^ m := mul_le_mul_of_nonneg_right hLκ hm0
  rw [h5]
  linarith

/-- The tail: with `N ≥ L^E`, `E = (A+1)/2 + |d₁| + |d₂| + |CF|` and
`δ = K (L^{d₁} + L^{d₂})/N`, the bound of the mean-value theorem is
`≤ (1 + |C_s|) 4a₂ (2Kv)² L^{-A}`. -/
theorem tail_numeric {L E A d1 d2 CF K vm δ a₂ Cs Y ba : ℝ} {N W : ℕ} (hL : 1 ≤ L)
    (hE : E = (A + 1) / 2 + |d1| + |d2| + |CF|) (hK : 0 ≤ K) (hvm : 0 ≤ vm) (ha₂ : 0 ≤ a₂)
    (hY : 0 < Y) (hN : L ^ E ≤ (N : ℝ)) (hδ : δ = K * (L ^ d1 + L ^ d2) / N)
    (hba : ba ≤ Y) (hW : (W : ℝ) ≤ 4 * a₂ * Y)
    (hlen : 4 * (W : ℝ) * (1 + Real.log (W : ℝ)) ≤ Cs * Y * L) :
    (Y ^ 2)⁻¹ * ((ba + 4 * (W : ℝ) * (1 + Real.log (W : ℝ))) *
        ((W : ℝ) * (δ * vm * L ^ CF) ^ 2)) ≤
      (1 + |Cs|) * (4 * a₂) * (2 * K * vm) ^ 2 * L ^ (-A) := by
  have hL0 : 0 < L := by linarith
  have hLE0 : 0 < L ^ E := Real.rpow_pos_of_pos hL0 _
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hLE0 hN
  have hW0 : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg W
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = L ^ (|d1| + |d2|) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = L ^ (-((A + 1) / 2)) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact Real.rpow_nonneg hL0.le _
  have hd1 : L ^ d1 ≤ q := by
    rw [hq]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith [le_abs_self d1, abs_nonneg d2])
  have hd2 : L ^ d2 ≤ q := by
    rw [hq]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith [le_abs_self d2, abs_nonneg d1])
  have hCF : L ^ CF ≤ L ^ |CF| := Real.rpow_le_rpow_of_exponent_le hL (le_abs_self CF)
  have hCF0 : 0 ≤ L ^ CF := Real.rpow_nonneg hL0.le _
  have hqr : q * L ^ |CF| = r * L ^ E := by
    rw [hq, hr, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    rw [hE]
    ring
  have hsum0 : 0 ≤ L ^ d1 + L ^ d2 :=
    add_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact div_nonneg (mul_nonneg hK hsum0) hN0.le
  have hδle : δ * L ^ E ≤ 2 * K * q := by
    have h1 : δ * (N : ℝ) = K * (L ^ d1 + L ^ d2) := by
      rw [hδ]
      exact div_mul_cancel₀ _ hN0.ne'
    have h2 : δ * L ^ E ≤ δ * (N : ℝ) := mul_le_mul_of_nonneg_left hN hδ0
    have h3 : K * (L ^ d1 + L ^ d2) ≤ K * (2 * q) :=
      mul_le_mul_of_nonneg_left (by linarith) hK
    linarith
  have hg0 : 0 ≤ δ * vm * L ^ CF := mul_nonneg (mul_nonneg hδ0 hvm) hCF0
  have hg : δ * vm * L ^ CF ≤ 2 * K * vm * r := by
    have h1 : δ * vm * L ^ CF * L ^ E ≤ 2 * K * vm * r * L ^ E :=
      calc δ * vm * L ^ CF * L ^ E = (δ * L ^ E) * (vm * L ^ CF) := by ring
        _ ≤ (2 * K * q) * (vm * L ^ |CF|) :=
            mul_le_mul hδle (mul_le_mul_of_nonneg_left hCF hvm) (mul_nonneg hvm hCF0)
              (mul_nonneg (mul_nonneg zero_le_two hK) hq0)
        _ = 2 * K * vm * (q * L ^ |CF|) := by ring
        _ = 2 * K * vm * r * L ^ E := by
            rw [hqr]
            ring
    exact le_of_mul_le_mul_right h1 hLE0
  have hg2 : (δ * vm * L ^ CF) ^ 2 ≤ (2 * K * vm) ^ 2 * r ^ 2 := by
    have h1 := pow_le_pow_left₀ hg0 hg 2
    rwa [mul_pow (2 * K * vm) r 2] at h1
  have hLr : L * r ^ 2 = L ^ (-A) := by
    have e : (-A : ℝ) = 1 + (-((A + 1) / 2) + -((A + 1) / 2)) := by ring
    rw [hr, e, Real.rpow_add hL0, Real.rpow_one, Real.rpow_add hL0, pow_two]
  have hYL0 : 0 ≤ Y * L := mul_nonneg hY.le hL0.le
  have hlen' : ba + 4 * (W : ℝ) * (1 + Real.log (W : ℝ)) ≤ (1 + |Cs|) * (Y * L) := by
    have h1 : Y ≤ Y * L := le_mul_of_one_le_right hY.le hL
    have h2 : Cs * (Y * L) ≤ |Cs| * (Y * L) := mul_le_mul_of_nonneg_right (le_abs_self Cs) hYL0
    have e1 : Cs * Y * L = Cs * (Y * L) := by ring
    have e2 : (1 + |Cs|) * (Y * L) = Y * L + |Cs| * (Y * L) := by ring
    rw [e1] at hlen
    rw [e2]
    linarith
  have hWg : (W : ℝ) * (δ * vm * L ^ CF) ^ 2 ≤ 4 * a₂ * Y * ((2 * K * vm) ^ 2 * r ^ 2) :=
    mul_le_mul hW hg2 (sq_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) ha₂) hY.le)
  have hb0 : 0 ≤ (1 + |Cs|) * (Y * L) :=
    mul_nonneg (by linarith [abs_nonneg Cs]) hYL0
  have hprod := mul_le_mul hlen' hWg (mul_nonneg hW0 (sq_nonneg _)) hb0
  have hYY : (Y ^ 2)⁻¹ * (Y * Y) = 1 := by
    rw [← pow_two]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hY.ne')
  calc (Y ^ 2)⁻¹ * ((ba + 4 * (W : ℝ) * (1 + Real.log (W : ℝ))) *
        ((W : ℝ) * (δ * vm * L ^ CF) ^ 2))
      ≤ (Y ^ 2)⁻¹ * ((1 + |Cs|) * (Y * L) * (4 * a₂ * Y * ((2 * K * vm) ^ 2 * r ^ 2))) :=
        mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr (sq_nonneg _))
    _ = (1 + |Cs|) * (4 * a₂) * (2 * K * vm) ^ 2 * (L * r ^ 2) * ((Y ^ 2)⁻¹ * (Y * Y)) := by
        ring
    _ = (1 + |Cs|) * (4 * a₂) * (2 * K * vm) ^ 2 * L ^ (-A) := by rw [hYY, hLr, mul_one]

/-! ### The core -/

/-- **The separation of an extracted part** (`[P-06:0723–0737]`). Order of the choices: the fixed
data, the exponent `CF` of the uncut coefficient and the saving `A`; then the saving `A₀` required
from the uncut polynomial; then, for the low-time exponent `B₀` and the constant `M₀` of the uncut
polynomial, the enlarged exponent `B'`, the constant `M` and the threshold `x₀`. The bound is
uniform in the configuration, in `|v| ≤ v₋⁻¹`, in `k`, `h` and in the coefficients. -/
theorem separation_core (D : EndpointData) (CF A : ℝ) (hA : 0 < A) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ B₀ M₀ : ℝ, ∃ B' : ℝ, 0 < B' ∧ ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ {d : ℕ} (c : EndpointConfig d), c.Admissible D x → ∀ v : ℝ, |v| ≤ D.P.vlo⁻¹ →
      ∀ (k : ℕ) (h : ℤ) (F X : ℕ → ℂ),
        (∀ w, F w ≠ 0 → 1 ≤ w ∧ D.a₁ / 4 ≤ (w : ℝ) / c.Y ∧ (w : ℝ) / c.Y ≤ 4 * D.a₂) →
        (∀ w, ‖F w‖ ≤ Real.log x ^ CF) →
        (∀ w : ℕ, c.ψ₁ ((w : ℝ) / c.Y) ≠ 0 → X w = F w) →
        HighEnergyLe (endpointPolynomial F c.Y h k) (Real.log x ^ B₀) (2 * timeBound D x)
          (M₀ * Real.log x ^ (-A₀)) →
        HighEnergyLe (endpointPolynomial (fun w : ℕ => c.ψ₁ ((w : ℝ) / c.Y) *
            (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) * (v : ℂ) * X w) c.Y h k)
          (Real.log x ^ B') (timeBound D x) (M * Real.log x ^ (-A)) := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (A + 1) / 2 + |D.Dψ 1| + |D.Dψ 2| + |CF| := ⟨_, rfl⟩
  have hE0 : 0 < E := by
    have h1 := abs_nonneg (D.Dψ 1)
    have h2 := abs_nonneg (D.Dψ 2)
    have h3 := abs_nonneg CF
    rw [hE]
    linarith
  have hA₀ : 0 < A + 2 * E + 2 * |D.Dψ 0| := by
    have h1 := abs_nonneg (D.Dψ 0)
    linarith
  refine ⟨A + 2 * E + 2 * |D.Dψ 0|, hA₀, ?_⟩
  intro B₀ M₀
  have ha₂ : 0 < D.a₂ := lt_of_lt_of_le D.a₁_pos D.a₁_le_a₂
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = cutoffFreq D.a₁ D.a₂ := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκ]
    exact cutoffFreq_pos D.a₁_pos D.a₁_le_a₂
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = cutoffConst D.a₁ D.a₂ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact cutoffConst_nonneg D.a₁_pos D.a₁_le_a₂
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max (max B₀ D.Cσ) E := ⟨_, rfl⟩
  have hm1 : B₀ ≤ m := by
    rw [hm]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hm2 : D.Cσ ≤ m := by
    rw [hm]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hm3 : E ≤ m := by
    rw [hm]
    exact le_max_right _ _
  have hvlo : 0 ≤ D.P.vlo⁻¹ := inv_nonneg.mpr D.P.vlo_pos.le
  obtain ⟨Cs, xs, hCs⟩ := scaleFacts
    { D with a₂ := 4 * D.a₂, a₁_le_a₂ := by linarith [D.a₁_le_a₂, D.a₁_pos] }
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp ((eventually_log_rpow_le (m + 1)).and
    (Real.tendsto_log_atTop.eventually_ge_atTop (2 + 2 * κ)))
  refine ⟨m + 1, by linarith, 2 * (25 * D.P.vlo⁻¹ ^ 2 * |M₀|) +
    2 * ((1 + |Cs|) * (4 * D.a₂) * (2 * K * D.P.vlo⁻¹) ^ 2), max (max xs x₁) 1, ?_⟩
  intro x hx d c hc v hv k h F X hFsupp hFle hXF hQ
  have hxs : xs ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  obtain ⟨hxm, hLκ⟩ := hx₁ x (((le_max_right _ _).trans (le_max_left _ _)).trans hx)
  have hfacts : 1 < Real.log x ∧ 0 < c.Y ∧ timeBound D x ≤ c.Y ∧
      4 * (⌊4 * D.a₂ * c.Y⌋₊ : ℝ) * (1 + Real.log (⌊4 * D.a₂ * c.Y⌋₊ : ℝ)) ≤
        Cs * c.Y * Real.log x := hCs x hxs c.Y hc.scale_ge hc.scale_le
  obtain ⟨hL1', hY, hTY, hWlen⟩ := hfacts
  have hL1 : 1 ≤ Real.log x := hL1'.le
  have hL0 : 0 < Real.log x := lt_trans one_pos hL1'
  have hxT : x ≤ timeBound D x := by
    unfold timeBound
    exact le_mul_of_one_le_right hx0.le (Real.one_le_rpow hL1 (by linarith [D.C₆_pos]))
  -- the cutoff
  have hψ0 : ∀ u, ‖c.ψ₁ u‖ ≤ Real.log x ^ D.Dψ 0 := fun u => by
    have h0 := hc.cutoff_deriv 0 u
    rwa [iteratedDeriv_zero] at h0
  have hψ1 : ∀ u, ‖deriv c.ψ₁ u‖ ≤ Real.log x ^ D.Dψ 1 := fun u => by
    have h0 := hc.cutoff_deriv 1 u
    rwa [iteratedDeriv_one] at h0
  have e2 : iteratedDeriv 2 c.ψ₁ = deriv (deriv c.ψ₁) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hψ2 : ∀ u, ‖deriv (deriv c.ψ₁) u‖ ≤ Real.log x ^ D.Dψ 2 := fun u => by
    have h0 := hc.cutoff_deriv 2 u
    rwa [e2] at h0
  obtain ⟨cf, hcf0, hcfN⟩ := cutoff_fourier D.a₁_pos D.a₁_le_a₂ hc.cutoff_smooth
    hc.cutoff_support hψ0 hψ1 hψ2
  -- the truncation level
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈Real.log x ^ E⌉₊ := ⟨_, rfl⟩
  have hLE1 : 1 ≤ Real.log x ^ E := Real.one_le_rpow hL1 hE0.le
  have hNge : Real.log x ^ E ≤ (N : ℝ) := by
    rw [hNdef]
    exact Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 2 * Real.log x ^ E := by
    have h1 : (N : ℝ) < Real.log x ^ E + 1 := by
      rw [hNdef]
      exact Nat.ceil_lt_add_one (by linarith)
    linarith
  have hNpos : 0 < N := Nat.cast_pos.mp (lt_of_lt_of_le (by linarith) hNge)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ,
      δ = K * (Real.log x ^ D.Dψ 1 + Real.log x ^ D.Dψ 2) / N := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact div_nonneg (mul_nonneg hK0 (add_nonneg (Real.rpow_nonneg hL0.le _)
      (Real.rpow_nonneg hL0.le _))) (Nat.cast_nonneg N)
  -- the length
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = ⌊4 * D.a₂ * c.Y⌋₊ := ⟨_, rfl⟩
  rw [← hW] at hWlen
  have hWle : (W : ℝ) ≤ 4 * D.a₂ * c.Y := by
    rw [hW]
    exact Nat.floor_le (mul_nonneg (mul_nonneg (by norm_num) ha₂.le) hY.le)
  have hFW : ∀ w, F w ≠ 0 → w ∈ Finset.Icc 1 W := by
    intro w hw
    obtain ⟨h1, -, h3⟩ := hFsupp w hw
    have h4 : (w : ℝ) ≤ 4 * D.a₂ * c.Y := (div_le_iff₀ hY).mp h3
    rw [hW]
    exact Finset.mem_Icc.mpr ⟨h1, Nat.le_floor h4⟩
  -- the two sequences
  obtain ⟨UN, hUN⟩ : ∃ UN : ℕ → ℂ, UN = fun w : ℕ => truncCutoff cf κ N ((w : ℝ) / c.Y) *
      (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) * (v : ℂ) * F w := ⟨_, rfl⟩
  obtain ⟨UT, hUT⟩ : ∃ UT : ℕ → ℂ, UT = fun w : ℕ =>
      (c.ψ₁ ((w : ℝ) / c.Y) - truncCutoff cf κ N ((w : ℝ) / c.Y)) *
        (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) * (v : ℂ) * F w := ⟨_, rfl⟩
  have hsN : ∀ w, UN w ≠ 0 → w ∈ Finset.Icc 1 W := by
    intro w hw
    refine hFW w fun h0 => hw ?_
    rw [hUN]
    show truncCutoff cf κ N ((w : ℝ) / c.Y) * (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) * (v : ℂ) *
      F w = 0
    rw [h0, mul_zero]
  have hsT : ∀ w, UT w ≠ 0 → w ∈ Finset.Icc 1 W := by
    intro w hw
    refine hFW w fun h0 => hw ?_
    rw [hUT]
    show (c.ψ₁ ((w : ℝ) / c.Y) - truncCutoff cf κ N ((w : ℝ) / c.Y)) *
      (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) * (v : ℂ) * F w = 0
    rw [h0, mul_zero]
  have hU : (fun w : ℕ => c.ψ₁ ((w : ℝ) / c.Y) * (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) *
      (v : ℂ) * X w) = fun w : ℕ => UN w + UT w := by
    funext w
    rw [hUN, hUT]
    show c.ψ₁ ((w : ℝ) / c.Y) * (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) * (v : ℂ) * X w =
      truncCutoff cf κ N ((w : ℝ) / c.Y) * (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) * (v : ℂ) * F w +
        (c.ψ₁ ((w : ℝ) / c.Y) - truncCutoff cf κ N ((w : ℝ) / c.Y)) *
          (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) * (v : ℂ) * F w
    by_cases hψw : c.ψ₁ ((w : ℝ) / c.Y) = 0
    · rw [hψw]
      ring
    · rw [hXF w hψw]
      ring
  -- the retained part
  have hbd0 : 0 ≤ |M₀| * Real.log x ^ (-(A + 2 * E + 2 * |D.Dψ 0|)) :=
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hL0.le _)
  have hQ' : HighEnergyLe (endpointPolynomial F c.Y h k) (Real.log x ^ B₀) (2 * timeBound D x)
      (|M₀| * Real.log x ^ (-(A + 2 * E + 2 * |D.Dψ 0|))) :=
    hQ.mono le_rfl le_rfl
      (mul_le_mul_of_nonneg_right (le_abs_self M₀) (Real.rpow_nonneg hL0.le _))
  have hS : |c.σ| + κ * (N : ℝ) ≤ Real.log x ^ D.Cσ + κ * (N : ℝ) := by
    have h1 := hc.twist
    linarith
  have hshift : Real.log x ^ B₀ + (Real.log x ^ D.Cσ + κ * (N : ℝ)) ≤ Real.log x ^ (m + 1) :=
    shift_numeric hL1 hκ0.le hLκ hm1 hm2 hm3 hNle
  have hST : Real.log x ^ D.Cσ + κ * (N : ℝ) ≤ timeBound D x := by
    have h1 : 0 ≤ Real.log x ^ B₀ := Real.rpow_nonneg hL0.le _
    linarith
  have hTr : HighEnergyLe (endpointPolynomial UN c.Y h k) (Real.log x ^ (m + 1))
      (timeBound D x) (25 * D.P.vlo⁻¹ ^ 2 * |M₀| * Real.log x ^ (-A)) := by
    have h1 := energy_truncated hFW hY h k v cf N hκ0.le hS hv hcf0 hbd0 hQ'
    rw [← hUN] at h1
    exact h1.mono hshift (by linarith)
      (trunc_numeric hL1 hE0.le hvlo (abs_nonneg M₀) hNle)
  -- the tail
  have happrox : ∀ w, F w ≠ 0 →
      ‖c.ψ₁ ((w : ℝ) / c.Y) - truncCutoff cf κ N ((w : ℝ) / c.Y)‖ ≤ δ := by
    intro w hw
    obtain ⟨-, h2, h3⟩ := hFsupp w hw
    have h4 := hcfN N hNpos ((w : ℝ) / c.Y) h2 h3
    rw [hδ, hK, hκ]
    exact h4
  have hlo0 : 0 ≤ Real.log x ^ (m + 1) := Real.rpow_nonneg hL0.le _
  rw [hU]
  intro a b hab hr
  have hadd := integral_normSq_endpointPolynomial_add_le hsN hsT c.Y h k hab
  have hI1 : ∫ τ in a..b, ‖endpointPolynomial UN c.Y h k τ‖ ^ 2 ≤
      25 * D.P.vlo⁻¹ ^ 2 * |M₀| * Real.log x ^ (-A) := hTr a b hab hr
  have hI2 : ∫ τ in a..b, ‖endpointPolynomial UT c.Y h k τ‖ ^ 2 ≤
      (1 + |Cs|) * (4 * D.a₂) * (2 * K * D.P.vlo⁻¹) ^ 2 * Real.log x ^ (-A) := by
    have h1 := energy_tail hFW c.Y h k c.σ v
      (fun w : ℕ => c.ψ₁ ((w : ℝ) / c.Y) - truncCutoff cf κ N ((w : ℝ) / c.Y)) happrox hδ0 hv
      hFle hab
    rw [← hUT] at h1
    have hba : b - a ≤ c.Y := (sub_le_of_highRange hlo0 hr).trans hTY
    exact h1.trans (tail_numeric hL1 hE hK0 hvlo ha₂.le hY hNge hδ hba hWle hWlen)
  calc ∫ τ in a..b, ‖endpointPolynomial (fun w : ℕ => UN w + UT w) c.Y h k τ‖ ^ 2
      ≤ 2 * (∫ τ in a..b, ‖endpointPolynomial UN c.Y h k τ‖ ^ 2) +
          2 * ∫ τ in a..b, ‖endpointPolynomial UT c.Y h k τ‖ ^ 2 := hadd
    _ ≤ 2 * (25 * D.P.vlo⁻¹ ^ 2 * |M₀| * Real.log x ^ (-A)) +
          2 * ((1 + |Cs|) * (4 * D.a₂) * (2 * K * D.P.vlo⁻¹) ^ 2 * Real.log x ^ (-A)) := by
        linarith
    _ = (2 * (25 * D.P.vlo⁻¹ ^ 2 * |M₀|) +
          2 * ((1 + |Cs|) * (4 * D.a₂) * (2 * K * D.P.vlo⁻¹) ^ 2)) * Real.log x ^ (-A) := by
        ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
