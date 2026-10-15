module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements

/-!
# The Dirichlet polynomial of a divisor model: the interchange of the divisor sum

The common part of (cor:constant-medium) and (cor:constant-high) (`[P-06:0878–0912]`): "For the
truncated model, a divisor `d'` leaves a progression modulo `k` at scale `R' = R_0 / d'`. Its
normalization in `N(t)` is `A_{d'} / d'` times normalization at `R'`. … The divisor is a unit
modulo `k`, so the original residue restriction becomes a single residue restriction at this
scale. … sum using `∑ |A_{d'}| / d' ≤ L^{C_8}`."

* `mem_natIcc_of_pos`, `natIcc_eq_empty`: the integers of `[a, b]` for `a > 0`.
* `natCast_cpow_mul_I`: `n^{it} = exp(i t log n)` for `n ≥ 1`.
* `mul_modEq_iff_natCast_eq`: for `gcd(e, k) = 1`, `e m ≡ a (k)` is the single class
  `m ≡ a e⁻¹ (k)`.
* `sum_progression_divisorSum`: the interchange
  `∑_{n ≡ a (k)} (∑_{e ∣ n} A_e) n^z = ∑_e A_e e^z ∑_{e m ≡ a (k)} m^z`.
* `norm_normPoly_divisorSum_le`: a bound `(R_0/e) β` for the progression at each divisor gives
  `|N_0(t)| ≤ β ∑_e |A_e| / e`.
* `norm_sum_natIcc_le_of_dyadic`: a sum over the integers of `[l, r] ⊆ [N, 2^J N]` from bounds on
  the subintervals of the dyads `[2^j N, 2^{j+1} N]`.
* `sum_natIcc_ite_eq_of_mem`: the progression sum in the normalization of the classical inputs
  (`exp(i t log n)`, an arbitrary finite set with the same members).
* `norm_normPoly_model_le`: the two statements reduced to a bound at dyadic scales; the range
  `R_0 ≤ n ≤ ρ R_0` is cut into `⌈ρ⌉` dyads.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### Integer ranges -/

/-- The integers of `[a, b]` for `a > 0` (no condition on `b`). -/
theorem mem_natIcc_of_pos {a b : ℝ} (ha : 0 < a) {n : ℕ} :
    n ∈ natIcc a b ↔ a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b := by
  by_cases hb : 0 ≤ b
  · exact mem_natIcc hb
  · have hb' : b < 0 := not_le.mp hb
    constructor
    · intro h
      unfold natIcc at h
      rw [Finset.mem_Icc, Nat.floor_of_nonpos hb'.le] at h
      have h1 : a ≤ ((0 : ℕ) : ℝ) := Nat.ceil_le.mp (h.1.trans h.2)
      rw [Nat.cast_zero] at h1
      exact absurd h1 (not_le.mpr ha)
    · rintro ⟨-, h2⟩
      have h3 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      exact absurd (h3.trans h2) (not_le.mpr hb')

/-- `[a, b]` contains no integer when `b < a` and `a > 0`. -/
theorem natIcc_eq_empty {a b : ℝ} (ha : 0 < a) (hba : b < a) : natIcc a b = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
  obtain ⟨h1, h2⟩ := (mem_natIcc_of_pos ha).mp hn
  exact absurd (h1.trans h2) (not_le.mpr hba)

/-! ### Phases and residue classes -/

/-- `n^{it} = exp(i t log n)` for a positive integer `n`. -/
theorem natCast_cpow_mul_I {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ ((t : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log]
  congr 1
  ring

/-- `|n^{it}| = 1` for a positive integer `n`. -/
theorem norm_natCast_cpow_mul_I {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
  have hre : ((t : ℂ) * Complex.I).re = 0 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [Complex.norm_natCast_cpow_of_pos hn, hre, Real.rpow_zero]

/-- "The divisor is a unit modulo `k`, so the original residue restriction becomes a single
residue restriction" (`[P-06:0881–0883]`). -/
theorem mul_modEq_iff_natCast_eq {k e a m : ℕ} (he : e.Coprime k) :
    e * m ≡ a [MOD k] ↔ (m : ZMod k) = (a : ZMod k) * (e : ZMod k)⁻¹ := by
  have hinv : (e : ZMod k) * (e : ZMod k)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one e he
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul]
  constructor
  · intro h
    linear_combination (e : ZMod k)⁻¹ * h - (m : ZMod k) * hinv
  · intro h
    linear_combination (e : ZMod k) * h + (a : ZMod k) * hinv

/-! ### The interchange of the divisor sum -/

/-- The divisor sum of a sequence supported on `1 ≤ e ≤ E`, as a sum over `1 ≤ e ≤ E`. -/
theorem divisorSum_eq_sum_Icc {A : ℕ → ℂ} {E : ℕ}
    (hA : ∀ e : ℕ, A e ≠ 0 → e ∈ Finset.Icc 1 E) {n : ℕ} (hn : n ≠ 0) :
    divisorSum A n = ∑ e ∈ Finset.Icc 1 E, if e ∣ n then A e else 0 := by
  unfold divisorSum
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro e he
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp he).2, hn⟩
  · intro e he hnot
    by_contra hAe
    exact hnot (Finset.mem_filter.mpr ⟨hA e hAe, (Nat.mem_divisors.mp he).1⟩)

/-- The change of variables `n = e m` on the multiples of `e` in `[R₁, R₂]`. -/
theorem sum_dvd_natIcc_eq {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) {e : ℕ} (he : 0 < e) (P : ℕ → Prop)
    [DecidablePred P] (g : ℕ → ℂ) :
    ∑ n ∈ (natIcc R₁ R₂).filter (fun n => e ∣ n ∧ P n), g n =
      ∑ m ∈ (natIcc (R₁ / e) (R₂ / e)).filter (fun m => P (e * m)), g (e * m) := by
  have he' : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.mpr he
  have hR₁e : 0 < R₁ / (e : ℝ) := div_pos hR₁ he'
  refine Finset.sum_nbij' (fun n => n / e) (fun m => e * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn1, hdvd, hP⟩ := Finset.mem_filter.mp hn
    obtain ⟨c, rfl⟩ := hdvd
    obtain ⟨h1, h2⟩ := (mem_natIcc_of_pos hR₁).mp hn1
    rw [Nat.cast_mul] at h1 h2
    have hc : e * c / e = c := Nat.mul_div_cancel_left c he
    show e * c / e ∈ _
    rw [hc]
    refine Finset.mem_filter.mpr ⟨(mem_natIcc_of_pos hR₁e).mpr ⟨?_, ?_⟩, hP⟩
    · rw [div_le_iff₀ he']
      linarith
    · rw [le_div_iff₀ he']
      linarith
  · intro m hm
    obtain ⟨hm1, hP⟩ := Finset.mem_filter.mp hm
    obtain ⟨h1, h2⟩ := (mem_natIcc_of_pos hR₁e).mp hm1
    rw [div_le_iff₀ he'] at h1
    rw [le_div_iff₀ he'] at h2
    show e * m ∈ _
    refine Finset.mem_filter.mpr ⟨(mem_natIcc_of_pos hR₁).mpr ⟨?_, ?_⟩, dvd_mul_right e m, hP⟩
    · rw [Nat.cast_mul]
      linarith
    · rw [Nat.cast_mul]
      linarith
  · intro n hn
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2.1
  · intro m _
    exact Nat.mul_div_cancel_left m he
  · intro n hn
    show g n = g (e * (n / e))
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2.1]

/-- **The interchange of the divisor sum** (`[P-06:0878–0881]`): for coefficients supported on
`1 ≤ e ≤ E`,
`∑_{R₁ ≤ n ≤ R₂, n ≡ a (k)} (∑_{e ∣ n} A_e) n^z = ∑_e A_e e^z ∑_{R₁/e ≤ m ≤ R₂/e, e m ≡ a (k)} m^z`. -/
theorem sum_progression_divisorSum (A : ℕ → ℂ) {E : ℕ}
    (hA : ∀ e : ℕ, A e ≠ 0 → e ∈ Finset.Icc 1 E) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (a k : ℕ) (z : ℂ) :
    ∑ n ∈ natIcc R₁ R₂, (if n ≡ a [MOD k] then divisorSum A n else 0) * (n : ℂ) ^ z =
      ∑ e ∈ Finset.Icc 1 E, A e * ((e : ℂ) ^ z *
        ∑ m ∈ (natIcc (R₁ / e) (R₂ / e)).filter (fun m => e * m ≡ a [MOD k]), (m : ℂ) ^ z) := by
  -- the divisor sum as a sum over `1 ≤ e ≤ E`
  have h1 : ∀ n ∈ natIcc R₁ R₂,
      (if n ≡ a [MOD k] then divisorSum A n else 0) * (n : ℂ) ^ z =
        ∑ e ∈ Finset.Icc 1 E, if e ∣ n ∧ n ≡ a [MOD k] then A e * (n : ℂ) ^ z else 0 := by
    intro n hn
    have hn0 : n ≠ 0 := by
      intro h0
      have h := ((mem_natIcc_of_pos hR₁).mp hn).1
      rw [h0, Nat.cast_zero] at h
      exact absurd h (not_le.mpr hR₁)
    by_cases hna : n ≡ a [MOD k]
    · rw [if_pos hna, divisorSum_eq_sum_Icc hA hn0, Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases hd : e ∣ n
      · rw [if_pos hd, if_pos (⟨hd, hna⟩ : e ∣ n ∧ n ≡ a [MOD k])]
      · rw [if_neg hd, if_neg (fun h : e ∣ n ∧ n ≡ a [MOD k] => hd h.1), zero_mul]
    · rw [if_neg hna, zero_mul]
      exact (Finset.sum_eq_zero fun e _ =>
        if_neg (fun h : e ∣ n ∧ n ≡ a [MOD k] => hna h.2)).symm
  -- the change of variables `n = e m`
  have h2 : ∀ e ∈ Finset.Icc 1 E,
      ∑ n ∈ natIcc R₁ R₂, (if e ∣ n ∧ n ≡ a [MOD k] then A e * (n : ℂ) ^ z else 0) =
        A e * ((e : ℂ) ^ z *
          ∑ m ∈ (natIcc (R₁ / e) (R₂ / e)).filter (fun m => e * m ≡ a [MOD k]),
            (m : ℂ) ^ z) := by
    intro e he
    have he0 : 0 < e := by
      have h := (Finset.mem_Icc.mp he).1
      omega
    calc ∑ n ∈ natIcc R₁ R₂, (if e ∣ n ∧ n ≡ a [MOD k] then A e * (n : ℂ) ^ z else 0)
        = ∑ n ∈ (natIcc R₁ R₂).filter (fun n => e ∣ n ∧ n ≡ a [MOD k]), A e * (n : ℂ) ^ z :=
          (Finset.sum_filter _ _).symm
      _ = A e * ∑ n ∈ (natIcc R₁ R₂).filter (fun n => e ∣ n ∧ n ≡ a [MOD k]), (n : ℂ) ^ z :=
          (Finset.mul_sum _ _ _).symm
      _ = A e * ∑ m ∈ (natIcc (R₁ / e) (R₂ / e)).filter (fun m => e * m ≡ a [MOD k]),
            ((e * m : ℕ) : ℂ) ^ z :=
          congrArg (fun y : ℂ => A e * y)
            (sum_dvd_natIcc_eq hR₁ he0 (fun n => n ≡ a [MOD k]) (fun n => (n : ℂ) ^ z))
      _ = A e * ((e : ℂ) ^ z *
            ∑ m ∈ (natIcc (R₁ / e) (R₂ / e)).filter (fun m => e * m ≡ a [MOD k]),
              (m : ℂ) ^ z) := by
          refine congrArg (fun y : ℂ => A e * y) ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  calc ∑ n ∈ natIcc R₁ R₂, (if n ≡ a [MOD k] then divisorSum A n else 0) * (n : ℂ) ^ z
      = ∑ n ∈ natIcc R₁ R₂, ∑ e ∈ Finset.Icc 1 E,
          (if e ∣ n ∧ n ≡ a [MOD k] then A e * (n : ℂ) ^ z else 0) := Finset.sum_congr rfl h1
    _ = ∑ e ∈ Finset.Icc 1 E, ∑ n ∈ natIcc R₁ R₂,
          (if e ∣ n ∧ n ≡ a [MOD k] then A e * (n : ℂ) ^ z else 0) := Finset.sum_comm
    _ = ∑ e ∈ Finset.Icc 1 E, A e * ((e : ℂ) ^ z *
          ∑ m ∈ (natIcc (R₁ / e) (R₂ / e)).filter (fun m => e * m ≡ a [MOD k]),
            (m : ℂ) ^ z) := Finset.sum_congr rfl h2

/-- **The model polynomial from the progressions** (`[P-06:0878–0892]`): if the progression
`e m ≡ a (k)` at scale `R_0 / e` has phase sum at most `(R_0 / e) β` for every divisor `e` of the
model, then `|N_0(t)| ≤ β ∑_e |A_e| / e`. -/
theorem norm_normPoly_divisorSum_le (A : ℕ → ℂ) {E : ℕ}
    (hA : ∀ e : ℕ, A e ≠ 0 → e ∈ Finset.Icc 1 E) {R₀ R₁ : ℝ} (hR₀ : 0 < R₀) (a k : ℕ)
    (t β : ℝ)
    (hβ : ∀ e ∈ Finset.Icc 1 E, A e ≠ 0 →
      ‖∑ m ∈ (natIcc (R₀ / e) (R₁ / e)).filter (fun m => e * m ≡ a [MOD k]),
          (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ R₀ / (e : ℝ) * β) :
    ‖normPoly R₀ (natIcc R₀ R₁) (fun n => if n ≡ a [MOD k] then divisorSum A n else 0) t‖ ≤
      β * ∑ e ∈ Finset.Icc 1 E, ‖A e‖ / (e : ℝ) := by
  have hpoly : normPoly R₀ (natIcc R₀ R₁)
        (fun n => if n ≡ a [MOD k] then divisorSum A n else 0) t =
      (R₀ : ℂ)⁻¹ * ∑ n ∈ natIcc R₀ R₁,
        (if n ≡ a [MOD k] then divisorSum A n else 0) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  have hterm : ∀ e ∈ Finset.Icc 1 E,
      ‖A e * ((e : ℂ) ^ ((t : ℂ) * Complex.I) *
          ∑ m ∈ (natIcc (R₀ / e) (R₁ / e)).filter (fun m => e * m ≡ a [MOD k]),
            (m : ℂ) ^ ((t : ℂ) * Complex.I))‖ ≤ R₀ * (β * (‖A e‖ / (e : ℝ))) := by
    intro e he
    have he0 : 0 < e := by
      have h := (Finset.mem_Icc.mp he).1
      omega
    rw [norm_mul, norm_mul, norm_natCast_cpow_mul_I he0, one_mul]
    by_cases hAe : A e = 0
    · have h0 : ‖A e‖ = 0 := by rw [hAe, norm_zero]
      have e1 : ‖A e‖ * ‖∑ m ∈ (natIcc (R₀ / e) (R₁ / e)).filter
          (fun m => e * m ≡ a [MOD k]), (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 0 := by
        rw [h0, zero_mul]
      have e2 : R₀ * (β * (‖A e‖ / (e : ℝ))) = 0 := by rw [h0, zero_div, mul_zero, mul_zero]
      exact le_of_eq (e1.trans e2.symm)
    · calc ‖A e‖ * ‖∑ m ∈ (natIcc (R₀ / e) (R₁ / e)).filter
            (fun m => e * m ≡ a [MOD k]), (m : ℂ) ^ ((t : ℂ) * Complex.I)‖
          ≤ ‖A e‖ * (R₀ / (e : ℝ) * β) :=
            mul_le_mul_of_nonneg_left (hβ e he hAe) (norm_nonneg _)
        _ = R₀ * (β * (‖A e‖ / (e : ℝ))) := by ring
  have hinv : 0 ≤ R₀⁻¹ := inv_nonneg.mpr hR₀.le
  rw [hpoly, sum_progression_divisorSum A hA hR₀ a k ((t : ℂ) * Complex.I), norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hR₀.le]
  calc R₀⁻¹ * ‖∑ e ∈ Finset.Icc 1 E, A e * ((e : ℂ) ^ ((t : ℂ) * Complex.I) *
          ∑ m ∈ (natIcc (R₀ / e) (R₁ / e)).filter (fun m => e * m ≡ a [MOD k]),
            (m : ℂ) ^ ((t : ℂ) * Complex.I))‖
      ≤ R₀⁻¹ * ∑ e ∈ Finset.Icc 1 E, ‖A e * ((e : ℂ) ^ ((t : ℂ) * Complex.I) *
          ∑ m ∈ (natIcc (R₀ / e) (R₁ / e)).filter (fun m => e * m ≡ a [MOD k]),
            (m : ℂ) ^ ((t : ℂ) * Complex.I))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hinv
    _ ≤ R₀⁻¹ * ∑ e ∈ Finset.Icc 1 E, R₀ * (β * (‖A e‖ / (e : ℝ))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hinv
    _ = R₀⁻¹ * (R₀ * (β * ∑ e ∈ Finset.Icc 1 E, ‖A e‖ / (e : ℝ))) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = β * ∑ e ∈ Finset.Icc 1 E, ‖A e‖ / (e : ℝ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hR₀.ne', one_mul]

/-! ### Dyadic decomposition -/

/-- **Dyadic decomposition of a sum over an integer range**: if the sums of `f` over the integers
of the subintervals `[l, r]` of the dyads `[2^j N, 2^{j+1} N]`, `j ≤ J`, are at most `2^j B`, then
the sum over the integers of every `[l, r]` with `N ≤ l` and `r ≤ 2^J N` is at most
`2^{J+1} B`. -/
theorem norm_sum_natIcc_le_of_dyadic (f : ℕ → ℂ) {N B : ℝ} (hN : 0 < N) (hB : 0 ≤ B) (J : ℕ)
    (h : ∀ j : ℕ, j ≤ J → ∀ l r : ℝ, 2 ^ j * N ≤ l → l ≤ r → r ≤ 2 * (2 ^ j * N) →
      ‖∑ n ∈ natIcc l r, f n‖ ≤ 2 ^ j * B) :
    ∀ l r : ℝ, N ≤ l → r ≤ 2 ^ J * N → ‖∑ n ∈ natIcc l r, f n‖ ≤ 2 ^ (J + 1) * B := by
  induction J with
  | zero =>
    intro l r hl hr
    rw [pow_zero, one_mul] at hr
    by_cases hlr : l ≤ r
    · have h0 := h 0 le_rfl l r
      simp only [pow_zero, one_mul] at h0
      have h1 : ‖∑ n ∈ natIcc l r, f n‖ ≤ B := h0 hl hlr (by linarith)
      have h2 : B ≤ 2 ^ (0 + 1) * B := by
        have e0 : (2 : ℝ) ^ (0 + 1) * B = 2 * B := by norm_num
        rw [e0]
        linarith
      exact h1.trans h2
    · rw [natIcc_eq_empty (hN.trans_le hl) (not_le.mp hlr), Finset.sum_empty, norm_zero]
      exact mul_nonneg (pow_nonneg zero_le_two _) hB
  | succ J ih =>
    intro l r hl hr
    have ih' := ih (fun j hj => h j (Nat.le_succ_of_le hj))
    have hl0 : 0 < l := hN.trans_le hl
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = 2 ^ J * N := ⟨_, rfl⟩
    have hm0 : 0 < m := by
      rw [hm]
      exact mul_pos (pow_pos two_pos _) hN
    have hceil : 0 < ⌈m⌉₊ := Nat.ceil_pos.mpr hm0
    have hceil1 : 1 ≤ ⌈m⌉₊ := by omega
    -- the integers below `m` and the integers from `m` on
    have hsplit : ∑ n ∈ natIcc l r, f n =
        ∑ n ∈ natIcc l (min r ((⌈m⌉₊ - 1 : ℕ) : ℝ)), f n + ∑ n ∈ natIcc (max l m) r, f n := by
      rw [← Finset.sum_filter_add_sum_filter_not (natIcc l r) (fun n : ℕ => (n : ℝ) < m) f]
      congr 1
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext n
        have hiff : (n : ℝ) < m ↔ (n : ℝ) ≤ ((⌈m⌉₊ - 1 : ℕ) : ℝ) := by
          rw [← Nat.lt_ceil, Nat.cast_le]
          omega
        rw [Finset.mem_filter, mem_natIcc_of_pos hl0, mem_natIcc_of_pos hl0, le_min_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h2, hiff.mp h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1, h2⟩, hiff.mpr h3⟩
      · refine Finset.sum_congr ?_ fun _ _ => rfl
        ext n
        rw [Finset.mem_filter, mem_natIcc_of_pos hl0,
          mem_natIcc_of_pos (lt_max_of_lt_left hl0), max_le_iff, not_lt]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨⟨h1, h3⟩, h2⟩
        · rintro ⟨⟨h1, h3⟩, h2⟩
          exact ⟨⟨h1, h2⟩, h3⟩
    -- the lower part, by induction
    have h1 : ‖∑ n ∈ natIcc l (min r ((⌈m⌉₊ - 1 : ℕ) : ℝ)), f n‖ ≤ 2 ^ (J + 1) * B := by
      refine ih' l _ hl ?_
      have hc1 : (⌈m⌉₊ : ℝ) < m + 1 := Nat.ceil_lt_add_one hm0.le
      have hc2 : ((⌈m⌉₊ - 1 : ℕ) : ℝ) = (⌈m⌉₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hceil1, Nat.cast_one]
      rw [← hm]
      exact (min_le_right _ _).trans (by linarith)
    -- the upper part, a subinterval of the dyad `[m, 2m]`
    have hr' : r ≤ 2 * m := by
      rw [hm]
      calc r ≤ 2 ^ (J + 1) * N := hr
        _ = 2 * (2 ^ J * N) := by ring
    have h2 : ‖∑ n ∈ natIcc (max l m) r, f n‖ ≤ 2 ^ J * B := by
      by_cases hlr : max l m ≤ r
      · have h' := h J (Nat.le_succ J) (max l m) r
        rw [← hm] at h'
        exact h' (le_max_right _ _) hlr hr'
      · rw [natIcc_eq_empty (lt_max_of_lt_left hl0) (not_le.mp hlr), Finset.sum_empty, norm_zero]
        exact mul_nonneg (pow_nonneg zero_le_two _) hB
    have h5 : 0 ≤ (2 : ℝ) ^ J * B := mul_nonneg (pow_nonneg zero_le_two _) hB
    have e1 : (2 : ℝ) ^ (J + 1) * B = 2 * (2 ^ J * B) := by ring
    have e2 : (2 : ℝ) ^ (J + 1 + 1) * B = 4 * (2 ^ J * B) := by ring
    calc ‖∑ n ∈ natIcc l r, f n‖
        = ‖∑ n ∈ natIcc l (min r ((⌈m⌉₊ - 1 : ℕ) : ℝ)), f n +
            ∑ n ∈ natIcc (max l m) r, f n‖ := by rw [hsplit]
      _ ≤ ‖∑ n ∈ natIcc l (min r ((⌈m⌉₊ - 1 : ℕ) : ℝ)), f n‖ +
            ‖∑ n ∈ natIcc (max l m) r, f n‖ := norm_add_le _ _
      _ ≤ 2 ^ (J + 1) * B + 2 ^ J * B := add_le_add h1 h2
      _ ≤ 2 ^ (J + 1 + 1) * B := by
          rw [e1, e2]
          linarith

/-! ### The normalization of the classical inputs -/

/-- The progression sum `∑_{l ≤ n ≤ r, n ≡ a' (k)} n^{it}` in the normalization of the classical
inputs: phases `exp(i t log n)` and any finite set with the same members. -/
theorem sum_natIcc_ite_eq_of_mem (k : ℕ) (a' : ZMod k) (t : ℝ) {l r : ℝ} (hl : 0 < l)
    (T : Finset ℕ)
    (hT : ∀ n : ℕ, n ∈ T ↔ (l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r) ∧ (n : ZMod k) = a') :
    ∑ n ∈ natIcc l r, (if (n : ZMod k) = a' then (n : ℂ) ^ ((t : ℂ) * Complex.I) else 0) =
      ∑ n ∈ T, Complex.exp (Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ ?_
  · ext n
    rw [Finset.mem_filter, mem_natIcc_of_pos hl, hT n]
  · intro n hn
    have h1 : l ≤ (n : ℝ) := ((hT n).mp hn).1.1
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero] at h1
      exact absurd h1 (not_le.mpr hl)
    exact natCast_cpow_mul_I hn0 t

/-- The same with `residuePhaseSum` (`EndpointProof/ClassicalInputs.lean`). -/
theorem sum_natIcc_ite_eq_residuePhaseSum (k : ℕ) (a' : ZMod k) (t : ℝ) {l r : ℝ} (hl : 0 < l) :
    ∑ n ∈ natIcc l r, (if (n : ZMod k) = a' then (n : ℂ) ^ ((t : ℂ) * Complex.I) else 0) =
      residuePhaseSum k a' t l r := by
  unfold residuePhaseSum
  refine sum_natIcc_ite_eq_of_mem k a' t hl _ fun n => ?_
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h2), h1, h2, h3⟩

/-! ### The reduction to dyadic scales -/

/-- **The model polynomial from bounds at dyadic scales**: if for every divisor `e` of the model,
every residue class `a' (mod k)` and every `j ≤ ⌈ρ⌉`, the progression sums over the subintervals
of `[2^j R_0/e, 2^{j+1} R_0/e]` are at most `2^j (R_0/e) γ`, then
`|N_0(t)| ≤ 2^{⌈ρ⌉+1} γ ∑_e |A_e| / e` for the range `R_0 ≤ n ≤ ρ R_0`. -/
theorem norm_normPoly_model_le {R₀ ρ : ℝ} (hR₀ : 0 < R₀) {k : ℕ} (a : ℕ) (A : ℕ → ℂ) {E : ℕ}
    (hA : ∀ e : ℕ, A e ≠ 0 → e ∈ Finset.Icc 1 E ∧ e.Coprime k) (t : ℝ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hdy : ∀ e ∈ Finset.Icc 1 E, A e ≠ 0 → ∀ a' : ZMod k, ∀ j : ℕ, j ≤ ⌈ρ⌉₊ → ∀ l r : ℝ,
      2 ^ j * (R₀ / (e : ℝ)) ≤ l → l ≤ r → r ≤ 2 * (2 ^ j * (R₀ / (e : ℝ))) →
        ‖∑ n ∈ natIcc l r,
            (if (n : ZMod k) = a' then (n : ℂ) ^ ((t : ℂ) * Complex.I) else 0)‖ ≤
          2 ^ j * (R₀ / (e : ℝ) * γ)) :
    ‖normPoly R₀ (natIcc R₀ (ρ * R₀))
        (fun n => if n ≡ a [MOD k] then divisorSum A n else 0) t‖ ≤
      2 ^ (⌈ρ⌉₊ + 1) * γ * ∑ e ∈ Finset.Icc 1 E, ‖A e‖ / (e : ℝ) := by
  have hρ2 : ρ ≤ (2 : ℝ) ^ ⌈ρ⌉₊ := by
    have h1 : ρ ≤ (⌈ρ⌉₊ : ℝ) := Nat.le_ceil ρ
    have h2 : (⌈ρ⌉₊ : ℝ) ≤ (2 : ℝ) ^ ⌈ρ⌉₊ := by
      exact_mod_cast (Nat.lt_two_pow_self : ⌈ρ⌉₊ < 2 ^ ⌈ρ⌉₊).le
    exact h1.trans h2
  refine norm_normPoly_divisorSum_le A (fun e he => (hA e he).1) hR₀ a k t
    (2 ^ (⌈ρ⌉₊ + 1) * γ) fun e he hAe => ?_
  have he0 : 0 < e := by
    have h := (Finset.mem_Icc.mp he).1
    omega
  have he' : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.mpr he0
  have hN : 0 < R₀ / (e : ℝ) := div_pos hR₀ he'
  have hcop : e.Coprime k := (hA e hAe).2
  -- the single residue class
  have hclass : ∑ m ∈ (natIcc (R₀ / e) (ρ * R₀ / e)).filter (fun m => e * m ≡ a [MOD k]),
        (m : ℂ) ^ ((t : ℂ) * Complex.I) =
      ∑ m ∈ natIcc (R₀ / e) (ρ * R₀ / e),
        (if (m : ZMod k) = (a : ZMod k) * (e : ZMod k)⁻¹ then
          (m : ℂ) ^ ((t : ℂ) * Complex.I) else 0) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (Finset.filter_congr fun m _ => mul_modEq_iff_natCast_eq hcop)
      fun _ _ => rfl
  have hup : ρ * R₀ / (e : ℝ) ≤ 2 ^ ⌈ρ⌉₊ * (R₀ / (e : ℝ)) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hρ2 hN.le
  have hmain := norm_sum_natIcc_le_of_dyadic
    (fun m : ℕ => if (m : ZMod k) = (a : ZMod k) * (e : ZMod k)⁻¹ then
      (m : ℂ) ^ ((t : ℂ) * Complex.I) else 0)
    hN (mul_nonneg hN.le hγ) ⌈ρ⌉₊ (hdy e he hAe ((a : ZMod k) * (e : ZMod k)⁻¹))
    (R₀ / e) (ρ * R₀ / e) le_rfl hup
  rw [hclass]
  calc ‖∑ m ∈ natIcc (R₀ / e) (ρ * R₀ / e),
        (if (m : ZMod k) = (a : ZMod k) * (e : ZMod k)⁻¹ then
          (m : ℂ) ^ ((t : ℂ) * Complex.I) else 0)‖
      ≤ 2 ^ (⌈ρ⌉₊ + 1) * (R₀ / (e : ℝ) * γ) := hmain
    _ = R₀ / (e : ℝ) * (2 ^ (⌈ρ⌉₊ + 1) * γ) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
