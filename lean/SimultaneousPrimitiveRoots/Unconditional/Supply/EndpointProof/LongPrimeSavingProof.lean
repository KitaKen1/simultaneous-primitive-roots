module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# (cor:long-prime-saving)

`longPrimeSaving : LongPrimePolynomial → LongPrimeSaving` (`[P-06:0836–0847]`): "In the tuple term
the long-prime polynomial is, after partial summation, a normalized prime sum with a character
modulo `k` and a fixed log-power twist. … Choose fixed `0 < τ < ε` and `1 - ε < η < 1` to apply
Lemma `lem:long-prime`. For any prescribed `A_l`, it gives `|P_l(t)| ≪ L^{-A_l}`."

* `natCast_cpow_eq`: `p^{it} = p · exp((-1 + it) log p)` for `p ≥ 1`, so with
  `a_p = χ(p) p^{-1+it}` the polynomial is `N_l^{-1} ∑_{p ∈ J} p a_p`.
* Partial summation (`sum_natCast_mul_eq_sum_tails`): `p = #{1 ≤ j ≤ p}`, hence
  `∑_{p ∈ J} p a_p = ∑_{1 ≤ j ≤ ⌊2N_l⌋} ∑_{p ∈ J, p ≥ j} a_p`.
* A tail `{p ∈ J : p ≥ j}` of an interval of primes inside `[N_l, 2N_l]` is an interval of primes
  inside `[N_l, 2N_l]` (`isPrimeInterval_filter_le`), namely the primes of
  `[N_l, 2N_l] ∩ [min, max]` (`mem_primeInterval_iff`), so Lemma `lem:long-prime` bounds each tail
  sum by `C₀ L^{-A_l}`.
* There are `⌊2N_l⌋ ≤ 2N_l` tails: `|P_l(t)| ≤ 2 C₀ L^{-A_l}`.

Lemma `lem:long-prime` is used with `τ = min(ε, 1/4)` and `η = max(1 - ε, 1/2)`; the threshold
`B₀` and `x₀` are its own, and `M = 2 C₀`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-- `p^{it} = p · exp((-1 + it) log p)` for a positive integer `p`. -/
theorem natCast_cpow_eq {p : ℕ} (hp : p ≠ 0) (t : ℝ) :
    (p : ℂ) ^ ((t : ℂ) * Complex.I) =
      (p : ℂ) * Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_log (Nat.cast_nonneg p)).symm
  calc (p : ℂ) ^ ((t : ℂ) * Complex.I)
      = Complex.exp (Complex.log (p : ℂ) * ((t : ℂ) * Complex.I)) :=
        Complex.cpow_def_of_ne_zero hp0 _
    _ = Complex.exp (Complex.log (p : ℂ)) *
          Complex.exp ((-1 + Complex.I * (t : ℂ)) * Complex.log (p : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
    _ = (p : ℂ) * Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)) := by
        rw [Complex.exp_log hp0, hlog]

/-- **Partial summation** in the form `p = #{1 ≤ j ≤ p}`: for a finite set `J` of integers
`≤ M`, `∑_{p ∈ J} p a_p = ∑_{1 ≤ j ≤ M} ∑_{p ∈ J, p ≥ j} a_p`. -/
theorem sum_natCast_mul_eq_sum_tails {J : Finset ℕ} {M : ℕ} (hM : ∀ p ∈ J, p ≤ M)
    (a : ℕ → ℂ) :
    ∑ p ∈ J, (p : ℂ) * a p =
      ∑ j ∈ Finset.Icc 1 M, ∑ p ∈ J.filter (fun p => j ≤ p), a p := by
  have hcount : ∀ p ∈ J, ((Finset.Icc 1 M).filter (fun j => j ≤ p)).card = p := by
    intro p hp
    have hpM : p ≤ M := hM p hp
    have h : (Finset.Icc 1 M).filter (fun j => j ≤ p) = Finset.Icc 1 p := by
      ext j
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans hpM⟩, h2⟩
    rw [h, Nat.card_Icc, Nat.add_sub_cancel]
  calc ∑ p ∈ J, (p : ℂ) * a p
      = ∑ p ∈ J, ∑ _j ∈ (Finset.Icc 1 M).filter (fun j => j ≤ p), a p :=
        Finset.sum_congr rfl fun p hp => by
          rw [Finset.sum_const, hcount p hp, nsmul_eq_mul]
    _ = ∑ p ∈ J, ∑ j ∈ Finset.Icc 1 M, (if j ≤ p then a p else 0) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_filter (fun j => j ≤ p) (fun _ => a p)
    _ = ∑ j ∈ Finset.Icc 1 M, ∑ p ∈ J, (if j ≤ p then a p else 0) := Finset.sum_comm
    _ = ∑ j ∈ Finset.Icc 1 M, ∑ p ∈ J.filter (fun p => j ≤ p), a p :=
        Finset.sum_congr rfl fun j _ => (Finset.sum_filter (fun p => j ≤ p) a).symm

/-- A tail of an interval of primes is an interval of primes. -/
theorem isPrimeInterval_filter_le {J : Finset ℕ} (hJ : IsPrimeInterval J) (j : ℕ) :
    IsPrimeInterval (J.filter fun p => j ≤ p) := by
  refine ⟨fun p hp => hJ.1 p (Finset.mem_filter.mp hp).1, fun p₁ hp₁ p₂ hp₂ p hpp h1 h2 => ?_⟩
  obtain ⟨hp₁J, hj⟩ := Finset.mem_filter.mp hp₁
  exact Finset.mem_filter.mpr
    ⟨hJ.2 p₁ hp₁J p₂ (Finset.mem_filter.mp hp₂).1 p hpp h1 h2, hj.trans h1⟩

/-- A nonempty interval of primes inside `[N, 2N]` is the set of the primes of
`[N, 2N] ∩ [min, max]`. -/
theorem mem_primeInterval_iff {J : Finset ℕ} (hJ : IsPrimeInterval J) {N : ℝ}
    (hN : ∀ l ∈ J, N ≤ (l : ℝ) ∧ (l : ℝ) ≤ 2 * N) (hne : J.Nonempty) (p : ℕ) :
    p ∈ J ↔ p < ⌊2 * N⌋₊ + 1 ∧ (p.Prime ∧ N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N ∧
      ((J.min' hne : ℕ) : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ ((J.max' hne : ℕ) : ℝ)) := by
  constructor
  · intro hp
    have h1 := hN p hp
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h1.2), hJ.1 p hp, h1.1, h1.2,
      Nat.cast_le.mpr (Finset.min'_le J p hp), Nat.cast_le.mpr (Finset.le_max' J p hp)⟩
  · rintro ⟨-, hpp, -, -, h3, h4⟩
    exact hJ.2 _ (Finset.min'_mem J hne) _ (Finset.max'_mem J hne) p hpp
      (Nat.cast_le.mp h3) (Nat.cast_le.mp h4)

/-- **(cor:long-prime-saving)** (`[P-06:0836–0847]`), by partial summation from Lemma
`lem:long-prime`. -/
theorem longPrimeSaving : LongPrimePolynomial → LongPrimeSaving := by
  intro hLP ε C₆ Al hε hC₆ hAl
  have hτ0 : 0 < min ε (1 / 4) := lt_min hε (by norm_num)
  have hτη : min ε (1 / 4) < max (1 - ε) (1 / 2) :=
    lt_of_le_of_lt (min_le_right _ _) (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
  have hη1 : max (1 - ε) (1 / 2) < 1 := max_lt (by linarith) (by norm_num)
  obtain ⟨B₀, C₀, x₀, hB₀, hC₀, hx₀, hmain⟩ :=
    hLP (min ε (1 / 4)) (max (1 - ε) (1 / 2)) C₆ Al hτ0 hτη hη1 hC₆ hAl
  refine ⟨B₀, 2 * C₀, x₀, hB₀, fun x hx Nl hNl1 hNl2 J hJ hJN k hk hkL χ t ht1 ht2 => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hxε : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  have hNl0 : 0 < Nl := by linarith
  have hlow : x ^ min ε (1 / 4) / 2 ≤ Nl := by
    have h1 : x ^ min ε (1 / 4) ≤ x ^ ε :=
      Real.rpow_le_rpow_of_exponent_le hx1 (min_le_left _ _)
    linarith
  have hup : Nl ≤ x ^ max (1 - ε) (1 / 2) :=
    hNl2.trans (Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _))
  have hE0 : 0 ≤ C₀ * Real.log x ^ (-Al) :=
    mul_nonneg hC₀.le (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  -- Lemma `lem:long-prime` on the intervals of `[Nl, 2 Nl]`
  have hbound := hmain x hx Nl hlow hup k (Nat.succ_le_of_lt hk) hkL χ t ht1 ht2
  -- the tails of `J`
  have htail : ∀ j : ℕ, ‖∑ p ∈ J.filter (fun p => j ≤ p), χ (p : ZMod k) *
        Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))‖ ≤
      C₀ * Real.log x ^ (-Al) := by
    intro j
    have hJ' : IsPrimeInterval (J.filter fun p => j ≤ p) := isPrimeInterval_filter_le hJ j
    have hJN' : ∀ l ∈ J.filter (fun p => j ≤ p), Nl ≤ (l : ℝ) ∧ (l : ℝ) ≤ 2 * Nl :=
      fun l hl => hJN l (Finset.mem_filter.mp hl).1
    rcases (J.filter fun p => j ≤ p).eq_empty_or_nonempty with hempty | hne
    · rw [hempty, Finset.sum_empty, norm_zero]
      exact hE0
    · have h := hbound (((J.filter fun p => j ≤ p).min' hne : ℕ) : ℝ)
        (((J.filter fun p => j ≤ p).max' hne : ℕ) : ℝ)
        (hJN' _ (Finset.min'_mem _ hne)).1 (hJN' _ (Finset.max'_mem _ hne)).2
      refine le_of_eq_of_le ?_ h
      congr 1
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext p
      refine (mem_primeInterval_iff hJ' hJN' hne p).trans ?_
      rw [Finset.mem_filter, Finset.mem_range]
  -- partial summation
  have hM : ∀ p ∈ J, p ≤ ⌊2 * Nl⌋₊ := fun p hp => Nat.le_floor (hJN p hp).2
  have hlayer : ∑ p ∈ J, (p : ℂ) * (χ (p : ZMod k) *
        Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))) =
      ∑ j ∈ Finset.Icc 1 ⌊2 * Nl⌋₊, ∑ p ∈ J.filter (fun p => j ≤ p),
        χ (p : ZMod k) *
          Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)) :=
    sum_natCast_mul_eq_sum_tails hM (fun p => χ (p : ZMod k) *
      Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)))
  have hsum : ∑ n ∈ J, χ (n : ZMod k) * (n : ℂ) ^ ((t : ℂ) * Complex.I) =
      ∑ j ∈ Finset.Icc 1 ⌊2 * Nl⌋₊, ∑ p ∈ J.filter (fun p => j ≤ p),
        χ (p : ZMod k) *
          Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)) := by
    rw [← hlayer]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : p ≠ 0 := by
      intro h0
      have h1 : Nl ≤ (p : ℝ) := (hJN p hp).1
      rw [h0, Nat.cast_zero] at h1
      linarith
    rw [natCast_cpow_eq hp0 t]
    ring
  have hcount : ‖∑ j ∈ Finset.Icc 1 ⌊2 * Nl⌋₊, ∑ p ∈ J.filter (fun p => j ≤ p),
        χ (p : ZMod k) *
          Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))‖ ≤
      (⌊2 * Nl⌋₊ : ℝ) * (C₀ * Real.log x ^ (-Al)) :=
    calc ‖∑ j ∈ Finset.Icc 1 ⌊2 * Nl⌋₊, ∑ p ∈ J.filter (fun p => j ≤ p),
          χ (p : ZMod k) *
            Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))‖
        ≤ ∑ j ∈ Finset.Icc 1 ⌊2 * Nl⌋₊, ‖∑ p ∈ J.filter (fun p => j ≤ p),
          χ (p : ZMod k) *
            Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.Icc 1 ⌊2 * Nl⌋₊, C₀ * Real.log x ^ (-Al) :=
          Finset.sum_le_sum fun j _ => htail j
      _ = (⌊2 * Nl⌋₊ : ℝ) * (C₀ * Real.log x ^ (-Al)) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hfl : (⌊2 * Nl⌋₊ : ℝ) ≤ 2 * Nl := Nat.floor_le (by linarith)
  have hinv : 0 ≤ Nl⁻¹ := inv_nonneg.mpr hNl0.le
  have hnp : normPoly Nl J (fun l => χ (l : ZMod k)) t =
      (Nl : ℂ)⁻¹ * ∑ n ∈ J, χ (n : ZMod k) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  have hfin : Nl⁻¹ * (2 * Nl * (C₀ * Real.log x ^ (-Al))) = 2 * C₀ * Real.log x ^ (-Al) := by
    have h1 : Nl⁻¹ * (2 * Nl * (C₀ * Real.log x ^ (-Al))) =
        Nl⁻¹ * Nl * (2 * C₀ * Real.log x ^ (-Al)) := by ring
    rw [h1, inv_mul_cancel₀ hNl0.ne', one_mul]
  rw [hnp, hsum, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hNl0.le]
  calc Nl⁻¹ * ‖∑ j ∈ Finset.Icc 1 ⌊2 * Nl⌋₊, ∑ p ∈ J.filter (fun p => j ≤ p),
        χ (p : ZMod k) *
          Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))‖
      ≤ Nl⁻¹ * ((⌊2 * Nl⌋₊ : ℝ) * (C₀ * Real.log x ^ (-Al))) :=
        mul_le_mul_of_nonneg_left hcount hinv
    _ ≤ Nl⁻¹ * (2 * Nl * (C₀ * Real.log x ^ (-Al))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfl hE0) hinv
    _ = 2 * C₀ * Real.log x ^ (-Al) := hfin

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
