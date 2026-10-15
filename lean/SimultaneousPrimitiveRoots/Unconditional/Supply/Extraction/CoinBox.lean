module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinCRT
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.StripProof

/-!
# The coin step: equidistribution of the patterns on rough product dyads

`[P-07:0409–0431]`: "We prove the uniformity needed for this claim on full rough product dyads.
Select each `m_i` independently and uniformly among `W`-rough integers in its full dyad. For any
fixed number of distinct candidate primes, their product `Q` satisfies `log Q = O(L^{.45})`. Each
prescribed residue class modulo `Q` is relatively equidistributed among these rough integers, with
error `o(1)` uniformly in the classes, primes, and dyads."

The manuscript verifies this by a Bonferroni argument; here it is Lemma 2.5,
(eq:rough-off-sieve-progression) (`RoughCounts`, second clause, with `a = 1/2`, `A = 1`): the
product `Q` of at most six candidate primes is `≤ exp(6 L^{.45}) ≤ exp(L^{1/2})` and has no prime
factor `≤ W`.

* `roughDyad x k`: the `W`-rough integers of `[2^k, 2^{k+1}]`; `roughBox x k`: the product box of
  the dyads `k_1, …, k_j`.
* `boxEq_of_rough`: if every class modulo every rough `d ≤ exp(L^{1/2})` contains
  `V(W) 2^{k_i}/d · (1 + θ ε₀)` rough integers of the dyad `k_i`, then the patterns of at most six
  candidate primes are equidistributed on the box, with mass `∏ V(W) 2^{k_i}` and relative error
  `(1 + ε₀)^j - 1` (`abs_pattern_count_sub_le`).
* `eventually_boxEq`: for every `ε > 0` and large `x`, `BoxEq … ε` holds for all the boxes with
  `x^δ ≤ 2^{k_i} ≤ x^C`.

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

open Filter

noncomputable section

open _root_.Classical in
/-- The `W`-rough integers of the dyad `[2^k, 2^{k+1}]`. -/
def roughDyad (x : ℝ) (k : ℕ) : Finset ℕ :=
  (Finset.Icc (2 ^ k) (2 ^ (k + 1))).filter fun n => IsRough (roughCutoff x) n

/-- The product of the rough dyads `k_1, …, k_j` (`[P-07:0409–0411]`). -/
def roughBox (x : ℝ) {j : ℕ} (k : Fin j → ℕ) : Finset (Fin j → ℕ) :=
  Fintype.piFinset fun i => roughDyad x (k i)

open _root_.Classical in
theorem mem_roughDyad {x : ℝ} {k n : ℕ} :
    n ∈ roughDyad x k ↔ (2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1)) ∧ IsRough (roughCutoff x) n := by
  unfold roughDyad
  rw [Finset.mem_filter, Finset.mem_Icc]

open _root_.Classical in
theorem roughDyad_filter_modEq (x : ℝ) (k b d : ℕ) :
    (roughDyad x k).filter (fun n => n ≡ b [MOD d]) =
      (Finset.Icc (2 ^ k) (2 ^ (k + 1))).filter
        fun n => n ≡ b [MOD d] ∧ IsRough (roughCutoff x) n := by
  unfold roughDyad
  ext n
  simp only [Finset.mem_filter]
  tauto

open _root_.Classical in
/-- **The patterns on a rough product box**, from the equidistribution of the rough integers of
each dyad in the classes modulo rough `d ≤ exp(L^{1/2})`. -/
theorem boxEq_of_rough {x : ℝ} {j : ℕ} (hj : 1 ≤ j) {ε₀ ε : ℝ} (hL : 1 < Real.log x)
    (h05 : 6 ≤ Real.log x ^ (0.05 : ℝ)) (hε₀ : 0 ≤ ε₀) (hεε : (1 + ε₀) ^ j - 1 ≤ ε)
    (k : Fin j → ℕ)
    (hcount : ∀ i, ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.exp (Real.log x ^ (1 / 2 : ℝ)) →
      IsRough (roughCutoff x) d → ∀ b : ℕ,
        |(((Finset.Icc (2 ^ k i) (2 ^ (k i + 1))).filter
            fun n => n ≡ b [MOD d] ∧ IsRough (roughCutoff x) n).card : ℝ) -
          mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i / (d : ℝ)| ≤
        ε₀ * (mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i / (d : ℝ))) :
    BoxEq j (candidatePrimes x) (roughBox x k) (fun m => ∏ i, m i - 1)
      (∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i) ε := by
  intro A A' hA hA' hcard
  have hL1 : 1 ≤ Real.log x := hL.le
  have hL0 : 0 < Real.log x := by linarith
  have hprime : ∀ p ∈ candidatePrimes x, p.Prime := fun p hp =>
    (Strip.candidatePrimes_facts hL1 hp).1
  have hV : 0 < mertensProduct (roughCutoff x) := mertensProduct_pos _
  have hM0 : 0 ≤ ∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i :=
    Finset.prod_nonneg fun i _ => mul_nonneg hV.le (pow_nonneg zero_le_two _)
  by_cases hd : Disjoint A A'
  · have hD : A ∪ A' ⊆ candidatePrimes x := Finset.union_subset hA hA'
    have hDcard : (A ∪ A').card ≤ 6 := (Finset.card_union_le A A').trans hcard
    -- the modulus
    have hQpos : 0 < ∏ p ∈ A ∪ A', p :=
      Finset.prod_pos fun p hp => (hprime p (hD hp)).pos
    have hQle : ((∏ p ∈ A ∪ A', p : ℕ) : ℝ) ≤ Real.exp (Real.log x ^ (1 / 2 : ℝ)) := by
      have h45 : 0 ≤ Real.log x ^ (0.45 : ℝ) := Real.rpow_nonneg hL0.le _
      have hsum : Real.log x ^ (0.05 : ℝ) * Real.log x ^ (0.45 : ℝ) =
          Real.log x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hL0]
        norm_num
      have h6 : 6 * Real.log x ^ (0.45 : ℝ) ≤ Real.log x ^ (1 / 2 : ℝ) := by
        rw [← hsum]
        exact mul_le_mul_of_nonneg_right h05 h45
      rw [Nat.cast_prod]
      calc ∏ p ∈ A ∪ A', (p : ℝ)
          ≤ ∏ _p ∈ A ∪ A', Real.exp (Real.log x ^ (0.45 : ℝ)) :=
            Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p)
              (fun p hp => (Strip.candidatePrimes_facts hL1 (hD hp)).2.2)
        _ = Real.exp (Real.log x ^ (0.45 : ℝ)) ^ (A ∪ A').card := Finset.prod_const _
        _ ≤ Real.exp (Real.log x ^ (0.45 : ℝ)) ^ 6 :=
            pow_le_pow_right₀ (Real.one_le_exp h45) hDcard
        _ = Real.exp (6 * Real.log x ^ (0.45 : ℝ)) := by
            rw [← Real.exp_nat_mul]
            norm_num
        _ ≤ Real.exp (Real.log x ^ (1 / 2 : ℝ)) := Real.exp_le_exp.mpr h6
    have hQrough : IsRough (roughCutoff x) (∏ p ∈ A ∪ A', p) := by
      intro q hq hqQ
      obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff (Nat.Prime.prime hq) _).mp hqQ
      have hpp := hprime p (hD hp)
      have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq hpp).mp hqp
      have hlow := (Strip.candidatePrimes_facts hL1 (hD hp)).2.1
      rw [hqeq]
      unfold roughCutoff
      exact lt_of_lt_of_le
        (Real.exp_lt_exp.mpr (Real.rpow_lt_rpow_of_exponent_lt hL (by norm_num))) hlow
    have hmain := abs_pattern_count_sub_le hj (fun p hp => hprime p (hA hp))
      (fun p hp => hprime p (hA' hp)) hd (fun i => roughDyad x (k i))
      (fun i n hn => (Nat.one_le_two_pow).trans (mem_roughDyad.mp hn).1.1)
      (fun i => mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i)
      (fun i => mul_nonneg hV.le (pow_nonneg zero_le_two _)) hε₀
      (fun i b => by
        rw [roughDyad_filter_modEq]
        exact hcount i _ hQpos hQle hQrough b)
    have hdens0 : 0 ≤ dens j A A' :=
      dens_nonneg hj (fun p hp => (hprime p (hA hp)).one_le)
        (fun p hp => (hprime p (hA' hp)).one_le)
    exact hmain.trans (mul_le_mul_of_nonneg_right hεε (mul_nonneg hM0 hdens0))
  · have hz : ∑ m ∈ roughBox x k, hit A A' (∏ i, m i - 1) = 0 :=
      Finset.sum_eq_zero fun m _ =>
        hit_eq_zero_of_not_disjoint (fun p hp => hprime p (hA hp)) hd _
    show |∑ m ∈ roughBox x k, hit A A' (∏ i, m i - 1) -
        (∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i) * dens j A A'| ≤
      ε * ((∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i) * dens j A A')
    rw [hz, dens_of_not hd, mul_zero, sub_zero, abs_zero, mul_zero]

open _root_.Classical in
/-- **Equidistribution of the patterns on rough product dyads** (`[P-07:0409–0431]`): for every
`ε > 0` and large `x`, on every box with `x^δ ≤ 2^{k_i} ≤ x^C`. From Lemma 2.5
(`RoughCounts`, residue classes modulo rough `d ≤ exp(L^{1/2})`) and `V(W) ≫ L^{-.24}`. -/
theorem eventually_boxEq (hR : RoughCounts) (hM : MertensProduct) {j : ℕ} (hj : 1 ≤ j)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ k : Fin j → ℕ,
      (∀ i, x ^ δ ≤ (2 : ℝ) ^ k i ∧ (2 : ℝ) ^ k i ≤ x ^ C) →
        BoxEq j (candidatePrimes x) (roughBox x k) (fun m => ∏ i, m i - 1)
          (∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i) ε := by
  obtain ⟨Mr, xr, hrough⟩ := hR δ C (1 / 2) 1 hδ hC (by norm_num) (by norm_num) one_pos
  obtain ⟨c₁, hc₁def⟩ :
      ∃ c₁ : ℝ, c₁ = Real.exp (-Real.eulerMascheroniConstant) / 2 := ⟨_, rfl⟩
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    exact div_pos (Real.exp_pos _) two_pos
  -- `t` with `(1 + t)^j = 1 + ε`
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (1 + ε) ^ ((j : ℝ)⁻¹) - 1 := ⟨_, rfl⟩
  have hj0 : j ≠ 0 := by omega
  have hjR : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by omega)
  have ht : 0 < t := by
    rw [htdef]
    have h1 : 1 < (1 + ε) ^ ((j : ℝ)⁻¹) := Real.one_lt_rpow (by linarith) (inv_pos.mpr hjR)
    linarith
  have htj : (1 + t) ^ j = 1 + ε := by
    rw [htdef, add_sub_cancel]
    exact Real.rpow_inv_natCast_pow (by linarith) hj0
  have hpow : ∀ a : ℝ, 0 < a → ∀ B : ℝ, ∀ᶠ x : ℝ in atTop, B ≤ Real.log x ^ a :=
    fun a ha B =>
      ((tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop).eventually_ge_atTop B
  filter_upwards [eventually_mertensProduct_roughCutoff_ge hM, eventually_ge_atTop xr,
    Real.tendsto_log_atTop.eventually_gt_atTop 1, hpow 0.05 (by norm_num) 6,
    hpow 0.76 (by norm_num) (|Mr| / (c₁ * t))] with x hV hxr hL h05 h76 k hk
  rw [← hc₁def] at hV
  have hL0 : 0 < Real.log x := by linarith
  have hVpos := mertensProduct_pos (roughCutoff x)
  have hVL : 0 < mertensProduct (roughCutoff x) * Real.log x := mul_pos hVpos hL0
  obtain ⟨ε₀, hε₀def⟩ :
      ∃ ε₀ : ℝ, ε₀ = |Mr| / (mertensProduct (roughCutoff x) * Real.log x) := ⟨_, rfl⟩
  have hε₀0 : 0 ≤ ε₀ := by
    rw [hε₀def]
    exact div_nonneg (abs_nonneg _) hVL.le
  have hε₀t : ε₀ ≤ t := by
    rw [hε₀def, div_le_iff₀ hVL]
    have h1 : |Mr| ≤ c₁ * t * Real.log x ^ (0.76 : ℝ) := by
      rwa [div_le_iff₀' (mul_pos hc₁ ht)] at h76
    have hsplit : Real.log x ^ (0.76 : ℝ) * Real.log x ^ (0.24 : ℝ) = Real.log x :=
      (Strip.strip_rpow_facts hL.le).1
    have h2 : c₁ * Real.log x ^ (0.76 : ℝ) ≤ mertensProduct (roughCutoff x) * Real.log x :=
      calc c₁ * Real.log x ^ (0.76 : ℝ)
          ≤ Real.log x ^ (0.24 : ℝ) * mertensProduct (roughCutoff x) *
              Real.log x ^ (0.76 : ℝ) :=
            mul_le_mul_of_nonneg_right hV.le (Real.rpow_nonneg hL0.le _)
        _ = mertensProduct (roughCutoff x) *
              (Real.log x ^ (0.76 : ℝ) * Real.log x ^ (0.24 : ℝ)) := by ring
        _ = mertensProduct (roughCutoff x) * Real.log x := by rw [hsplit]
    calc |Mr| ≤ c₁ * t * Real.log x ^ (0.76 : ℝ) := h1
      _ = t * (c₁ * Real.log x ^ (0.76 : ℝ)) := by ring
      _ ≤ t * (mertensProduct (roughCutoff x) * Real.log x) :=
          mul_le_mul_of_nonneg_left h2 ht.le
  have hεε : (1 + ε₀) ^ j - 1 ≤ ε := by
    have h1 := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + ε₀)
      (by linarith : 1 + ε₀ ≤ 1 + t) j
    rw [htj] at h1
    linarith
  refine boxEq_of_rough hj hL h05 hε₀0 hεε k ?_
  intro i d hd0 hdle hdrough b
  obtain ⟨hk1, hk2⟩ := hk i
  have hH0 : (0 : ℝ) < (2 : ℝ) ^ k i := pow_pos two_pos _
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd0
  have hcast : ((2 ^ k i : ℕ) : ℝ) = (2 : ℝ) ^ k i := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have hceil : ⌈(2 : ℝ) ^ k i⌉₊ = 2 ^ k i := by rw [← hcast, Nat.ceil_natCast]
  have hfloor : ⌊2 * (2 : ℝ) ^ k i⌋₊ = 2 ^ (k i + 1) := by
    have e : 2 * (2 : ℝ) ^ k i = ((2 ^ (k i + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      ring
    rw [e, Nat.floor_natCast]
  have h := (hrough x hxr ((2 : ℝ) ^ k i) hk1 hk2 ((2 : ℝ) ^ k i) (2 * (2 : ℝ) ^ k i) le_rfl
    (by linarith) le_rfl).2.1 d hd0 hdle hdrough b
  rw [hceil, hfloor, Real.rpow_neg_one] at h
  have e1 : mertensProduct (roughCutoff x) * (2 * (2 : ℝ) ^ k i - (2 : ℝ) ^ k i) / (d : ℝ) =
      mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i / (d : ℝ) := by ring
  rw [e1] at h
  refine h.trans ?_
  have hV0 : mertensProduct (roughCutoff x) ≠ 0 := hVpos.ne'
  have hLne : Real.log x ≠ 0 := hL0.ne'
  have hdne : (d : ℝ) ≠ 0 := hdR.ne'
  have e2 : ε₀ * (mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i / (d : ℝ)) =
      |Mr| * ((2 : ℝ) ^ k i / (d : ℝ)) * (Real.log x)⁻¹ := by
    rw [hε₀def]
    field_simp
  rw [e2]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self Mr) (div_nonneg hH0.le hdR.le))
    (inv_nonneg.mpr hL0.le)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin
