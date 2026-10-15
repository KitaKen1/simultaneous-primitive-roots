module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Statements

/-!
# Dyadic counts and reciprocal sums

Counting tools for [P] §7 (`[P-07:0347–0352]`: "decompose into full product dyads … the number of
`W`-rough integers in each dyad is `O(H_i V(W))`").

* `dyadic_sums`: if a nonnegative weight has mass `≤ c 2^k A` on each block `(2^k A, 2^{k+1} A]`,
  `k < K`, then its mass on `(A, 2^K A]` is `≤ c 2^K A` and its reciprocal sum there is `≤ c K`.
* `exists_pow_ge`: for `y ≥ 1` there is `K` with `y ≤ 2^K ≤ 2y` and `K ≤ 2 log y + 1`.
* `rough_block_sum_le`, `rough_dyadic`: the blocks of the indicator of the `W`-rough integers,
  from a bound `c_b H` for the number of rough integers of `[H, 2H]`, `A ≤ H ≤ H_max`.
* `rough_count_le`: `#{m ≤ t : m > A, m rough} ≤ 2 c_b t`;
  `rough_reciprocal_le`: `∑ σ(m)/m ≤ c_b K` for a weight `σ` below the rough indicator on
  `(A, 2^K A]`.
* `reciprocal_of_count`: `∑_{m ≤ M} β(m)/m ≤ 2 c K` when `∑_{m ≤ t} β(m) ≤ c t` for all `t` and
  `M ≤ 2^{K-1}`.

The declarations are in the namespace `Extraction.Strip`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip

noncomputable section

/-- Splitting the indicator of `(A, C]` at `B`. -/
theorem ite_Ioc_split {A B C y v : ℝ} (hAB : A ≤ B) (hBC : B ≤ C) :
    (if A < y ∧ y ≤ C then v else 0) =
      (if A < y ∧ y ≤ B then v else 0) + (if B < y ∧ y ≤ C then v else 0) := by
  by_cases h1 : y ≤ B
  · have hB : ¬ (B < y ∧ y ≤ C) := fun h => absurd h.1 (not_lt.mpr h1)
    rw [if_neg hB, add_zero]
    by_cases h2 : A < y
    · have h3 : A < y ∧ y ≤ C := ⟨h2, h1.trans hBC⟩
      have h4 : A < y ∧ y ≤ B := ⟨h2, h1⟩
      rw [if_pos h3, if_pos h4]
    · have h3 : ¬ (A < y ∧ y ≤ C) := fun h => h2 h.1
      have h4 : ¬ (A < y ∧ y ≤ B) := fun h => h2 h.1
      rw [if_neg h3, if_neg h4]
  · have h1' : B < y := not_le.mp h1
    have hAB' : ¬ (A < y ∧ y ≤ B) := fun h => h1 h.2
    rw [if_neg hAB', zero_add]
    by_cases h2 : y ≤ C
    · have h3 : A < y ∧ y ≤ C := ⟨lt_of_le_of_lt hAB h1', h2⟩
      have h4 : B < y ∧ y ≤ C := ⟨h1', h2⟩
      rw [if_pos h3, if_pos h4]
    · have h3 : ¬ (A < y ∧ y ≤ C) := fun h => h2 h.2
      have h4 : ¬ (B < y ∧ y ≤ C) := fun h => h2 h.2
      rw [if_neg h3, if_neg h4]

/-- **Dyadic blocks**: mass `≤ c 2^k A` on each block `(2^k A, 2^{k+1} A]`, `k < K`, gives mass
`≤ c 2^K A` and reciprocal sum `≤ c K` on `(A, 2^K A]`. -/
theorem dyadic_sums {w : ℕ → ℝ} (hw : ∀ m, 0 ≤ w m) {A c : ℝ} (hA : 0 < A) (hc : 0 ≤ c)
    (M : ℕ) : ∀ K : ℕ,
    (∀ k, k < K → ∑ m ∈ Finset.Icc 1 M,
        (if 2 ^ k * A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (k + 1) * A then w m else 0) ≤
          c * (2 ^ k * A)) →
      ∑ m ∈ Finset.Icc 1 M, (if A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ K * A then w m else 0) ≤
          c * (2 ^ K * A) ∧
        ∑ m ∈ Finset.Icc 1 M,
            (if A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ K * A then w m / (m : ℝ) else 0) ≤ c * (K : ℝ) := by
  intro K
  induction K with
  | zero =>
    intro _
    have hz : ∀ f : ℕ → ℝ, ∑ m ∈ Finset.Icc 1 M,
        (if A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ 0 * A then f m else 0) = 0 := fun f =>
      Finset.sum_eq_zero fun m _ => if_neg fun h => by
        rw [pow_zero, one_mul] at h
        exact absurd h.1 (not_lt.mpr h.2)
    rw [hz w, hz fun m => w m / (m : ℝ), Nat.cast_zero, mul_zero]
    exact ⟨mul_nonneg hc (mul_nonneg (pow_nonneg zero_le_two _) hA.le), le_rfl⟩
  | succ K ih =>
    intro hblocks
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hblocks k (Nat.lt_succ_of_lt hk)
    have hb := hblocks K (Nat.lt_succ_self K)
    have hKA : 0 < 2 ^ K * A := mul_pos (pow_pos zero_lt_two K) hA
    have hA1 : A ≤ 2 ^ K * A := le_mul_of_one_le_left hA.le (one_le_pow₀ one_le_two)
    have hA2 : 2 ^ K * A ≤ 2 ^ (K + 1) * A := by
      rw [pow_succ]
      linarith
    have hsplit : ∀ f : ℕ → ℝ, ∑ m ∈ Finset.Icc 1 M,
        (if A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (K + 1) * A then f m else 0) =
        ∑ m ∈ Finset.Icc 1 M, (if A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ K * A then f m else 0) +
          ∑ m ∈ Finset.Icc 1 M,
            (if 2 ^ K * A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (K + 1) * A then f m else 0) := fun f => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => ite_Ioc_split hA1 hA2
    have hblockrec : ∑ m ∈ Finset.Icc 1 M,
        (if 2 ^ K * A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (K + 1) * A then w m / (m : ℝ) else 0) ≤ c := by
      have h1 : ∑ m ∈ Finset.Icc 1 M,
          (if 2 ^ K * A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (K + 1) * A then w m / (m : ℝ) else 0) ≤
          ∑ m ∈ Finset.Icc 1 M,
            (if 2 ^ K * A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (K + 1) * A then w m else 0) /
              (2 ^ K * A) := by
        refine Finset.sum_le_sum fun m _ => ?_
        by_cases h : 2 ^ K * A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (K + 1) * A
        · rw [if_pos h, if_pos h]
          exact div_le_div_of_nonneg_left (hw m) hKA h.1.le
        · rw [if_neg h, if_neg h, zero_div]
      rw [← Finset.sum_div] at h1
      refine h1.trans ?_
      rw [div_le_iff₀ hKA]
      exact hb
    constructor
    · rw [hsplit w]
      have e : c * (2 ^ (K + 1) * A) = c * (2 ^ K * A) + c * (2 ^ K * A) := by
        rw [pow_succ]
        ring
      rw [e]
      exact add_le_add ih1 hb
    · rw [hsplit fun m => w m / (m : ℝ), Nat.cast_succ, mul_add, mul_one]
      exact add_le_add ih2 hblockrec

/-- For `y ≥ 1` there is `K` with `y ≤ 2^K ≤ 2y` and `K ≤ 2 log y + 1`. -/
theorem exists_pow_ge {y : ℝ} (hy : 1 ≤ y) :
    ∃ K : ℕ, y ≤ 2 ^ K ∧ (2 : ℝ) ^ K ≤ 2 * y ∧ (K : ℝ) ≤ 2 * Real.log y + 1 := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hy (one_lt_two : (1 : ℝ) < 2)
  refine ⟨n + 1, hn2.le, ?_, ?_⟩
  · rw [pow_succ]
    linarith
  · have h1 : Real.log ((2 : ℝ) ^ n) ≤ Real.log y :=
      Real.log_le_log (pow_pos zero_lt_two n) hn1
    rw [Real.log_pow] at h1
    have h2 := Real.log_two_gt_d9
    have h3 : (n : ℝ) * (1 / 2) ≤ (n : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
    rw [Nat.cast_succ]
    linarith

/-! ### Rough integers -/

section Rough

open _root_.Classical in
/-- The mass of the rough indicator on a block `(H, 2H]` is at most the number of rough integers
of `[H, 2H]`. -/
theorem rough_block_sum_le {W cb H H2 : ℝ} (hH2 : H2 = 2 * H) (M : ℕ)
    (hcount : (((Finset.Icc ⌈H⌉₊ ⌊2 * H⌋₊).filter fun n => IsRough W n).card : ℝ) ≤ cb * H) :
    ∑ m ∈ Finset.Icc 1 M, (if H < (m : ℝ) ∧ (m : ℝ) ≤ H2 then
      (if IsRough W m then (1 : ℝ) else 0) else 0) ≤ cb * H := by
  have h1 : ∑ m ∈ Finset.Icc 1 M, (if H < (m : ℝ) ∧ (m : ℝ) ≤ H2 then
        (if IsRough W m then (1 : ℝ) else 0) else 0) =
      (((Finset.Icc 1 M).filter fun m : ℕ =>
        (H < (m : ℝ) ∧ (m : ℝ) ≤ H2) ∧ IsRough W m).card : ℝ) := by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases ha : H < (m : ℝ) ∧ (m : ℝ) ≤ H2
    · by_cases hb : IsRough W m
      · have hab : (H < (m : ℝ) ∧ (m : ℝ) ≤ H2) ∧ IsRough W m := ⟨ha, hb⟩
        rw [if_pos ha, if_pos hb, if_pos hab]
      · have hab : ¬ ((H < (m : ℝ) ∧ (m : ℝ) ≤ H2) ∧ IsRough W m) := fun h => hb h.2
        rw [if_pos ha, if_neg hb, if_neg hab]
    · have hab : ¬ ((H < (m : ℝ) ∧ (m : ℝ) ≤ H2) ∧ IsRough W m) := fun h => ha h.1
      rw [if_neg ha, if_neg hab]
  have hsub : ((Finset.Icc 1 M).filter fun m : ℕ =>
      (H < (m : ℝ) ∧ (m : ℝ) ≤ H2) ∧ IsRough W m) ⊆
      (Finset.Icc ⌈H⌉₊ ⌊2 * H⌋₊).filter fun n => IsRough W n := by
    intro m hm
    obtain ⟨-, ⟨h2, h3⟩, h4⟩ := Finset.mem_filter.mp hm
    rw [hH2] at h3
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr h2.le, Nat.le_floor h3⟩, h4⟩
  rw [h1]
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcount

variable {W A cb Hmax : ℝ}

open _root_.Classical in
/-- The rough indicator on `(A, 2^K A]`: mass `≤ c_b 2^K A` and reciprocal sum `≤ c_b K`, when
`[H, 2H]` contains at most `c_b H` rough integers for `A ≤ H ≤ H_max` and `2^K A ≤ 2 H_max`. -/
theorem rough_dyadic (hA : 0 < A) (hcb : 0 ≤ cb)
    (hblock : ∀ H : ℝ, A ≤ H → H ≤ Hmax →
      (((Finset.Icc ⌈H⌉₊ ⌊2 * H⌋₊).filter fun n => IsRough W n).card : ℝ) ≤ cb * H)
    (M K : ℕ) (hK : 2 ^ K * A ≤ 2 * Hmax) :
    ∑ m ∈ Finset.Icc 1 M, (if A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ K * A then
        (if IsRough W m then (1 : ℝ) else 0) else 0) ≤ cb * (2 ^ K * A) ∧
      ∑ m ∈ Finset.Icc 1 M, (if A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ K * A then
        (if IsRough W m then (1 : ℝ) else 0) / (m : ℝ) else 0) ≤ cb * (K : ℝ) := by
  have hw : ∀ m : ℕ, (0 : ℝ) ≤ if IsRough W m then (1 : ℝ) else 0 := fun m => by
    by_cases h : IsRough W m
    · rw [if_pos h]
      exact zero_le_one
    · rw [if_neg h]
  refine dyadic_sums hw hA hcb M K fun k hk => ?_
  have h1 : A ≤ 2 ^ k * A := le_mul_of_one_le_left hA.le (one_le_pow₀ one_le_two)
  have h2 : (2 : ℝ) ^ (k + 1) * A ≤ 2 ^ K * A :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hk) hA.le
  have h3 : (2 : ℝ) ^ (k + 1) * A = 2 * (2 ^ k * A) := by
    rw [pow_succ]
    ring
  exact rough_block_sum_le h3 M (hblock _ h1 (by linarith))

open _root_.Classical in
/-- `#{m ≤ t : m > A, m rough} ≤ 2 c_b t` for `t ≤ H_max`. -/
theorem rough_count_le (hA : 0 < A) (hcb : 0 ≤ cb)
    (hblock : ∀ H : ℝ, A ≤ H → H ≤ Hmax →
      (((Finset.Icc ⌈H⌉₊ ⌊2 * H⌋₊).filter fun n => IsRough W n).card : ℝ) ≤ cb * H)
    (t : ℕ) (ht : (t : ℝ) ≤ Hmax) :
    ∑ m ∈ Finset.Icc 1 t, (if A < (m : ℝ) ∧ IsRough W m then (1 : ℝ) else 0) ≤
      2 * cb * (t : ℝ) := by
  by_cases hAt : A ≤ (t : ℝ)
  · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ((one_le_div hA).mpr hAt)
      (one_lt_two : (1 : ℝ) < 2)
    have h1 : (2 : ℝ) ^ n * A ≤ (t : ℝ) := (le_div_iff₀ hA).mp hn1
    have h2 : (t : ℝ) < 2 ^ (n + 1) * A := (div_lt_iff₀ hA).mp hn2
    have h3 : (2 : ℝ) ^ (n + 1) * A = 2 * (2 ^ n * A) := by
      rw [pow_succ]
      ring
    obtain ⟨hd, -⟩ := rough_dyadic hA hcb hblock t (n + 1) (by linarith)
    have hle : ∑ m ∈ Finset.Icc 1 t, (if A < (m : ℝ) ∧ IsRough W m then (1 : ℝ) else 0) ≤
        ∑ m ∈ Finset.Icc 1 t, (if A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (n + 1) * A then
          (if IsRough W m then (1 : ℝ) else 0) else 0) := by
      refine Finset.sum_le_sum fun m hm => ?_
      have hmt : (m : ℝ) ≤ (t : ℝ) := Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2
      by_cases h : A < (m : ℝ) ∧ IsRough W m
      · have h4 : A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (n + 1) * A := ⟨h.1, by linarith⟩
        rw [if_pos h, if_pos h4, if_pos h.2]
      · rw [if_neg h]
        by_cases h4 : A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (n + 1) * A
        · have h5 : ¬ IsRough W m := fun h6 => h ⟨h4.1, h6⟩
          rw [if_pos h4, if_neg h5]
        · rw [if_neg h4]
    refine hle.trans (hd.trans ?_)
    rw [h3]
    nlinarith
  · have hz : ∑ m ∈ Finset.Icc 1 t, (if A < (m : ℝ) ∧ IsRough W m then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun m hm => if_neg fun h => by
        have hmt : (m : ℝ) ≤ (t : ℝ) := Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2
        exact hAt (h.1.le.trans hmt)
    rw [hz]
    exact mul_nonneg (mul_nonneg zero_le_two hcb) (Nat.cast_nonneg t)

open _root_.Classical in
/-- `∑_{m ≤ M} σ(m)/m ≤ c_b K` for a weight `σ` below the rough indicator on `(A, 2^K A]`. -/
theorem rough_reciprocal_le (hA : 0 < A) (hcb : 0 ≤ cb)
    (hblock : ∀ H : ℝ, A ≤ H → H ≤ Hmax →
      (((Finset.Icc ⌈H⌉₊ ⌊2 * H⌋₊).filter fun n => IsRough W n).card : ℝ) ≤ cb * H)
    (M K : ℕ) (hK : 2 ^ K * A ≤ 2 * Hmax) (σ : ℕ → ℝ)
    (hσ : ∀ m ∈ Finset.Icc 1 M, σ m ≤ if A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ K * A then
      (if IsRough W m then (1 : ℝ) else 0) else 0) :
    ∑ m ∈ Finset.Icc 1 M, σ m / (m : ℝ) ≤ cb * (K : ℝ) := by
  obtain ⟨-, hd⟩ := rough_dyadic hA hcb hblock M K hK
  refine (Finset.sum_le_sum fun m hm => ?_).trans hd
  have h1 := div_le_div_of_nonneg_right (hσ m hm) (Nat.cast_nonneg m)
  refine h1.trans (le_of_eq ?_)
  by_cases h : A < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ K * A
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_div]

end Rough

/-! ### From counts to reciprocal sums -/

/-- If `∑_{m ≤ t} β(m) ≤ c t` for all `t`, then `∑_{m ≤ M} β(m)/m ≤ 2 c K` for `M ≤ 2^K / 2`. -/
theorem reciprocal_of_count {β : ℕ → ℝ} (hβ : ∀ m, 0 ≤ β m) {c : ℝ} (hc : 0 ≤ c)
    (hcount : ∀ t : ℕ, ∑ m ∈ Finset.Icc 1 t, β m ≤ c * (t : ℝ)) (M K : ℕ)
    (hK : (M : ℝ) ≤ 2 ^ K * (1 / 2)) :
    ∑ m ∈ Finset.Icc 1 M, β m / (m : ℝ) ≤ 2 * c * (K : ℝ) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hblocks : ∀ k, k < K → ∑ m ∈ Finset.Icc 1 M,
      (if 2 ^ k * (1 / 2 : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (k + 1) * (1 / 2 : ℝ) then β m else 0) ≤
        2 * c * (2 ^ k * (1 / 2 : ℝ)) := by
    intro k _
    have hsub : (Finset.Icc 1 M).filter (fun m : ℕ =>
        2 ^ k * (1 / 2 : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (k + 1) * (1 / 2 : ℝ)) ⊆
        Finset.Icc 1 (2 ^ k) := by
      intro m hm
      obtain ⟨h1, -, h3⟩ := Finset.mem_filter.mp hm
      have h4 : (m : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        rw [pow_succ] at h3
        linarith
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp h1).1, Nat.cast_le.mp h4⟩
    have h5 := hcount (2 ^ k)
    rw [Nat.cast_pow, Nat.cast_ofNat] at h5
    rw [← Finset.sum_filter]
    calc ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ =>
          2 ^ k * (1 / 2 : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ (k + 1) * (1 / 2 : ℝ)), β m
        ≤ ∑ m ∈ Finset.Icc 1 (2 ^ k), β m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hβ m
      _ ≤ c * 2 ^ k := h5
      _ = 2 * c * (2 ^ k * (1 / 2 : ℝ)) := by ring
  obtain ⟨-, hd⟩ := dyadic_sums hβ hhalf (mul_nonneg zero_le_two hc) M K hblocks
  refine (Finset.sum_le_sum fun m hm => ?_).trans hd
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  have h1 : (1 / 2 : ℝ) < (m : ℝ) := by
    have h2 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    linarith
  have h3 : (m : ℝ) ≤ 2 ^ K * (1 / 2 : ℝ) := (Nat.cast_le.mpr hm2).trans hK
  have h4 : (1 / 2 : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ 2 ^ K * (1 / 2 : ℝ) := ⟨h1, h3⟩
  rw [if_pos h4]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip
