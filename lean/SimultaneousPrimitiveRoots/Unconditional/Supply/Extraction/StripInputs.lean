module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.StripCounts
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.StripCoeff

/-!
# The counts and the reciprocal sums of the weights of the stripping step

`[P-07:0347–0361, 0373–0379]`: for one large `x`, with `N = ⌊R x⌋ + 1`, `L = log x`, and when
every block `[H, 2H]`, `x^γ ≤ H ≤ x^3`, contains at most `c_b H` rough integers (Lemma 2.5):

* `∑_{m ≤ t} ρ(m) ≤ 2 c_b t` for `t ≤ N`;
* `∑_{m ≤ N} ρ(m)/m ≤ 5 c_b L` (`O(L)` blocks);
* `∑_{m ≤ N} σ(m)/m ≤ 3 c_b Λ` (the strip `x^γ < m ≤ x^γ e^Λ` has `O(Λ)` blocks);
* `∑_{m ≤ N} β(m)/m ≤ 10 c_β L` when `∑_{m ≤ t} β(m) ≤ c_β t` for all `t`.

This is `strip_inputs`. The hypotheses on `x` are `x ≥ 2(R + 1)`, `log x ≥ 2` and
`1 ≤ Λ ≤ log x`.

The declarations are in the namespace `Extraction.Strip`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip

noncomputable section

open _root_.Classical in
/-- **The inputs of the stripping step at one `x`.** -/
theorem strip_inputs {x γ R cb cβ Λ Λ₀ : ℝ} {P : Finset ℕ} (hR0 : 0 < R) (hγ : 0 < γ)
    (hγ1 : γ < 1) (hxR : 2 * (R + 1) ≤ x) (hL2 : 2 ≤ Real.log x) (hcb : 0 ≤ cb)
    (hblock : ∀ H : ℝ, x ^ γ ≤ H → H ≤ x ^ (3 : ℝ) →
      (((Finset.Icc ⌈H⌉₊ ⌊2 * H⌋₊).filter fun n => IsRough (roughCutoff x) n).card : ℝ) ≤
        cb * H)
    (hΛ1 : 1 ≤ Λ) (hΛL : Λ ≤ Real.log x) (hcβ : 0 ≤ cβ)
    (hbad : ∀ t : ℕ, ∑ m ∈ Finset.Icc 1 t, badW P Λ₀ m ≤ cβ * (t : ℝ)) :
    ((⌊R * x⌋₊ + 1 : ℕ) : ℝ) ≤ (R + 1) * x ∧
      (∀ t : ℕ, t ≤ ⌊R * x⌋₊ + 1 →
        ∑ m ∈ Finset.Icc 1 t, rhoW x γ m ≤ 2 * cb * (t : ℝ)) ∧
      ∑ m ∈ Finset.Icc 1 (⌊R * x⌋₊ + 1), rhoW x γ m / (m : ℝ) ≤ cb * (5 * Real.log x) ∧
      ∑ m ∈ Finset.Icc 1 (⌊R * x⌋₊ + 1), stripW x γ Λ m / (m : ℝ) ≤ cb * (3 * Λ) ∧
      ∑ m ∈ Finset.Icc 1 (⌊R * x⌋₊ + 1), badW P Λ₀ m / (m : ℝ) ≤
        2 * cβ * (5 * Real.log x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hA1 : 1 ≤ x ^ γ := Real.one_le_rpow hx1 hγ.le
  have hA0 : 0 < x ^ γ := lt_of_lt_of_le one_pos hA1
  have hAx : x ^ γ ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 hγ1.le
    rwa [Real.rpow_one] at h
  have hx3 : x ^ (3 : ℝ) = x * x * x := by
    have h : x ^ (3 : ℝ) = x ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast x 3
    rw [h]
    ring
  have hxx : x * x ≤ x * x * x := by
    have h := mul_le_mul_of_nonneg_left hx1 (mul_nonneg hx0.le hx0.le)
    linarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌊R * x⌋₊ + 1 := ⟨_, rfl⟩
  rw [← hNdef]
  have hN1' : 1 ≤ N := by
    rw [hNdef]
    exact Nat.le_add_left 1 _
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1'
  have hNle : (N : ℝ) ≤ (R + 1) * x := by
    rw [hNdef, Nat.cast_add, Nat.cast_one]
    have h := Nat.floor_le (mul_nonneg hR0.le hx0.le)
    linarith
  have h2N : 2 * (N : ℝ) ≤ x * x := by
    have h := mul_le_mul_of_nonneg_right hxR hx0.le
    linarith
  have hNH : (N : ℝ) ≤ x ^ (3 : ℝ) := by
    rw [hx3]
    linarith
  -- the number of blocks up to `2N`
  obtain ⟨K₁, hK1a, hK1b, hK1c⟩ := exists_pow_ge (y := 2 * (N : ℝ)) (by linarith)
  have hlog2N : Real.log (2 * (N : ℝ)) ≤ 2 * Real.log x := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < 2 * (N : ℝ)) h2N
    rwa [Real.log_mul hx0.ne' hx0.ne', ← two_mul] at h
  have hK1 : (K₁ : ℝ) ≤ 5 * Real.log x := by linarith
  have hK1H : 2 ^ K₁ * x ^ γ ≤ 2 * x ^ (3 : ℝ) := by
    rw [hx3]
    calc (2 : ℝ) ^ K₁ * x ^ γ ≤ 2 * (2 * (N : ℝ)) * x :=
          mul_le_mul hK1b hAx hA0.le (by linarith)
      _ ≤ 2 * (x * x) * x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2N two_pos.le) hx0.le
      _ = 2 * (x * x * x) := by ring
  have hNK : (N : ℝ) ≤ 2 ^ K₁ * x ^ γ := by
    have h := le_mul_of_one_le_right (pow_pos two_pos K₁).le hA1
    linarith
  refine ⟨hNle, fun t ht => ?_, ?_, ?_, ?_⟩
  · exact rough_count_le hA0 hcb hblock t ((Nat.cast_le.mpr ht).trans hNH)
  · exact (rough_reciprocal_le hA0 hcb hblock N K₁ hK1H (rhoW x γ) fun m hm =>
      rhoW_le_block ((Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans hNK)).trans
        (mul_le_mul_of_nonneg_left hK1 hcb)
  · -- the strip has `O(Λ)` blocks
    obtain ⟨K₂, hK2a, hK2b, hK2c⟩ :=
      exists_pow_ge (y := Real.exp Λ) (Real.one_le_exp (by linarith))
    rw [Real.log_exp] at hK2c
    have hK2 : (K₂ : ℝ) ≤ 3 * Λ := by linarith
    have hexp : Real.exp Λ ≤ x := by
      calc Real.exp Λ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hΛL
        _ = x := Real.exp_log hx0
    have hK2H : 2 ^ K₂ * x ^ γ ≤ 2 * x ^ (3 : ℝ) := by
      rw [hx3]
      calc (2 : ℝ) ^ K₂ * x ^ γ ≤ 2 * Real.exp Λ * x :=
            mul_le_mul hK2b hAx hA0.le (mul_nonneg two_pos.le (Real.exp_pos _).le)
        _ ≤ 2 * x * x :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp two_pos.le) hx0.le
        _ ≤ 2 * (x * x * x) := by linarith
    have hB : x ^ γ * Real.exp Λ ≤ 2 ^ K₂ * x ^ γ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hK2a hA0.le
    exact (rough_reciprocal_le hA0 hcb hblock N K₂ hK2H (stripW x γ Λ) fun m _ =>
      stripW_le_block hB m).trans (mul_le_mul_of_nonneg_left hK2 hcb)
  · have hK : (N : ℝ) ≤ 2 ^ K₁ * (1 / 2) := by linarith
    exact (reciprocal_of_count (badW_nonneg P Λ₀) hcβ hbad N K₁ hK).trans
      (mul_le_mul_of_nonneg_left hK1 (mul_nonneg two_pos.le hcβ))

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip
