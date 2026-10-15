module

public import SimultaneousPrimitiveRoots.ProgressionSieveData
public import LeanPool.SelbergSieve4.AuxResults

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Finset
noncomputable section
open Classical

theorem multiples_Icc_eq_image (q M : ℕ) (hq : 0 < q) :
    (Icc 1 M).filter (fun m => q ∣ m) = (Icc 1 (M / q)).image (fun k => q * k) := by
  ext m
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨hm1, hmM⟩, ⟨k, rfl⟩⟩
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · by_contra hk
      have : k = 0 := by omega
      simp [this] at hm1
    · exact (Nat.le_div_iff_mul_le hq).mpr (by simpa [mul_comm] using hmM)
  · rintro ⟨k, ⟨hk1, hkM⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, dvd_mul_right q k⟩
    · exact Nat.succ_le_iff.mpr (Nat.mul_pos hq (by omega))
    · simpa [mul_comm] using Nat.mul_le_of_le_div q k M hkM

theorem harmonic_multiples_eq (q M : ℕ) (hq : 0 < q) :
    (∑ m ∈ (Icc 1 M).filter (fun m => q ∣ m), 1 / (m : ℝ)) =
      (1 / (q : ℝ)) * ∑ k ∈ Icc 1 (M / q), 1 / (k : ℝ) := by
  rw [multiples_Icc_eq_image q M hq, sum_image]
  · simp_rw [Nat.cast_mul, one_div, mul_inv]
    rw [mul_sum]
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left hq hij

theorem harmonic_multiples_le (q M : ℕ) (hq : 0 < q) :
    (∑ m ∈ (Icc 1 M).filter (fun m => q ∣ m), 1 / (m : ℝ)) ≤
      (1 / (q : ℝ)) * ∑ k ∈ Icc 1 M, 1 / (k : ℝ) := by
  rw [harmonic_multiples_eq q M hq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨hk1, hkM⟩ := mem_Icc.mp hk
    exact mem_Icc.mpr ⟨hk1, hkM.trans (Nat.div_le_self M q)⟩
  · intro k _ _
    positivity

theorem harmonic_coprime_ge_half {q : ℕ} (hq : q.Prime) (M : ℕ) :
    (1 / 2 : ℝ) * (∑ m ∈ Icc 1 M, 1 / (m : ℝ)) ≤
      ∑ m ∈ (Icc 1 M).filter (q.Coprime ·), 1 / (m : ℝ) := by
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 M) (fun m => q ∣ m)
    (fun m => 1 / (m : ℝ))
  have heq : (Icc 1 M).filter (fun m => ¬ q ∣ m) = (Icc 1 M).filter (q.Coprime ·) := by
    ext m
    simp [hq.coprime_iff_not_dvd]
  rw [heq] at hsplit
  have hbound := harmonic_multiples_le q M hq.pos
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hinv : 1 / (q : ℝ) ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hq2
  have hnonneg : 0 ≤ ∑ m ∈ Icc 1 M, 1 / (m : ℝ) :=
    sum_nonneg (fun _ _ => by positivity)
  have hhalf := hbound.trans (mul_le_mul_of_nonneg_right hinv hnonneg)
  linarith

theorem harmonic_coprime_ge_log {q : ℕ} (hq : q.Prime) (R : ℝ) (hR : 1 ≤ R) :
    Real.log R / 2 ≤
      ∑ m ∈ (Icc 1 (Nat.floor R)).filter (q.Coprime ·), 1 / (m : ℝ) := by
  have hlog : Real.log R ≤ ∑ m ∈ Icc 1 (Nat.floor R), 1 / (m : ℝ) := by
    simpa only [one_div] using Aux.log_le_sum_inv R hR
  have h := (mul_le_mul_of_nonneg_left hlog
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans (harmonic_coprime_ge_half hq (Nat.floor R))
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using h

end

end SimultaneousPrimitiveRoots
