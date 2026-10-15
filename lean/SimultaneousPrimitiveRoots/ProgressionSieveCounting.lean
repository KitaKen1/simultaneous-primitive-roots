module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Finset

noncomputable section
open Classical

def residuePrefix (m r N : ℕ) : Finset ℕ :=
  (range N).filter fun n => n ≡ r [MOD m]

theorem residuePrefix_card_le (m r N : ℕ) :
    (residuePrefix m r N).card ≤ N / m + 1 := by
  have h := card_le_card_of_injOn (fun n : ℕ => n / m)
    (s := residuePrefix m r N) (t := range (N / m + 1))
  apply (h ?_ ?_).trans_eq (card_range _)
  · intro n hn
    obtain ⟨hnN, _⟩ := mem_filter.mp hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp hnN).le))
  · intro a ha b hb hab
    exact Nat.ext_div_modEq hab ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)

theorem residuePrefix_card_ge {m r : ℕ} (hm : 0 < m) (hr : r < m) (N : ℕ) :
    N / m ≤ (residuePrefix m r N).card := by
  have h := card_le_card_of_injOn (fun k : ℕ => r + m * k)
    (s := range (N / m)) (t := residuePrefix m r N)
  rw [← card_range (N / m)]
  apply h
  · intro k hk
    have hk1 : k + 1 ≤ N / m := mem_range.mp hk
    have hmul : m * (k + 1) ≤ N :=
      (Nat.mul_le_mul_left m hk1).trans (Nat.mul_div_le N m)
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by nlinarith), ?_⟩
    simp [Nat.ModEq, Nat.add_mod]
  · intro a _ b _ hab
    nlinarith

theorem nat_div_cast_bounds {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m ∧
      (N : ℝ) / m < ((N / m : ℕ) : ℝ) + 1 := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have heq : (N : ℝ) = (m : ℝ) * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N m).symm
  have hmod : ((N % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt N hm
  constructor
  · apply (le_div_iff₀ hm0).2
    have hmod0 : (0 : ℝ) ≤ ((N % m : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  · apply (div_lt_iff₀ hm0).2
    nlinarith

theorem residuePrefix_card_error_le_one {m r : ℕ} (hm : 0 < m) (hr : r < m) (N : ℕ) :
    |((residuePrefix m r N).card : ℝ) - (N : ℝ) / m| ≤ 1 := by
  have hlo : ((N / m : ℕ) : ℝ) ≤ (residuePrefix m r N).card :=
    by exact_mod_cast residuePrefix_card_ge hm hr N
  have hhi : ((residuePrefix m r N).card : ℝ) ≤ ((N / m : ℕ) : ℝ) + 1 := by
    exact_mod_cast residuePrefix_card_le m r N
  obtain ⟨hdivlo, hdivhi⟩ := nat_div_cast_bounds hm N
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def progressionDivisorSupport (q d N : ℕ) : Finset ℕ :=
  (range N).filter fun n => n ≡ 1 [MOD q] ∧ d ∣ n

def progressionSieveResidue (q d : ℕ) (h : q.Coprime d) : ℕ :=
  Nat.chineseRemainder h 1 0

theorem progressionSieveResidue_properties {q d : ℕ} (h : q.Coprime d) :
    progressionSieveResidue q d h ≡ 1 [MOD q] ∧
      progressionSieveResidue q d h ≡ 0 [MOD d] :=
  (Nat.chineseRemainder h 1 0).property

theorem progressionSieveResidue_lt {q d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (h : q.Coprime d) : progressionSieveResidue q d h < q * d :=
  Nat.chineseRemainder_lt_mul h 1 0 hq.ne' hd.ne'

theorem progression_divisor_conditions_iff {q d n : ℕ} (h : q.Coprime d) :
    (n ≡ 1 [MOD q] ∧ d ∣ n) ↔ n ≡ progressionSieveResidue q d h [MOD q * d] := by
  constructor
  · rintro ⟨hnq, hdn⟩
    exact Nat.chineseRemainder_modEq_unique h hnq hdn.modEq_zero_nat
  · intro hn
    obtain ⟨hrq, hrd⟩ := progressionSieveResidue_properties h
    refine ⟨(hn.of_dvd (dvd_mul_right q d)).trans hrq, ?_⟩
    exact Nat.modEq_zero_iff_dvd.mp ((hn.of_dvd (dvd_mul_left d q)).trans hrd)

theorem progressionDivisorSupport_eq_residuePrefix {q d : ℕ} (h : q.Coprime d) (N : ℕ) :
    progressionDivisorSupport q d N = residuePrefix (q * d) (progressionSieveResidue q d h) N := by
  ext n
  simp only [progressionDivisorSupport, residuePrefix, mem_filter,
    progression_divisor_conditions_iff h]

theorem progressionDivisorSupport_card_error_coprime {q d : ℕ}
    (hq : 0 < q) (hd : 0 < d) (h : q.Coprime d) (N : ℕ) :
    |((progressionDivisorSupport q d N).card : ℝ) - (N : ℝ) / ((q : ℝ) * d)| ≤ 1 := by
  rw [progressionDivisorSupport_eq_residuePrefix h]
  simpa only [Nat.cast_mul] using residuePrefix_card_error_le_one (Nat.mul_pos hq hd)
    (progressionSieveResidue_lt hq hd h) N

theorem progressionDivisorSupport_eq_empty_of_dvd {q d : ℕ} (hq : 1 < q) (hqd : q ∣ d)
    (N : ℕ) : progressionDivisorSupport q d N = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨_, hnq, hdn⟩ := mem_filter.mp hn
  have hqn : q ∣ n := hqd.trans hdn
  have hqone : q ∣ 1 := (hnq.dvd_iff (dvd_refl q)).mp hqn
  have := Nat.dvd_one.mp hqone
  omega

def progressionSieveDensity (q d : ℕ) : ℝ :=
  if q.Coprime d then 1 / ((q : ℝ) * d) else 0

theorem progressionSieveDensity_nonneg (q d : ℕ) : 0 ≤ progressionSieveDensity q d := by
  unfold progressionSieveDensity
  split_ifs <;> positivity

theorem progressionDivisorSupport_card_error {q d : ℕ} (hq : q.Prime) (hd : 0 < d) (N : ℕ) :
    |((progressionDivisorSupport q d N).card : ℝ) - (N : ℝ) * progressionSieveDensity q d| ≤ 1 := by
  by_cases hc : q.Coprime d
  · rw [progressionSieveDensity, if_pos hc, mul_one_div]
    exact progressionDivisorSupport_card_error_coprime hq.pos hd hc N
  · have hqd : q ∣ d := by
      by_contra hnd
      exact hc (hq.coprime_iff_not_dvd.mpr hnd)
    rw [progressionDivisorSupport_eq_empty_of_dvd hq.one_lt hqd, card_empty,
      progressionSieveDensity, if_neg hc]
    norm_num

theorem progressionDivisorSupport_card_le_mass_add_one {q d : ℕ} (hq : q.Prime)
    (hd : 0 < d) (N : ℕ) :
    ((progressionDivisorSupport q d N).card : ℝ) ≤ (N : ℝ) * progressionSieveDensity q d + 1 := by
  have h := (abs_le.mp (progressionDivisorSupport_card_error hq hd N)).2
  linarith

theorem progressionDivisorSupport_card_ge_mass_sub_one {q d : ℕ} (hq : q.Prime)
    (hd : 0 < d) (N : ℕ) :
    (N : ℝ) * progressionSieveDensity q d - 1 ≤ ((progressionDivisorSupport q d N).card : ℝ) := by
  have h := (abs_le.mp (progressionDivisorSupport_card_error hq hd N)).1
  linarith

theorem progressionSieveDensity_factor {q d : ℕ} (h : q.Coprime d) :
    progressionSieveDensity q d = (1 / (q : ℝ)) * (1 / (d : ℝ)) := by
  rw [progressionSieveDensity, if_pos h]
  ring

end

end SimultaneousPrimitiveRoots
