module

public import SimultaneousPrimitiveRoots.SparseGoodCounting
public import Mathlib.Data.Nat.Find

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Filter
noncomputable section
open Classical

/-- Fixed-parameter eventual estimates admit one slowly growing cutoff
that controls every parameter below the cutoff at once. No quantitative
uniform onset is required, and no rate of growth is asserted. -/
theorem exists_eventually_controlled_cutoff (P : ℕ → ℝ → Prop)
    (hP : ∀ n : ℕ, ∀ᶠ x : ℝ in atTop, P n x) :
    ∃ Q : ℝ → ℕ, Tendsto Q atTop atTop ∧
      ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, n ≤ Q x → P n x := by
  have hfin (n : ℕ) : ∀ᶠ x : ℝ in atTop, ∀ k : ℕ, k ≤ n → P k x := by
    have h := (eventually_all_finset (Finset.range (n + 1))).mpr (fun k _ => hP k)
    filter_upwards [h] with x hx k hk
    exact hx k (Finset.mem_range.mpr (by omega))
  choose R hR using fun n => eventually_atTop.mp (hfin n)
  let Q : ℝ → ℕ := fun x => Nat.findGreatest (fun n => R n ≤ x) (Nat.floor x)
  have hQ : Tendsto Q atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    filter_upwards [eventually_ge_atTop (R n), eventually_ge_atTop (n : ℝ)] with x hx hn
    exact Nat.le_findGreatest (Nat.le_floor hn) hx
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [eventually_ge_atTop (R 0)] with x hx n hn
  have hRQ : R (Q x) ≤ x :=
    Nat.findGreatest_spec (P := fun k => R k ≤ x) (m := 0) (Nat.zero_le (Nat.floor x)) hx
  exact hR (Q x) x hRQ n hn

/-- A single cutoff for the actual exceptional prime sets, conditional
only on fixed-q eventual bounds with an onset allowed to depend on q.
This theorem does not assert those arithmetic bounds. -/
theorem exists_cutoff_of_fixed_powerResidue_counts (A : Finset ℕ) (C : ℝ)
    (hfixed : ∀ q : ℕ, ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, q.Prime → a < q →
      ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
        C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1)))) :
    ∃ Q : ℝ → ℕ, Tendsto Q atTop atTop ∧
      ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, q ≤ Q x → ∀ a ∈ A, q.Prime → a < q →
        ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
          C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) :=
  exists_eventually_controlled_cutoff _ hfixed

theorem smallExponentPowerResidueBound_of_cutoff_counts (A : Finset ℕ) (η C : ℝ)
    (Q : ℝ → ℕ) (hC : 0 ≤ C)
    (hcounts : ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, q ≤ Q x → ∀ a ∈ A, q.Prime → a < q →
      ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
        C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1)))) :
    SmallExponentPowerResidueBound A η ((A.card : ℝ) * C) Q := by
  intro Y hY hbase
  refine ⟨fun _ => 0, Asymptotics.isLittleO_zero _ _, ?_⟩
  filter_upwards [hcounts, eventually_ge_atTop (2 : ℝ)] with x hc hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hscale : 0 ≤ C * (x / Real.log x) := by positivity
  let S := (mediumObstructionPrimes Y η x).filter (fun q => q ≤ Q x)
  have hS (q : ℕ) (hq : q ∈ S) : q.Prime ∧ Y < q ∧ q ≤ Q x := by
    obtain ⟨hm, hcut⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, hp, hy⟩ := Finset.mem_filter.mp hm
    exact ⟨hp, hy, hcut⟩
  have htail := reciprocal_tail_finset_le hY S (fun q hq => (hS q hq).2.1)
  have hrow (a : ℕ) (ha : a ∈ A) :
      (∑ q ∈ S, ((powerResidueExceptionPrimes a q x).card : ℝ)) ≤
        (C / (Y : ℝ)) * (x / Real.log x) := by
    calc
      _ ≤ ∑ q ∈ S, C * (x / Real.log x) *
          (1 / ((q : ℝ) * ((q : ℝ) - 1))) := by
        apply Finset.sum_le_sum
        intro q hq
        exact hc q (hS q hq).2.2 a ha (hS q hq).1
          ((hbase a ha).trans_lt (hS q hq).2.1)
      _ = (C * (x / Real.log x)) *
          ∑ q ∈ S, 1 / ((q : ℝ) * ((q : ℝ) - 1)) := (Finset.mul_sum ..).symm
      _ ≤ (C * (x / Real.log x)) * (1 / (Y : ℝ)) :=
        mul_le_mul_of_nonneg_left htail hscale
      _ = _ := by ring
  calc
    sparseSmallExceptionSum A Y η Q x ≤
        ∑ _a ∈ A, (C / (Y : ℝ)) * (x / Real.log x) :=
      Finset.sum_le_sum (fun a ha => hrow a ha)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Fixed-q arithmetic estimates suffice for the whole small-q input,
with one cutoff shared by every Y. Its growth rate is left free. -/
theorem exists_smallExponentPowerResidueBound_of_fixed_counts (A : Finset ℕ) (η C : ℝ)
    (hC : 0 ≤ C)
    (hfixed : ∀ q : ℕ, ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, q.Prime → a < q →
      ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
        C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1)))) :
    ∃ Q : ℝ → ℕ, Tendsto Q atTop atTop ∧
      SmallExponentPowerResidueBound A η ((A.card : ℝ) * C) Q := by
  obtain ⟨Q, hQ, hc⟩ := exists_cutoff_of_fixed_powerResidue_counts A C hfixed
  exact ⟨Q, hQ, smallExponentPowerResidueBound_of_cutoff_counts A η C Q hC hc⟩

end
end SimultaneousPrimitiveRoots
