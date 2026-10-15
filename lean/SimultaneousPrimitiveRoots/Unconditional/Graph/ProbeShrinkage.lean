module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.HoeffdingCounts
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Choosing the probe count before the slot count

[S, §3, `eq:ideal-hoeffding-bound`]: for fixed positive ell and any
positive precision, choose a probe count first. Its scalar surviving
fraction is then small for every admissible number of slots and component
degree. This includes varying slot counts; no finite upper cutoff is used.
The tensor norm and frequency-uniform comparison are separate remaining work.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

/-- For positive ell the scalar shrinkage is bounded by a constant times 1/m. -/
theorem probe_shrinkage_le_inverse {m ell : ℕ} (hm : 0 < m) (hell : 0 < ell) :
    2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell ≤
      2 * (ell : ℝ) ^ ell / (m : ℝ) := by
  have hm' : 0 < (m : ℝ) := by positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : (m : ℝ) ≤ (m : ℝ) ^ ell := le_self_pow₀ hm1 (Nat.ne_of_gt hell)
  exact div_le_div_of_nonneg_left (by positivity) hm' hp

/-- One fixed threshold works for all subsequent probe counts. -/
theorem exists_probe_shrinkage_threshold {ell : ℕ} (hell : 0 < ell)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ m₀ : ℕ, N ≤ m₀ ∧ 0 < m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell < ε := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt
    (max (2 * (ell : ℝ) ^ ell / ε) (max (N : ℝ) 1))
  have hN : (N : ℝ) < (m₀ : ℝ) :=
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hm₀)
  have hm1 : (1 : ℝ) < (m₀ : ℝ) :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hm₀)
  have hmpos : 0 < m₀ := by exact_mod_cast (zero_lt_one.trans hm1)
  refine ⟨m₀, (by exact_mod_cast hN.le), hmpos, ?_⟩
  intro m hm
  have hmp : 0 < m := hmpos.trans_le hm
  have hm' : (m₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlarge : 2 * (ell : ℝ) ^ ell / ε < (m : ℝ) :=
    ((le_max_left _ _).trans_lt hm₀).trans_le hm'
  have hdiv : 2 * (ell : ℝ) ^ ell / (m : ℝ) < ε := by
    apply (div_lt_iff₀ (show 0 < (m : ℝ) by positivity)).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlarge
  exact (probe_shrinkage_le_inverse hmp hell).trans_lt hdiv

/-- Fix m before M. Every admissible component fraction is then below ε. -/
theorem exists_uniform_probe_fraction_lt {ell : ℕ} (hell : 0 < ell)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < m ∧ ∀ M j : ℕ,
      m ≤ j → j ≤ M → ell ≤ M - j →
      (m + ell) * (m + ell - 1) ≤ M →
      ((M - m - ell).choose (j - m) : ℝ) / (M.choose j : ℝ) < ε := by
  obtain ⟨m, hN, hm, hsmall⟩ := exists_probe_shrinkage_threshold hell hε N
  refine ⟨m, hN, hm, ?_⟩
  intro M j hmj hjM hellM hsize
  have hM : 0 < M := hm.trans_le (hmj.trans hjM)
  exact (probe_hoeffding_fraction_le hM hm hmj hjM hellM hsize).trans_lt
    (hsmall m le_rfl)

end SimultaneousPrimitiveRoots.Unconditional.Graph
