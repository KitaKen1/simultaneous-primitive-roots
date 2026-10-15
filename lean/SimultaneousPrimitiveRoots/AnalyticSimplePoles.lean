module

public import SimultaneousPrimitiveRoots.AnalyticLogDerivativeResidue

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter
open scoped Topology
noncomputable section
open Classical

/-- A derived analytic principal part rules out higher order poles. -/
theorem meromorphicOrderAt_ge_neg_one_of_principal_part {f g : ℂ → ℂ} {s c : ℂ}
    (hg : AnalyticAt ℂ g s)
    (heq : f =ᶠ[𝓝[≠] s] fun z => c / (z - s) + g z) :
    (-1 : ℤ) ≤ meromorphicOrderAt f s := by
  have hp : MeromorphicAt (fun z : ℂ => c / (z - s)) s :=
    (MeromorphicAt.const c s).div (by fun_prop)
  have ho : (-1 : ℤ) ≤ meromorphicOrderAt (fun z : ℂ => c / (z - s)) s := by
    change (-1 : ℤ) ≤ meromorphicOrderAt ((fun _ : ℂ => c) / (fun z : ℂ => z - s)) s
    rw [meromorphicOrderAt_div (MeromorphicAt.const c s) (by fun_prop),
      meromorphicOrderAt_const, meromorphicOrderAt_id_sub_const]
    split_ifs <;> simp
  rw [meromorphicOrderAt_congr heq]
  exact (le_min ho (le_trans (WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by decide)) hg.meromorphicOrderAt_nonneg)).trans
    (meromorphicOrderAt_add hp hg.meromorphicAt)

/-- A nonzero derived residue makes the pole exactly simple. -/
theorem meromorphicOrderAt_eq_neg_one_of_principal_part {f g : ℂ → ℂ} {s c : ℂ}
    (hg : AnalyticAt ℂ g s) (hc : c ≠ 0)
    (heq : f =ᶠ[𝓝[≠] s] fun z => c / (z - s) + g z) :
    meromorphicOrderAt f s = (-1 : ℤ) := by
  have ho : meromorphicOrderAt (fun z : ℂ => c / (z - s)) s = (-1 : ℤ) := by
    change meromorphicOrderAt ((fun _ : ℂ => c) / (fun z : ℂ => z - s)) s = (-1 : ℤ)
    rw [meromorphicOrderAt_div (MeromorphicAt.const c s) (by fun_prop),
      meromorphicOrderAt_const, if_neg hc, meromorphicOrderAt_id_sub_const]
    norm_num
  have hlt : meromorphicOrderAt (fun z : ℂ => c / (z - s)) s < meromorphicOrderAt g s := by
    rw [ho]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)) hg.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr heq]
  change meromorphicOrderAt ((fun z : ℂ => c / (z - s)) + g) s = (-1 : ℤ)
  rw [meromorphicOrderAt_add_eq_left_of_lt hg.meromorphicAt hlt, ho]

end
end SimultaneousPrimitiveRoots
