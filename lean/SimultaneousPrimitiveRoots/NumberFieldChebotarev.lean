module

public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount
public import TauCeti.NumberTheory.Chebotarev.SplitsCompletely
public import TauCeti.Algebra.Group.ConjFinite

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Filter NumberField
open scoped Topology
noncomputable section

/-- Qualitative complete-splitting counts for a fixed Galois extension.
There is no moving-family uniform onset in this statement. -/
theorem fixed_frobeniusPrimeCount_one_tendsto (K L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    Tendsto (fun x : ℝ => (Chebotarev.frobeniusPrimeCount K L 1 x : ℝ) /
      (x / Real.log x)) atTop (𝓝 (1 / (Module.finrank K L : ℝ))) := by
  simpa only [ConjClasses.one_eq_mk_one, Nat.card_coe_set_eq,
    ConjClasses.ncard_carrier_mk_of_mem_center (Subgroup.one_mem _), Nat.cast_one,
    IsGalois.card_aut_eq_finrank] using Chebotarev.tendsto_frobeniusPrimeCount K L 1

/-- The coefficient is universal; the eventual onset may depend on K,L. -/
theorem fixed_frobeniusPrimeCount_one_eventually_le (K L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    ∀ᶠ x : ℝ in atTop, (Chebotarev.frobeniusPrimeCount K L 1 x : ℝ) ≤
      2 * (x / Real.log x) * (1 / (Module.finrank K L : ℝ)) := by
  have hd : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have hlt : 1 / (Module.finrank K L : ℝ) < 2 / (Module.finrank K L : ℝ) := by
    exact div_lt_div_of_pos_right (by norm_num) hd
  have h := (fixed_frobeniusPrimeCount_one_tendsto K L).eventually (gt_mem_nhds hlt)
  filter_upwards [h, eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hscale : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos (by linarith))
  have hb := (div_lt_iff₀ hscale).mp hx
  calc
    _ ≤ (2 / (Module.finrank K L : ℝ)) * (x / Real.log x) := hb.le
    _ = _ := by ring

end
end SimultaneousPrimitiveRoots
