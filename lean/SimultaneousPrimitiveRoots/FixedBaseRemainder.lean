module

public import SimultaneousPrimitiveRoots.AggregatedMain
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter Topology

/-- Abstract fixed-field zero sum: beta are real parts and weights are the
absolute Mellin weights, with repeated zeros listed with multiplicity. -/
noncomputable def fixedBaseZeroRemainder {ι : Type*} (β w : ι → ℝ) (x : ℝ) : ℝ :=
  ∑' i, w i * x ^ (β i - 1)

/-- No common gap beta <= 1-delta is required for the fixed field. The actual
zero enumeration and summability of its Mellin weights remain analytic work. -/
theorem fixedBaseZeroRemainder_tendsto {ι : Type*} (β w : ι → ℝ)
    (hβ : ∀ i, β i < 1) (hw : ∀ i, 0 ≤ w i) (hsum : Summable w) :
    Tendsto (fixedBaseZeroRemainder β w) atTop (𝓝 0) := by
  have hterm : ∀ i, Tendsto (fun x : ℝ => w i * x ^ (β i - 1)) atTop (𝓝 (0 : ℝ)) := by
    intro i
    have hpow : Tendsto (fun x : ℝ => x ^ (β i - 1)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr (hβ i))
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  have hbound : ∀ᶠ x : ℝ in atTop, ∀ i, ‖w i * x ^ (β i - 1)‖ ≤ w i := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx i
    have hp : 0 ≤ x ^ (β i - 1) := Real.rpow_nonneg (by linarith) _
    have hle : x ^ (β i - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith [hβ i])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw i) hp)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (hw i)
  change Tendsto (fun x : ℝ => ∑' i, w i * x ^ (β i - 1)) atTop (𝓝 0)
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence hsum hterm hbound

/-- The exact counting estimate to obtain from the fixed-field zero comparison
and smoothed explicit formula in research_patch_ja.md (6.6)--(6.8). It is an
unproved input on actual prime counts, not a formalized Hecke theorem. -/
def FixedBasePowerResidueBound (A : Finset ℕ) (δ m C : ℝ) (R : ℝ → ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, q.Prime → a < q →
    ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      (m + R x) * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x

theorem fixedBase_remainder_eventually_below (R : ℝ → ℝ) {m : ℝ}
    (hm : m < 2) (hR : Tendsto R atTop (𝓝 0)) :
    ∀ᶠ x : ℝ in atTop, m + R x ≤ 2 := by
  filter_upwards [hR.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < 2 - m))]
    with x hx
  linarith

/-- The onset is independent of q because the remainder comes from one fixed
field. max(2,C) also resolves the differing constants in the two terms of U. -/
theorem uniformPowerResidueBound_of_fixedBase {A : Finset ℕ} {δ η m C : ℝ}
    {R : ℝ → ℝ} (hm : m < 2) (hR : Tendsto R atTop (𝓝 0))
    (hcount : FixedBasePowerResidueBound A δ m C R) :
    UniformPowerResidueBound A δ η (max 2 C) := by
  filter_upwards [hcount, fixedBase_remainder_eventually_below R hm hR,
    eventually_ge_atTop (2 : ℝ)] with x hc hrem hx
  intro a ha q hq haq _
  have hqp : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have hq1 : 0 < (q : ℝ) - 1 := by
    have : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
    linarith
  have hscale : 0 ≤ (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) := by
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  have herror : 0 ≤ x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x := by
    have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  have hmC : m + R x ≤ max 2 C := hrem.trans (le_max_left _ _)
  have hmain := mul_le_mul_of_nonneg_right hmC hscale
  have herr := mul_le_mul_of_nonneg_right (le_max_right (2 : ℝ) C) herror
  have hsum := add_le_add hmain herr
  have hc' := hc a ha q hq haq
  exact hc'.trans (by simpa only [mul_assoc, mul_div_assoc] using hsum)

theorem mainClaim_of_fixedBase_bounds {δ η : ℝ} (hη : 0 ≤ η) (hηδ : η < δ)
    (hηhalf : η < 1 / 2)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hfixed : ∀ A : Finset ℕ, Admissible A →
      ∃ m C : ℝ, ∃ R : ℝ → ℝ, m < 2 ∧ Tendsto R atTop (𝓝 0) ∧
        FixedBasePowerResidueBound A δ m C R) : MainClaim := by
  apply mainClaim_of_aggregated_bounds hηhalf hsupply
  intro A hA
  obtain ⟨m, C, R, hm, hR, hc⟩ := hfixed A hA
  have hC : 0 ≤ max (2 : ℝ) C := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  refine ⟨(A.card : ℝ) * max 2 C, mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  exact aggregatedPowerResidueBound_of_uniform hC hη hηδ
    (uniformPowerResidueBound_of_fixedBase hm hR hc)

end SimultaneousPrimitiveRoots
