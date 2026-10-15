module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter
open scoped Topology
noncomputable section

/-- Finite analytic order gives the exact logarithmic principal part,
including multiple zeros. The remainder is analytic at the center. -/
theorem analyticAt_logDeriv_principal_part {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (hn : analyticOrderAt f s ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      logDeriv f =ᶠ[𝓝[≠] s] fun z =>
        (analyticOrderNatAt f s : ℂ) / (z - s) + g z := by
  obtain ⟨u, hu, hu0, heq⟩ := hf.analyticOrderAt_ne_top.mp hn
  refine ⟨logDeriv u, hu.deriv.div hu hu0, ?_⟩
  have hlog : logDeriv f =ᶠ[𝓝[≠] s]
      logDeriv (fun z => (z - s) ^ analyticOrderNatAt f s • u z) :=
    (logDeriv_congr_nhds heq).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlog, hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hu.continuousAt.eventually_ne hu0 |>.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with z hz hzu hzne hzs
  have hzs0 : z - s ≠ 0 := sub_ne_zero.mpr hzs
  rw [hz]
  change logDeriv (fun w : ℂ => (w - s) ^ analyticOrderNatAt f s * u w) z = _
  rw [logDeriv_mul (f := fun w : ℂ => (w - s) ^ analyticOrderNatAt f s)
    (g := u) z (pow_ne_zero _ hzs0) hzne (by fun_prop) hzu.differentiableAt,
    logDeriv_fun_pow (f := fun w : ℂ => w - s) (by fun_prop)
      (analyticOrderNatAt f s)]
  simp [logDeriv_apply, div_eq_mul_inv]

/-- The residue coefficient of the logarithmic derivative is the actual
natural order. This does not require the zero to be simple. -/
theorem analyticAt_tendsto_mul_logDeriv {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (hn : analyticOrderAt f s ≠ ⊤) :
    Tendsto (fun z => (z - s) * logDeriv f z) (𝓝[≠] s)
      (𝓝 (analyticOrderNatAt f s : ℂ)) := by
  obtain ⟨g, hg, heq⟩ := analyticAt_logDeriv_principal_part hf hn
  have hc : ContinuousAt (fun z => (analyticOrderNatAt f s : ℂ) + (z - s) * g z) s :=
    continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul hg.continuousAt)
  have ht : Tendsto (fun z => (analyticOrderNatAt f s : ℂ) + (z - s) * g z)
      (𝓝[≠] s) (𝓝 (analyticOrderNatAt f s : ℂ)) := by
    simpa using hc.tendsto.mono_left
      (show 𝓝[≠] s ≤ 𝓝 s from nhdsWithin_le_nhds)
  apply ht.congr'
  filter_upwards [heq, eventually_mem_nhdsWithin] with z hz hzs
  have hzs0 : z - s ≠ 0 := sub_ne_zero.mpr hzs
  rw [hz]
  field_simp

end
end SimultaneousPrimitiveRoots
