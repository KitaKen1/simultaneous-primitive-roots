module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SimultaneousPrimitiveRoots

open MeasureTheory Filter Asymptotics Set Complex
open scoped Topology
noncomputable section

/-- The actual endpoint estimates for a probe. The small endpoint is flat to
every real power; no holomorphic continuation or zero exclusion is an input. -/
def MellinProbeBounds (f : ℝ → ℂ) (α : ℝ) : Prop :=
  LocallyIntegrableOn f (Ioi 0) ∧
    f =O[atTop] (fun x : ℝ => x ^ α) ∧
    ∀ b : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ b)

/-- The transform in A-06, with C(s)=s-β. -/
def probeMellinTransform (f : ℝ → ℂ) (β : ℝ) (s : ℂ) : ℂ :=
  mellin f ((β : ℂ) - s)

theorem probeMellinTransform_convergent {f : ℝ → ℂ} {α β : ℝ}
    (hf : MellinProbeBounds f α) {s : ℂ} (hs : α + β < s.re) :
    MellinConvergent f ((β : ℂ) - s) := by
  apply mellinConvergent_of_isBigO_rpow (a := -α)
    (b := (((β : ℂ) - s).re - 1)) hf.1
  · simpa using hf.2.1
  · simp only [sub_re, ofReal_re]
    linarith
  · exact hf.2.2 _
  · linarith

theorem probeMellinTransform_differentiableAt {f : ℝ → ℂ} {α β : ℝ}
    (hf : MellinProbeBounds f α) {s : ℂ} (hs : α + β < s.re) :
    DifferentiableAt ℂ (probeMellinTransform f β) s := by
  have hm : DifferentiableAt ℂ (mellin f) ((β : ℂ) - s) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a := -α)
      (b := (((β : ℂ) - s).re - 1)) hf.1
    · simpa using hf.2.1
    · simp only [sub_re, ofReal_re]
      linarith
    · exact hf.2.2 _
    · linarith
  exact hm.comp s (differentiableAt_id.const_sub (β : ℂ))

theorem probeMellinTransform_analyticOnNhd {f : ℝ → ℂ} {α β : ℝ}
    (hf : MellinProbeBounds f α) :
    AnalyticOnNhd ℂ (probeMellinTransform f β) {s : ℂ | α + β < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const continuous_re)
  intro s hs
  exact (probeMellinTransform_differentiableAt hf hs).differentiableWithinAt

/-- Multiplying through by the holomorphic denominator avoids meromorphic
identity arguments. Agreement on a right half-plane suffices. -/
theorem probeMellinTransform_mul_eq {f : ℝ → ℂ} {α β σ : ℝ}
    (hf : MellinProbeBounds f α) {L N : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L {s : ℂ | α + β < s.re})
    (hN : AnalyticOnNhd ℂ N {s : ℂ | α + β < s.re})
    (heq : ∀ s : ℂ, σ < s.re → probeMellinTransform f β s * L s = N s) :
    EqOn (fun s => probeMellinTransform f β s * L s) N
      {s : ℂ | α + β < s.re} := by
  let r := max σ (α + β) + 1
  have hrσ : σ < r := by dsimp [r]; linarith [le_max_left σ (α + β)]
  have hrα : α + β < r := by dsimp [r]; linarith [le_max_right σ (α + β)]
  have han := (probeMellinTransform_analyticOnNhd hf).mul hL
  apply han.eqOn_of_preconnected_of_eventuallyEq hN (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (r : ℂ)) (by simpa using hrα)
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (show (r : ℂ) ∈ {s : ℂ | σ < s.re} by simpa using hrσ)] with s hs
  exact heq s hs

/-- Zero exclusion is derived from the probe endpoint bounds and an actual
right-line identity. The nonzero numerator must be checked independently. -/
theorem nonvanishing_of_mellin_probe {f : ℝ → ℂ} {α β σ : ℝ}
    (hf : MellinProbeBounds f α) {L N : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L {s : ℂ | α + β < s.re})
    (hN : AnalyticOnNhd ℂ N {s : ℂ | α + β < s.re})
    (hne : ∀ s : ℂ, α + β < s.re → N s ≠ 0)
    (heq : ∀ s : ℂ, σ < s.re → probeMellinTransform f β s * L s = N s)
    {s : ℂ} (hs : α + β < s.re) : L s ≠ 0 := by
  intro hz
  have h := probeMellinTransform_mul_eq hf hL hN heq hs
  change probeMellinTransform f β s * L s = N s at h
  rw [hz, mul_zero] at h
  exact hne s hs h.symm

end
end SimultaneousPrimitiveRoots
