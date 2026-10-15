module

public import SimultaneousPrimitiveRoots.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Hecke.GaussianMainTerm

/-!
# Abstract entire zero data (step D6)

The finite-contour machinery of the project is stated for the entire continuation `H` of a zeta
quotient `ζ_K / ζ_L` (`NumberFieldEntireFullQuotientContinuation K L H`). Apart from the Dirichlet
series identification on `Re s > 1`, it only uses three consequences of that hypothesis:

* `H` is entire;
* `H` has no zeros on `Re s ≥ 1`;
* the centre bound `log ‖H 2‖ ≥ -4 [L : ℚ]`.

`EntireZeroData K L H` packages exactly these, together with the identification
`H s = (s - 1) ζ_K(s)` on `Re s > 1` that replaces `H = ζ_K/ζ_L` (the field `L` only enters
through the centre constant, so that every statement of the machinery is a drop-in replacement). The files in `Explicit/` restate the
quotient-dependent declarations with this hypothesis, in the namespace
`SimultaneousPrimitiveRoots.Explicit`, so that the machinery applies to the entire function
`F_K(s) = (s - 1) ζ_K(s)` itself (`dedekindZetaEntire_entireZeroData`), with no Aramata–Brauer
input.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField IsDedekindDomain Filter Metric
open scoped Topology
noncomputable section
open Classical

/-- Abstract replacement of the entire zeta quotient. -/
def EntireZeroData (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    (H : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ H Set.univ ∧ (∀ s : ℂ, 1 ≤ s.re → H s ≠ 0) ∧
    -(4 * (Module.finrank ℚ L : ℝ)) ≤ Real.log ‖H 2‖ ∧
    ∀ s : ℂ, 1 < s.re → H s = (s - 1) * dedekindZeta K s

/-- **`F_K = (s - 1) ζ_K(s)` satisfies `EntireZeroData`** for every auxiliary field `L`. -/
theorem dedekindZetaEntire_entireZeroData (K L : Type*) [Field K] [Field L] [NumberField K]
    [NumberField L] : EntireZeroData K L (Hecke.dedekindZetaEntire K) := by
  refine ⟨fun z _ => (Hecke.differentiable_dedekindZetaEntire K).analyticAt z,
    fun s hs => Hecke.dedekindZetaEntire_ne_zero K hs, ?_,
    fun s hs => Hecke.dedekindZetaEntire_eq_mul K hs⟩
  have h1 := Hecke.one_le_norm_dedekindZetaEntire_two K
  have hlog : 0 ≤ Real.log ‖Hecke.dedekindZetaEntire K 2‖ := Real.log_nonneg h1
  have : (0 : ℝ) ≤ 4 * (Module.finrank ℚ L : ℝ) := by positivity
  linarith

theorem numberFieldEntireFullQuotientContinuation_positive (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) : EntireZeroData K L H := hH

theorem numberFieldFullQuotientContinuation_ne_zero_two (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) : H 2 ≠ 0 :=
  hH.2.1 2 (by norm_num)

theorem numberFieldFullQuotientContinuation_log_norm_two_lower (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) :
    -(4 * (Module.finrank ℚ L : ℝ)) ≤ Real.log ‖H 2‖ :=
  hH.2.2.1

theorem numberFieldFullQuotientContinuation_norm_two_lower (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) :
    Real.exp (-(4 * (Module.finrank ℚ L : ℝ))) ≤ ‖H 2‖ := by
  have hp : 0 < ‖H 2‖ := norm_pos_iff.mpr
    (numberFieldFullQuotientContinuation_ne_zero_two K L hH)
  simpa only [Real.exp_log hp] using
    Real.exp_le_exp.mpr (numberFieldFullQuotientContinuation_log_norm_two_lower K L hH)

theorem numberFieldEntireFullQuotientContinuation_boundary_ne_zero (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {s : ℂ} (hs : 1 ≤ s.re) : H s ≠ 0 :=
  hH.2.1 s hs

/-- The logarithmic derivative on `Re s > 1`: `H'/H = 1/(s - 1) + Z'/Z` with
`Z = numberFieldIncompleteZeta K ∅`. -/
theorem entireZeroData_logDeriv_eq {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] {H : ℂ → ℂ} (hH : EntireZeroData K L H) {s : ℂ} (hs : 1 < s.re) :
    logDeriv H s = 1 / (s - 1) + logDeriv (numberFieldIncompleteZeta K ∅) s := by
  have heq : H =ᶠ[𝓝 s] Hecke.dedekindZetaEntire K :=
    eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
      (fun z hz => by rw [hH.2.2.2 z hz, Hecke.dedekindZetaEntire_eq_mul K hz])
  rw [(logDeriv_congr_nhds heq).eq_of_nhds, Hecke.logDeriv_dedekindZetaEntire K hs]

end
end SimultaneousPrimitiveRoots.Explicit
