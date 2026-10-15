module

public import SimultaneousPrimitiveRoots.Hecke.EntireBasics

/-!
# Uniqueness of the entire continuation of `(s - 1) ζ_K(s)`

`dedekindZetaEntire K` is built from choices (class representatives, bases), but any entire
function agreeing with `(s - 1) ζ_K(s)` on `Re s > 1` is equal to it
(`eq_dedekindZetaEntire_of_differentiable`). Hence hypotheses phrased with
`dedekindZetaEntire K`, such as GRH for `ζ_K`, do not depend on these choices.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Filter
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- **Uniqueness:** an entire function equal to `(s - 1) ζ_K(s)` on `Re s > 1` is
`dedekindZetaEntire K`. -/
theorem eq_dedekindZetaEntire_of_differentiable {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h : ∀ s : ℂ, 1 < s.re → F s = (s - 1) * dedekindZeta K s) :
    F = dedekindZetaEntire K := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hGa : AnalyticOnNhd ℂ (dedekindZetaEntire K) Set.univ :=
    fun z _ => (differentiable_dedekindZetaEntire K).analyticAt z
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : F =ᶠ[𝓝 (2 : ℂ)] dedekindZetaEntire K := by
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
    rw [h s hs, dedekindZetaEntire_eq_mul K hs]
  funext z
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa isPreconnected_univ (Set.mem_univ _) heq
    (Set.mem_univ z)

end SimultaneousPrimitiveRoots.Hecke

end
