module

public import SimultaneousPrimitiveRoots.Explicit.KummerZetaGRH
public import SimultaneousPrimitiveRoots.Hecke.EntireUnique

/-!
# GRH ⇒ `MainClaim`, stated with Mathlib's definitions only

`MathlibDedekindGRH K` quantifies over *every* entire function agreeing with
`(s - 1) * NumberField.dedekindZeta K s` on `Re s > 1` (there is exactly one,
`Hecke.eq_dedekindZetaEntire_of_differentiable`), so the hypothesis can be read without trusting
any construction of this project. `MainClaim` (`Statement.lean`) also uses Mathlib's definitions
only.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Explicit

/-- GRH for `ζ_K` in Mathlib's terms: the nontrivial zeros (in `0 < Re s < 1`) of the entire
continuation of `(s - 1) ζ_K(s)` have real part `1/2`. -/
def MathlibDedekindGRH (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ s : ℂ, 1 < s.re → F s = (s - 1) * NumberField.dedekindZeta K s) →
    ∀ ρ : ℂ, F ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2

theorem dedekindZetaGRH_of_mathlibDedekindGRH {K : Type*} [Field K] [NumberField K]
    (h : MathlibDedekindGRH K) : DedekindZetaGRH K :=
  h _ (Hecke.differentiable_dedekindZetaEntire K) (fun _ hs => Hecke.dedekindZetaEntire_eq_mul K hs)

theorem mathlibDedekindGRH_of_dedekindZetaGRH {K : Type*} [Field K] [NumberField K]
    (h : DedekindZetaGRH K) : MathlibDedekindGRH K := by
  intro F hF hFeq ρ hρ h0 h1
  rw [Hecke.eq_dedekindZetaEntire_of_differentiable K hF hFeq] at hρ
  exact h ρ hρ h0 h1

/-- **GRH ⇒ simultaneous primitive roots**, with the hypothesis in Mathlib's terms. -/
theorem mainClaim_of_mathlibGRH
    (h : ∀ (K : Type) [Field K] [NumberField K], MathlibDedekindGRH K) : MainClaim :=
  mainClaim_of_GRH fun K _ _ => dedekindZetaGRH_of_mathlibDedekindGRH (h K)

end SimultaneousPrimitiveRoots.Explicit
