module

public import SimultaneousPrimitiveRoots.Unconditional.Assembly
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff

/-!
# The Hecke zero-free strip of [A], as a Lean proposition

[A, Theorem 1.2] (`thm:hecke-zero-free`, "Primitive roots for every admissible integer base",
OpenAI, 4 Oct 2026, unrefereed): *for every cyclotomic field `F ⊇ μ₁₂` and every finite-order
Hecke character `η` of `F`, the meromorphic continuation of `L_F(s, η)` has no zeros in
`Re s > 1 - 10⁻⁶`* (the principal character included, its pole at `s = 1` permitted).

`HeckeZeroFreeStrip δ` states this in ray class form with Tau Ceti's ray class characters:

* a finite-order Hecke character is a character of a ray class group (classical, e.g.
  Neukirch VI.6); the cyclotomic fields containing `μ₁₂` are the `ℚ(ζ_m)` with `12 ∣ m`;
* the `L`-series of a ray class character of modulus `𝔪` differs from the primitive `L`-function
  by finitely many Euler factors `1 - η(𝔭) N𝔭^{-s}`, none of which vanishes on `Re s > 0`;
* "the continuation has no zeros" is stated for every holomorphic continuation to the punctured
  half-plane `{Re s > 1 - δ} \ {1}` (connected, so the continuation is unique when it exists).

This file only *states* the proposition. It is neither assumed nor proved here, and no axiom is
added: the unconditional route needs a proof of `HeckeZeroFreeStrip (10⁻⁶)` (the content of [A],
§§2–6 and Appendix A, of quasi-Riemann-hypothesis strength: with `F = ℚ(ζ₁₂)` and `η = 1` it
gives `ζ(s) ≠ 0` for `Re s > 1 - δ`), and then the classical bridge to the Kummer zero gap.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Unconditional

open TauCeti TauCeti.GlobalNumberFields NumberField
open scoped NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- The ideal coefficients of a ray class character: `χ(𝔞)` on the integral ideals prime to the
modulus, `0` on the others. -/
def rayCoeff {𝔪 : Modulus K} (χ : RayClassCharacter 𝔪) : IdealArithmeticFunction K :=
  fun I => if h : (I : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪 then
    ((χ.onIdeals ⟨I, h⟩ : ℂˣ) : ℂ) else 0

/-- The `L`-series of a ray class character, `∑_{(𝔞, 𝔪) = 1} χ(𝔞) N𝔞^{-s}`, as a Dirichlet series
in the absolute norm. -/
def rayClassLSeries {𝔪 : Modulus K} (χ : RayClassCharacter 𝔪) (s : ℂ) : ℂ :=
  LSeries (normCoeff K (rayCoeff χ)) s

/-- `L(s, χ)` has no zeros in `Re s > 1 - δ`: every holomorphic continuation of the `L`-series
from `Re s > 1` to `{Re s > 1 - δ} \ {1}` is nonvanishing there. -/
def RayClassLZeroFree {𝔪 : Modulus K} (χ : RayClassCharacter 𝔪) (δ : ℝ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f {s : ℂ | 1 - δ < s.re ∧ s ≠ 1} →
    (∀ s : ℂ, 1 < s.re → f s = rayClassLSeries χ s) →
      ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 → f s ≠ 0

/-- **[A, Theorem 1.2] in ray class form.** For every `m` with `12 ∣ m`, every number field `F`
that is an `m`-th cyclotomic extension of `ℚ`, every modulus `𝔪` of `F` and every ray class
character `χ` of `𝔪`, the `L`-function of `χ` has no zeros in `Re s > 1 - δ`. -/
def HeckeZeroFreeStrip (δ : ℝ) : Prop :=
  ∀ (m : ℕ) [NeZero m], 12 ∣ m →
    ∀ (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F],
      ∀ (𝔪 : Modulus F) (χ : RayClassCharacter 𝔪), RayClassLZeroFree χ δ

end

end SimultaneousPrimitiveRoots.Unconditional
