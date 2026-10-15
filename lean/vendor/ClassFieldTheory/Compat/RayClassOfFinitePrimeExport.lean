/-
Compatibility module (this project, not upstream ClassFieldTheory).

openai/math's `ClassFieldTheory-lean4341.patch` turns the private lemma
`finitePrimeFractionalIdeal_mem_primeTo` of
`ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassOfFinitePrime.lean` into a public
one, and `cadamcat/artin-primitive-roots-lean4` uses it. This project vendors the unpatched file
(changing it would rebuild the whole reciprocity closure), so the lemma is restated here publicly,
with the upstream statement and proof (N. Yamaguchi, Apache-2.0).
-/
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- The fractional ideal of a finite prime away from the modulus is prime to the modulus. -/
lemma finitePrimeFractionalIdeal_mem_primeTo
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    finitePrimeFractionalIdeal v ∈ rayClassPrimeToIdeals m := by
  intro w hw
  exact FractionalIdeal.count_maximal_coprime K w fun h => (h ▸ hv) hw

end ClassFieldTheory
