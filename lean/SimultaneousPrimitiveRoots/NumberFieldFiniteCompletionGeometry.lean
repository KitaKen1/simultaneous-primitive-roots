module

public import SimultaneousPrimitiveRoots.RestrictedLocalUnitHaar
public import SimultaneousPrimitiveRoots.FrozenMajorantFubini
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.LinearAlgebra.Countable

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Set Topology TopologicalSpace
open scoped WithZero Valued
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem artinNumberField_countable : Countable K :=
  Finsupp.Countable.of_moduleFinite (R := ℚ)

instance artinNumberFieldFinitePrime_countable : Countable (HeightOneSpectrum (𝓞 K)) := by
  letI := numberField_ideals_countable K
  exact Function.Injective.countable HeightOneSpectrum.asIdeal_injective

theorem artinNumberFieldFinitePlace_countable : Countable (FinitePlace K) :=
  Countable.of_equiv _ FinitePlace.equivHeightOneSpectrum.symm

variable (v : HeightOneSpectrum (𝓞 K))

/-- Use the existing completion and its place-normalized norm, without constructing another field. -/
instance artinNumberFieldFiniteCompletion_nontriviallyNormed :
    NontriviallyNormedField (v.adicCompletion K) :=
  Valued.toNontriviallyNormedField _ ℤᵐ⁰

theorem artinNumberFieldFiniteCompletion_ultrametric :
    IsUltrametricDist (v.adicCompletion K) := inferInstance

theorem artinNumberFieldFiniteCompletion_complete :
    CompleteSpace (v.adicCompletion K) := inferInstance

theorem artinNumberFieldFiniteCompletion_norm_embedding (x : K) :
    ‖FinitePlace.embedding v x‖ = HeightOneSpectrum.adicAbv K v x :=
  FinitePlace.norm_embedding v x

theorem artinNumberFieldFiniteCompletion_norm_le_one_iff (x : v.adicCompletion K) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers K :=
  Valued.toNormedField.norm_le_one_iff

instance artinNumberFieldFiniteCompletion_separable : SeparableSpace (v.adicCompletion K) := by
  letI := artinNumberField_countable K
  exact (HeightOneSpectrum.denseRange_algebraMap K v).separableSpace'

theorem artinNumberFieldFiniteCompletion_secondCountable :
    SecondCountableTopology (v.adicCompletion K) := inferInstance

instance artinNumberFieldFiniteCompletionUnits_secondCountable :
    SecondCountableTopology (v.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem artinNumberFieldFiniteCompletionUnitCutoff_mem (z : (v.adicCompletion K)ˣ) :
    z ∈ artinLocalUnitCutoff (v.adicCompletion K) ↔ ‖(z : v.adicCompletion K)‖ = 1 :=
  artinLocalUnitCutoff_mem _ _

end
end SimultaneousPrimitiveRoots
