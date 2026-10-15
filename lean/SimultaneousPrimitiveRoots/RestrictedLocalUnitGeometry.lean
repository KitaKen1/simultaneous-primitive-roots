module

public import SimultaneousPrimitiveRoots.NonarchimedeanUnitCutoff
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Set Filter Topology
open scoped RestrictedProduct
noncomputable section

variable {ι : Type*} (F : ι → Type*)
  [∀ i, NontriviallyNormedField (F i)] [∀ i, IsUltrametricDist (F i)]

/-- The multiplicative restricted product of an arbitrary family of actual local fields. -/
abbrev ArtinRestrictedLocalUnits :=
  Πʳ i, [(F i)ˣ, artinLocalUnitCutoff (F i)]

instance artinRestrictedLocalUnitOpen :
    Fact (∀ i, IsOpen (artinLocalUnitCutoff (F i) : Set (F i)ˣ)) :=
  ⟨fun i => artinLocalUnitCutoff_isOpen (F i)⟩

/-- The full integral-unit cutoff, rather than a finite product of places. -/
def artinRestrictedLocalUnitCutoff : Subgroup (ArtinRestrictedLocalUnits F) where
  carrier := {z | ∀ i, z i ∈ artinLocalUnitCutoff (F i)}
  one_mem' := fun i => (artinLocalUnitCutoff (F i)).one_mem
  mul_mem' hx hy i := (artinLocalUnitCutoff (F i)).mul_mem (hx i) (hy i)
  inv_mem' hx i := (artinLocalUnitCutoff (F i)).inv_mem (hx i)

theorem artinRestrictedLocalUnitCutoff_mem (z : ArtinRestrictedLocalUnits F) :
    z ∈ artinRestrictedLocalUnitCutoff F ↔ ∀ i, ‖(z i : F i)‖ = 1 := by
  simp [artinRestrictedLocalUnitCutoff, artinLocalUnitCutoff_mem]

def artinRestrictedLocalUnitStructureMap :
    (∀ i, artinLocalUnitCutoff (F i)) →* ArtinRestrictedLocalUnits F where
  toFun := RestrictedProduct.structureMap _ _ cofinite
  map_one' := rfl
  map_mul' _ _ := rfl

theorem artinRestrictedLocalUnitStructureMap_range :
    range (artinRestrictedLocalUnitStructureMap F) =
      (artinRestrictedLocalUnitCutoff F : Set (ArtinRestrictedLocalUnits F)) :=
  RestrictedProduct.range_structureMap _ _

theorem artinRestrictedLocalUnitStructureMap_isOpenEmbedding :
    IsOpenEmbedding (artinRestrictedLocalUnitStructureMap F) :=
  RestrictedProduct.isOpenEmbedding_structureMap
    (fun i => artinLocalUnitCutoff_isOpen (F i))

theorem artinRestrictedLocalUnitCutoff_isOpen :
    IsOpen (artinRestrictedLocalUnitCutoff F : Set (ArtinRestrictedLocalUnits F)) :=
  RestrictedProduct.isOpen_forall_mem (fun i => artinLocalUnitCutoff_isOpen (F i))

theorem artinRestrictedLocalUnitCutoff_isCompact [∀ i, ProperSpace (F i)] :
    IsCompact (artinRestrictedLocalUnitCutoff F : Set (ArtinRestrictedLocalUnits F)) := by
  letI : ∀ i, CompactSpace (artinLocalUnitCutoff (F i)) := fun i =>
    isCompact_iff_compactSpace.mp (artinLocalUnitCutoff_isCompact (F i))
  rw [← artinRestrictedLocalUnitStructureMap_range]
  exact isCompact_range (artinRestrictedLocalUnitStructureMap_isOpenEmbedding F).continuous

theorem artinRestrictedLocalUnits_isTopologicalGroup :
    IsTopologicalGroup (ArtinRestrictedLocalUnits F) := inferInstance

instance artinRestrictedLocalUnits_locallyCompact [∀ i, ProperSpace (F i)] :
    LocallyCompactSpace (ArtinRestrictedLocalUnits F) := by
  letI : ∀ i, CompactSpace (artinLocalUnitCutoff (F i)) := fun i =>
    isCompact_iff_compactSpace.mp (artinLocalUnitCutoff_isCompact (F i))
  infer_instance

/-- Countably many places have a countable cover by finite exceptional-place charts. -/
instance artinRestrictedLocalUnits_secondCountable [Countable ι]
    [∀ i, SecondCountableTopology (F i)ˣ] :
    SecondCountableTopology (ArtinRestrictedLocalUnits F) := by
  classical
  let R := fun i => (F i)ˣ
  let A := fun i => (artinLocalUnitCutoff (F i) : Set (F i)ˣ)
  have hS (s : Finset ι) : cofinite ≤ 𝓟 (s : Set ι)ᶜ := by
    rw [le_principal_iff, mem_cofinite]
    simpa using s.finite_toSet
  let f (s : Finset ι) := RestrictedProduct.inclusion R A (hS s)
  have hf (s : Finset ι) : IsOpenEmbedding (f s) :=
    RestrictedProduct.isOpenEmbedding_inclusion_principal
      (fun i => artinLocalUnitCutoff_isOpen (F i)) (hS s)
  letI (s : Finset ι) : SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 (s : Set ι)ᶜ]) :=
    RestrictedProduct.isEmbedding_coe_of_principal.isInducing.secondCountableTopology
  letI (s : Finset ι) : SecondCountableTopology (range (f s)) :=
    (hf s).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun s : Finset ι => range (f s))
    (fun s => (hf s).isOpen_range)
  apply Set.eq_univ_of_forall
  intro z
  have hb : {i | z i ∉ A i}.Finite := eventually_cofinite.mp z.2
  apply mem_iUnion.mpr
  refine ⟨hb.toFinset, ?_⟩
  change z ∈ range (RestrictedProduct.inclusion R A (hS hb.toFinset))
  rw [RestrictedProduct.range_inclusion]
  change ∀ i ∈ (hb.toFinset : Set ι)ᶜ, z i ∈ A i
  intro i hi
  simpa using hi

end
end SimultaneousPrimitiveRoots
