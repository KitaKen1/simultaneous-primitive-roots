module

public import SimultaneousPrimitiveRoots.ComplexNormKernelHaar

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

/-- The complex product norm, recorded in additive logarithmic coordinates. -/
def artinComplexTotalLogNorm (n : ℕ) : (Fin (n + 1) → ℂˣ) →* Multiplicative ℝ where
  toFun z := Multiplicative.ofAdd (∑ i, artinComplexLogNorm (z i))
  map_one' := by simp [artinComplexLogNorm]
  map_mul' z v := by
    change Multiplicative.ofAdd (∑ i, artinComplexLogNorm (z i * v i)) = _
    simp only [artinComplexLogNorm_mul, Finset.sum_add_distrib]
    rfl

theorem artinComplexTotalLogNorm_continuous (n : ℕ) :
    Continuous (artinComplexTotalLogNorm n) :=
  continuous_ofAdd.comp (continuous_finsetSum _ (fun i _ =>
    artinComplexLogNorm_continuous.comp (continuous_apply i)))

theorem artinComplexTotalLogNorm_exp (n : ℕ) (z : Fin (n + 1) → ℂˣ) :
    Real.exp (Multiplicative.toAdd (artinComplexTotalLogNorm n z)) =
      ∏ i, ‖(z i : ℂ)‖ ^ 2 := by
  change Real.exp (∑ i, artinComplexLogNorm (z i)) = _
  rw [Real.exp_sum]
  simp_rw [artinComplexLogNorm_exp]

theorem artinComplexTotalLogNorm_eq_one_iff (n : ℕ) (z : Fin (n + 1) → ℂˣ) :
    artinComplexTotalLogNorm n z = 1 ↔ z ∈ artinComplexNormKernel n := by
  change (∑ i, artinComplexLogNorm (z i)) = 0 ↔ (∏ i, ‖(z i : ℂ)‖ ^ 2) = 1
  rw [← artinComplexTotalLogNorm_exp]
  exact ⟨fun h => by simp [artinComplexTotalLogNorm, h],
    fun h => Real.exp_injective (h.trans Real.exp_zero.symm)⟩

variable {G : Type*} [Group G]

/-- The finite and complex product norm kernel. The finite norm is exp(toAdd χ). -/
def artinFiniteComplexNorm (χ : G →* Multiplicative ℝ) (n : ℕ) :
    (G × (Fin (n + 1) → ℂˣ)) →* Multiplicative ℝ :=
  (χ.comp (MonoidHom.fst _ _)) *
    ((artinComplexTotalLogNorm n).comp (MonoidHom.snd _ _))

def artinFiniteComplexNormKernel (χ : G →* Multiplicative ℝ) (n : ℕ) :
    Subgroup (G × (Fin (n + 1) → ℂˣ)) := (artinFiniteComplexNorm χ n).ker

theorem artinFiniteComplexNorm_exp (χ : G →* Multiplicative ℝ) (n : ℕ)
    (p : G × (Fin (n + 1) → ℂˣ)) :
    Real.exp (Multiplicative.toAdd (artinFiniteComplexNorm χ n p)) =
      Real.exp (Multiplicative.toAdd (χ p.1)) * (∏ i, ‖(p.2 i : ℂ)‖ ^ 2) := by
  change Real.exp (Multiplicative.toAdd (χ p.1) +
    Multiplicative.toAdd (artinComplexTotalLogNorm n p.2)) = _
  rw [Real.exp_add, artinComplexTotalLogNorm_exp]

variable (χ : G →* Multiplicative ℝ) (U : Subgroup G) (n : ℕ)
  (hU : ∀ g ∈ U, χ g = 1)

/-- A norm-one finite cutoff times the complex norm kernel embeds in the full kernel. -/
def artinFiniteNormCutoffEmbedding :
    (U × artinComplexNormKernel n) →* artinFiniteComplexNormKernel χ n where
  toFun p := ⟨(p.1.1, p.2.1), by
    change χ p.1.1 * artinComplexTotalLogNorm n p.2.1 = 1
    rw [hU _ p.1.2, (artinComplexTotalLogNorm_eq_one_iff n _).mpr p.2.2, one_mul]⟩
  map_one' := by rfl
  map_mul' _ _ := by rfl

theorem artinFiniteNormCutoffEmbedding_range :
    Set.range (artinFiniteNormCutoffEmbedding χ U n hU) =
      {z : artinFiniteComplexNormKernel χ n | z.1.1 ∈ U} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact p.1.2
  · intro hz
    have hn : artinComplexTotalLogNorm n z.1.2 = 1 := by
      have h := z.2
      change χ z.1.1 * artinComplexTotalLogNorm n z.1.2 = 1 at h
      simpa only [hU _ hz, one_mul] using h
    exact ⟨(⟨z.1.1, hz⟩, ⟨z.1.2, (artinComplexTotalLogNorm_eq_one_iff n _).mp hn⟩), rfl⟩

variable [TopologicalSpace G]

theorem artinFiniteComplexNorm_continuous (hχ : Continuous χ) :
    Continuous (artinFiniteComplexNorm χ n) :=
  (hχ.comp continuous_fst).mul
    ((artinComplexTotalLogNorm_continuous n).comp continuous_snd)

theorem artinFiniteComplexNormKernel_isClosed (hχ : Continuous χ) :
    IsClosed (artinFiniteComplexNormKernel χ n : Set (G × (Fin (n + 1) → ℂˣ))) :=
  isClosed_eq (artinFiniteComplexNorm_continuous χ n hχ) continuous_const

theorem artinFiniteNormCutoffEmbedding_isEmbedding :
    Topology.IsEmbedding (artinFiniteNormCutoffEmbedding χ U n hU) :=
  (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.subtypeVal).codRestrict _ _

theorem artinFiniteNormCutoffEmbedding_isOpenEmbedding (hUo : IsOpen (U : Set G)) :
    Topology.IsOpenEmbedding (artinFiniteNormCutoffEmbedding χ U n hU) := by
  refine ⟨artinFiniteNormCutoffEmbedding_isEmbedding χ U n hU, ?_⟩
  rw [artinFiniteNormCutoffEmbedding_range]
  exact hUo.preimage (continuous_fst.comp continuous_subtype_val)

end
end SimultaneousPrimitiveRoots
