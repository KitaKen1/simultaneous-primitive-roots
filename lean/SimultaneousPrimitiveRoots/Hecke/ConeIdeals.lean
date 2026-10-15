module

public import SimultaneousPrimitiveRoots.Hecke.PartialZeta

/-!
# Cone points of an ideal and principal ideals

For a nonzero integral ideal `J`, the nonzero points of `J` in Mathlib's fundamental cone are, up to
the `w = #μ_K` roots of unity, the generators of the principal ideals divisible by `J`
(`integerSetEquiv`, `idealSetEquiv`). Hence

`∑_{x ∈ J ∩ cone} g(|N x|) = w · ∑_{(x) ⊆ J principal} g(N (x))`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units Ideal Submodule
open scoped nonZeroDivisors ENNReal

variable {K : Type*} [Field K] [NumberField K]

/-- An integral ideal as a subset of `K`. -/
def idealInK (J : Ideal (𝓞 K)) : Set K := algebraMap (𝓞 K) K '' (J : Set (𝓞 K))

omit [NumberField K] in
theorem idealInK_unit_mul (J : Ideal (𝓞 K)) (u : (𝓞 K)ˣ) (x : K) (hx : x ∈ idealInK J) :
    (u : K) * x ∈ idealInK J := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨(u : 𝓞 K) * a, J.mul_mem_left _ ha, by rw [map_mul]⟩

/-- The cone points of `J` in `K` and Mathlib's `idealSet`. -/
def coneToIdealSet (J : (Ideal (𝓞 K))⁰) :
    coneSet (idealInK (J : Ideal (𝓞 K))) → idealSet K J :=
  fun x => ⟨mixedEmbedding K (x : K), mem_idealSet.mpr ⟨x.2.2.2, by
    obtain ⟨a, ha, hax⟩ := x.2.1
    exact ⟨a, ha, by rw [← hax]⟩⟩⟩

theorem coneToIdealSet_bijective (J : (Ideal (𝓞 K))⁰) :
    Function.Bijective (coneToIdealSet J) := by
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · have h' : mixedEmbedding K (x : K) = mixedEmbedding K (y : K) := congrArg Subtype.val h
    exact Subtype.ext (mixedEmbedding_injective K h')
  · obtain ⟨hC, a, ha, hay⟩ := mem_idealSet.mp y.2
    have hy0 : (algebraMap (𝓞 K) K a) ≠ 0 := by
      intro h0
      have : mixedEmbedding K (algebraMap (𝓞 K) K a) = 0 := by rw [h0, map_zero]
      have hyz : (y : mixedSpace K) = 0 := by rw [← hay]; exact this
      exact hC.2 (by show mixedEmbedding.norm (y : mixedSpace K) = 0; rw [hyz, map_zero])
    refine ⟨⟨algebraMap (𝓞 K) K a, ⟨a, ha, rfl⟩, hy0, by rw [show mixedEmbedding K
      (algebraMap (𝓞 K) K a) = (y : mixedSpace K) from hay]; exact hC⟩, ?_⟩
    exact Subtype.ext hay

/-- `J ∩ cone ≃ {principal ideals divisible by J} × μ_K`. -/
def coneIdealEquiv (J : (Ideal (𝓞 K))⁰) :
    coneSet (idealInK (J : Ideal (𝓞 K))) ≃
      {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} // (J : Ideal (𝓞 K)) ∣ I.1.1} ×
        torsion K :=
  (Equiv.ofBijective _ (coneToIdealSet_bijective J)).trans <|
    (idealSetEquiv K J).trans <|
      (Equiv.subtypeEquiv (integerSetEquiv K) (fun a => by
        rw [integerSetEquiv_apply_fst, dvd_span_singleton]; rfl)).trans <|
        Equiv.prodSubtypeFstEquivSubtypeProd
          (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} => (J : Ideal (𝓞 K)) ∣ I.1.1)

theorem coneIdealEquiv_norm (J : (Ideal (𝓞 K))⁰) (x : coneSet (idealInK (J : Ideal (𝓞 K)))) :
    (absNorm ((coneIdealEquiv J x).1.1.1 : Ideal (𝓞 K)) : ℝ) =
      |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| := by
  set a := (idealSetEquiv K J (Equiv.ofBijective _ (coneToIdealSet_bijective J) x)).1 with ha
  have h1 : ((coneIdealEquiv J x).1.1.1 : Ideal (𝓞 K)) =
      span {(preimageOfMemIntegerSet a : 𝓞 K)} := by
    rw [← integerSetEquiv_apply_fst]
    rfl
  have h2 : mixedEmbedding K ((preimageOfMemIntegerSet a : 𝓞 K) : K) =
      mixedEmbedding K (x : K) := by
    rw [mixedEmbedding_preimageOfMemIntegerSet]
    rfl
  have h3 : (((preimageOfMemIntegerSet a : 𝓞 K)) : K) = (x : K) :=
    mixedEmbedding_injective K h2
  rw [h1, absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, ← Rat.cast_intCast,
    Algebra.coe_norm_int, h3]

/-- **Cone sums of an ideal as sums over principal ideals.** -/
theorem tsum_coneSet_eq (J : (Ideal (𝓞 K))⁰) (g : ℝ → ℝ≥0∞) :
    ∑' x : coneSet (idealInK (J : Ideal (𝓞 K))), g |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| =
      (torsionOrder K : ℝ≥0∞) *
        ∑' I : {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} // (J : Ideal (𝓞 K)) ∣ I.1.1},
          g (absNorm (I.1.1 : Ideal (𝓞 K)) : ℝ) := by
  let := Fintype.ofFinite (torsion K)
  rw [← (coneIdealEquiv J).symm.tsum_eq, ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro I
  have hconst : ∀ ζ : torsion K, g |((Algebra.norm ℚ ((coneIdealEquiv J).symm (I, ζ) : K) : ℚ) : ℝ)|
      = g (absNorm (I.1.1 : Ideal (𝓞 K)) : ℝ) := fun ζ => by
    rw [← coneIdealEquiv_norm, Equiv.apply_symm_apply]
  simp_rw [hconst]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
    Nat.card_eq_fintype_card]

end SimultaneousPrimitiveRoots.Hecke

end
