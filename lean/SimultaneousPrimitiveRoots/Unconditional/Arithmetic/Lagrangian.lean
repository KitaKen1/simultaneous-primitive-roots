module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Lagrangian subspaces and isotropic complements ([A] `lem:balanced-generators`, linear algebra)

[A] (`A-02:0193–0207`) applies "symplectic linear algebra" to the Hilbert pairing on
`F_S^× / F_S^{×ℓ}` (`ℓ = 2, 3`): the image `E` of the `S`-units is isotropic of half the dimension,
hence its own orthogonal, and it has an isotropic complement `B`. This file proves both facts for a
nondegenerate alternating bilinear form on a finite-dimensional vector space over any field, in
particular over `ZMod 2`, where an alternating form is not determined by halving its symmetric
part:

* `orthogonal_eq_self_of_isotropic`: an isotropic subspace of half the dimension is its own
  orthogonal;
* `exists_isotropic_isCompl`: it has an isotropic complement.

For the complement, take any complement `C` with basis `(cᵢ)`; the pairing identifies `E` with the
dual of `C`, and `W = {c + φ c}` is isotropic for the `φ : C → E` with `B(φ cᵢ, cⱼ) = -B(cᵢ, cⱼ)`
for `i < j` and `0` for `i ≥ j` (the upper-triangular half of the form).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

open Module LinearMap LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V}

/-- **An isotropic subspace of half the dimension is its own orthogonal.** -/
theorem orthogonal_eq_self_of_isotropic (hB : B.Nondegenerate) {E : Submodule K V}
    (hE : ∀ x ∈ E, ∀ y ∈ E, B x y = 0) (hdim : 2 * finrank K E = finrank K V) :
    B.orthogonal E = E := by
  have hle : E ≤ B.orthogonal E := fun x hx =>
    (mem_orthogonal_iff).mpr fun n hn => hE n hn x hx
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_orthogonal hB]
  omega

/-- **A Lagrangian subspace has an isotropic complement**, over any field: if `E` is isotropic
for a nondegenerate alternating form and has half the dimension, there is an isotropic `W` with
`V = E ⊕ W`. -/
theorem exists_isotropic_isCompl (hB : B.Nondegenerate) (halt : B.IsAlt) {E : Submodule K V}
    (hE : ∀ x ∈ E, ∀ y ∈ E, B x y = 0) (hdim : 2 * finrank K E = finrank K V) :
    ∃ W : Submodule K V, IsCompl E W ∧ ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl E
  have hdimC : finrank K C = finrank K E := by
    have := Submodule.finrank_add_eq_of_isCompl hC
    omega
  -- the pairing `E → C^*`, `e ↦ B e ·`
  let ψ : E →ₗ[K] Module.Dual K C := B.compl₁₂ E.subtype C.subtype
  have hψ : ∀ (e : E) (c : C), ψ e c = B e c := fun _ _ => rfl
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro e he
    rw [LinearMap.mem_ker] at he
    have hzero : ∀ v : V, B e v = 0 := by
      intro v
      have hv : v ∈ E ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add, hE e e.2 x hx, zero_add]
      exact (LinearMap.congr_fun he ⟨y, hy⟩ :)
    exact Subtype.ext (hB.1 e hzero)
  have hψbij : Function.Bijective ψ := by
    refine ⟨hψinj, ?_⟩
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hψinj
    · rw [Subspace.dual_finrank_eq, hdimC]
  let ψe : E ≃ₗ[K] Module.Dual K C := LinearEquiv.ofBijective ψ hψbij
  -- a basis of `C` and the upper-triangular correction
  let b := Module.finBasis K C
  let g : Fin (finrank K C) → Module.Dual K C := fun i =>
    b.constr K fun j => if i < j then -B (b i) (b j) else 0
  have hg : ∀ i j, g i (b j) = if i < j then -B (b i) (b j) else 0 := fun i j => by
    simp only [g, Basis.constr_basis]
  let φ : C →ₗ[K] E := b.constr K fun i => ψe.symm (g i)
  have hφ : ∀ i (c : C), B (φ (b i) : V) c = g i c := fun i c => by
    have h : φ (b i) = ψe.symm (g i) := by simp only [φ, Basis.constr_basis]
    rw [h, ← hψ, show ψ (ψe.symm (g i)) = ψe (ψe.symm (g i)) from rfl,
      LinearEquiv.apply_symm_apply]
  -- `W` is the graph of `φ` over `C`
  let T : C →ₗ[K] V := C.subtype + E.subtype ∘ₗ φ
  have hT : ∀ c : C, T c = (c : V) + (φ c : V) := fun _ => rfl
  refine ⟨LinearMap.range T, ⟨?_, ?_⟩, ?_⟩
  · -- `E ∩ W = 0`
    rw [Submodule.disjoint_def]
    rintro x hxE ⟨c, rfl⟩
    rw [hT] at hxE ⊢
    have hcE : (c : V) ∈ E := by
      have := E.sub_mem hxE (φ c).2
      simpa using this
    have hc0 : (c : V) = 0 := (Submodule.disjoint_def.mp hC.disjoint) _ hcE c.2
    have hc : c = 0 := Subtype.ext hc0
    rw [hc, map_zero]
    simp
  · -- `E + W = V`
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v ∈ E ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have hdecomp : x + y = (x - (φ ⟨y, hy⟩ : V)) + T ⟨y, hy⟩ := by
      rw [hT]
      abel
    rw [hdecomp]
    exact Submodule.add_mem_sup (E.sub_mem hx (φ ⟨y, hy⟩).2) (LinearMap.mem_range_self T _)
  · -- `W` is isotropic: check `B (T bᵢ) (T bⱼ) = 0` on the basis
    have hQ : B.compl₁₂ T T = 0 := by
      refine LinearMap.ext_basis b b fun i j => ?_
      simp only [LinearMap.compl₁₂_apply, LinearMap.zero_apply, hT, map_add,
        LinearMap.add_apply]
      have h1 : B (φ (b i) : V) (b j : V) = g i (b j) := hφ i (b j)
      have h2 : B (b i : V) (φ (b j) : V) = -g j (b i) := by
        rw [← hφ j (b i), ← halt.neg_eq]
      have h3 : B (φ (b i) : V) (φ (b j) : V) = 0 := hE _ (φ (b i)).2 _ (φ (b j)).2
      rw [h1, h2, h3, hg, hg]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [if_pos hij, if_neg (not_lt.mpr hij.le)]
        ring
      · rw [if_neg (lt_irrefl _), halt.self_eq_zero]
        ring
      · rw [if_neg (not_lt.mpr hij.le), if_pos hij, ← halt.neg_eq]
        ring
    rintro x ⟨c, rfl⟩ y ⟨c', rfl⟩
    have := LinearMap.congr_fun₂ hQ c c'
    simpa only [LinearMap.compl₁₂_apply, LinearMap.zero_apply] using this

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
