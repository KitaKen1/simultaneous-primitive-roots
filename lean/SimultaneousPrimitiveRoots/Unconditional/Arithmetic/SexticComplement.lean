module

public import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PairingComplement
public import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PowerClasses

/-!
# Combining the quadratic and cubic isotropic complements

The group-theoretic conclusion of [A, `lem:balanced-generators`, A-02:0203–0207].
The canonical CRT on power classes transports the unit image to the product of
its two prime-exponent images. The third and second powers of the sextic pairing
are assumed to agree with the quadratic and cubic pairings, respectively.

The result constructs an isotropic complement to the sixth-power unit image and
proves self-orthogonality. The arithmetic inputs (the local Hilbert pairings,
their compatibility, nondegeneracy and the unit-image cardinalities) remain
explicit hypotheses; this file does not claim to construct those inputs.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

private theorem isCompl_prod {V₁ V₂ : Type*} [CommGroup V₁] [CommGroup V₂]
    {E₁ B₁ : Subgroup V₁} {E₂ B₂ : Subgroup V₂}
    (h₁ : IsCompl E₁ B₁) (h₂ : IsCompl E₂ B₂) :
    IsCompl (E₁.prod E₂) (B₁.prod B₂) := by
  refine ⟨Subgroup.disjoint_def.mpr (fun {x} hx hy => ?_), ?_⟩
  · exact Prod.ext (Subgroup.disjoint_def.mp h₁.disjoint hx.1 hy.1)
      (Subgroup.disjoint_def.mp h₂.disjoint hx.2 hy.2)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx₁ : x.1 ∈ E₁ ⊔ B₁ := by rw [h₁.sup_eq_top]; trivial
    have hx₂ : x.2 ∈ E₂ ⊔ B₂ := by rw [h₂.sup_eq_top]; trivial
    obtain ⟨e₁, he₁, b₁, hb₁, hmul₁⟩ := Subgroup.mem_sup.mp hx₁
    obtain ⟨e₂, he₂, b₂, hb₂, hmul₂⟩ := Subgroup.mem_sup.mp hx₂
    exact Subgroup.mem_sup.mpr
      ⟨(e₁, e₂), ⟨he₁, he₂⟩, (b₁, b₂), ⟨hb₁, hb₂⟩, Prod.ext hmul₁ hmul₂⟩

/-- **CRT combines two self-orthogonal subgroups and their isotropic complements.**
The sextic pairing is detected by its quadratic (third power) and cubic (second
power) components. -/
theorem combine_isotropic_complements
    {V V₂ V₃ μ μ₂ μ₃ : Type*} [CommGroup V] [CommGroup V₂] [CommGroup V₃]
    [CommGroup μ] [CommGroup μ₂] [CommGroup μ₃]
    (e : V ≃* V₂ × V₃) (H : V →* V →* μ)
    (H₂ : V₂ →* V₂ →* μ₂) (H₃ : V₃ →* V₃ →* μ₃)
    (j₂ : μ₂ →* μ) (j₃ : μ₃ →* μ)
    (hj₂ : Function.Injective j₂) (hj₃ : Function.Injective j₃)
    (hc₂ : ∀ x y, H x y ^ 3 = j₂ (H₂ (e x).1 (e y).1))
    (hc₃ : ∀ x y, H x y ^ 2 = j₃ (H₃ (e x).2 (e y).2))
    {E : Subgroup V} {E₂ : Subgroup V₂} {E₃ : Subgroup V₃}
    (hE : E.map e.toMonoidHom = E₂.prod E₃)
    (hself₂ : ∀ x, (∀ y ∈ E₂, H₂ x y = 1) → x ∈ E₂)
    (hself₃ : ∀ x, (∀ y ∈ E₃, H₃ x y = 1) → x ∈ E₃)
    {B₂ : Subgroup V₂} {B₃ : Subgroup V₃}
    (hB₂ : IsCompl E₂ B₂) (hB₃ : IsCompl E₃ B₃)
    (hiso₂ : ∀ x ∈ B₂, ∀ y ∈ B₂, H₂ x y = 1)
    (hiso₃ : ∀ x ∈ B₃, ∀ y ∈ B₃, H₃ x y = 1) :
    (∀ x, (∀ y ∈ E, H x y = 1) → x ∈ E) ∧
      ∃ B : Subgroup V, IsCompl E B ∧ ∀ x ∈ B, ∀ y ∈ B, H x y = 1 := by
  have hmem : ∀ x : V, x ∈ E ↔ e x ∈ E₂.prod E₃ := by
    intro x
    rw [← hE]
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm
  refine ⟨fun x hx => ?_, ?_⟩
  · apply (hmem x).mpr
    constructor
    · apply hself₂
      intro y hy
      have hyE : e.symm (y, 1) ∈ E :=
        (hmem _).mpr (by
          simpa only [e.apply_symm_apply, Subgroup.mem_prod] using And.intro hy E₃.one_mem)
      apply hj₂
      have h := (hc₂ x (e.symm (y, 1))).symm
      simpa only [e.apply_symm_apply, hx _ hyE, one_pow, map_one] using h
    · apply hself₃
      intro y hy
      have hyE : e.symm (1, y) ∈ E :=
        (hmem _).mpr (by
          simpa only [e.apply_symm_apply, Subgroup.mem_prod] using And.intro E₂.one_mem hy)
      apply hj₃
      have h := (hc₃ x (e.symm (1, y))).symm
      simpa only [e.apply_symm_apply, hx _ hyE, one_pow, map_one] using h
  · let B : Subgroup V := (B₂.prod B₃).comap e.toMonoidHom
    have hback : (e.comapSubgroup) (E₂.prod E₃) = E := by
      ext x
      exact (hmem x).symm
    have hcomp := (e.comapSubgroup).isCompl (isCompl_prod hB₂ hB₃)
    rw [hback] at hcomp
    refine ⟨B, hcomp, fun x hx y hy => ?_⟩
    change e x ∈ B₂.prod B₃ at hx
    change e y ∈ B₂.prod B₃ at hy
    have hpow₃ : H x y ^ 3 = 1 := by rw [hc₂, hiso₂ _ hx.1 _ hy.1, map_one]
    have hpow₂ : H x y ^ 2 = 1 := by rw [hc₃, hiso₃ _ hx.2 _ hy.2, map_one]
    exact (pow_eq_one_iff_of_coprime (show Nat.Coprime 2 3 by decide)).mp ⟨hpow₂, hpow₃⟩

/-- **An isotropic complement to the unit image in sixth-power classes.**
All prime-exponent inputs are stated on the canonical square and cube quotients.
This is the CRT assembly in [A-02:0203–0207]. -/
theorem exists_sextic_isotropic_compl
    {G U μ μ₂ μ₃ : Type*} [CommGroup G] [CommGroup U]
    [CommGroup μ] [CommGroup μ₂] [CommGroup μ₃]
    [Finite (PowerClass G 2)] [Finite (PowerClass G 3)]
    (f : U →* G) (H : PowerClass G 6 →* PowerClass G 6 →* μ)
    (H₂ : PowerClass G 2 →* PowerClass G 2 →* μ₂)
    (H₃ : PowerClass G 3 →* PowerClass G 3 →* μ₃)
    (e₂ : μ₂ ≃* Multiplicative (ZMod 2)) (e₃ : μ₃ ≃* Multiplicative (ZMod 3))
    (j₂ : μ₂ →* μ) (j₃ : μ₃ →* μ)
    (hj₂ : Function.Injective j₂) (hj₃ : Function.Injective j₃)
    (hc₂ : ∀ x y, H x y ^ 3 =
      j₂ (H₂ (powerClassReduce G 2 3 x) (powerClassReduce G 2 3 y)))
    (hc₃ : ∀ x y, H x y ^ 2 =
      j₃ (H₃ (powerClassReduce G 3 2 x) (powerClassReduce G 3 2 y)))
    (hnd₂ : ∀ x, (∀ y, H₂ x y = 1) → x = 1)
    (hnd₃ : ∀ x, (∀ y, H₃ x y = 1) → x = 1)
    (halt₂ : ∀ x, H₂ x x = 1) (halt₃ : ∀ x, H₃ x x = 1)
    (hE₂ : ∀ x ∈ (powerClassMap f 2).range, ∀ y ∈ (powerClassMap f 2).range, H₂ x y = 1)
    (hE₃ : ∀ x ∈ (powerClassMap f 3).range, ∀ y ∈ (powerClassMap f 3).range, H₃ x y = 1)
    (hcard₂ : Nat.card (powerClassMap f 2).range ^ 2 = Nat.card (PowerClass G 2))
    (hcard₃ : Nat.card (powerClassMap f 3).range ^ 2 = Nat.card (PowerClass G 3)) :
    (∀ x, (∀ y ∈ (powerClassMap f 6).range, H x y = 1) → x ∈ (powerClassMap f 6).range) ∧
      ∃ B : Subgroup (PowerClass G 6), IsCompl (powerClassMap f 6).range B ∧
        ∀ x ∈ B, ∀ y ∈ B, H x y = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hs₂, B₂, hB₂, hi₂⟩ :=
    exists_isotropic_compl (powerClass_pow_eq_one G 2) e₂ H₂ hnd₂ halt₂ hE₂ hcard₂
  obtain ⟨hs₃, B₃, hB₃, hi₃⟩ :=
    exists_isotropic_compl (powerClass_pow_eq_one G 3) e₃ H₃ hnd₃ halt₃ hE₃ hcard₃
  exact combine_isotropic_complements (sexticClassEquiv G) H H₂ H₃ j₂ j₃ hj₂ hj₃
    hc₂ hc₃ (sexticClassEquiv_map_range f) hs₂ hs₃ hB₂ hB₃ hi₂ hi₃

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
