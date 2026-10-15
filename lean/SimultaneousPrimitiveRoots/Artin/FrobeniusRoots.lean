module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# An arithmetic Frobenius fixes the roots of a polynomial exactly when it splits mod `p`

Let `L` be a number field, `g ∈ ℤ[X]` monic and split in `L`, `Q` a prime of `𝓞 L` over the
rational prime `p`, and `σ ∈ Gal(L/ℚ)` an arithmetic Frobenius at `Q`. If `g mod p` is
separable, then

`σ` fixes every root of `g` in `L`  ⟺  `g mod p` splits over `𝔽_p`

(`frobenius_fixes_roots_iff_splits`). Both sides are equivalent to `g mod p ∣ X^p - X`: the
roots of `g` in `𝓞 L` reduce to distinct roots in the residue field `𝓞 L / Q` (separability),
`σ` acts on them as `x ↦ x^p`, and a root is fixed by `σ` iff its reduction is a root of
`X^p - X`.

This is the input that turns the Chebotarev density theorem (Tau Ceti) for the splitting field
of `∏_{q ≤ Y} (X^q - a)` into densities of primes `p` at which `a` is a `q`-th power residue.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Artin

open Polynomial NumberField IsDedekindDomain

/-- Over `ZMod p`, a monic separable polynomial splits iff it divides `X^p - X`. -/
theorem splits_iff_dvd_X_pow_sub_X {p : ℕ} [hp : Fact p.Prime] {f : (ZMod p)[X]}
    (hm : f.Monic) (hs : f.Separable) : f.Splits ↔ f ∣ X ^ p - X := by
  have hXne : (X ^ p - X : (ZMod p)[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) hp.out.one_lt
  constructor
  · intro hf
    rw [hf.eq_prod_roots_of_monic hm, Multiset.prod_X_sub_C_dvd_iff_le_roots hXne]
    have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
      have := FiniteField.roots_X_pow_card_sub_X (ZMod p)
      rwa [ZMod.card] at this
    rw [hroots]
    exact (Multiset.le_iff_subset (nodup_roots hs)).mpr fun x _ => Finset.mem_univ_val x
  · intro hdvd
    have hX : (X ^ p - X : (ZMod p)[X]).Splits := by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using
        (splits_X_pow_nat_card_sub_X (K := ZMod p))
    exact hX.of_dvd hXne hdvd

variable {L : Type*} [Field L] [NumberField L]

/-- **An arithmetic Frobenius fixes the roots of `g` iff `g` splits modulo `p`.** -/
theorem frobenius_fixes_roots_iff_splits
    (𝔭 : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal]
    {σ : L ≃ₐ[ℚ] L} (hσ : IsArithFrobAt (𝓞 ℚ) σ Q)
    {g : ℤ[X]} (hg : g.Monic) (hsplit : (g.map (algebraMap ℤ L)).Splits)
    (hsep : (g.map (Int.castRingHom (ZMod (Ideal.absNorm 𝔭.asIdeal)))).Separable) :
    (∀ β ∈ (g.map (algebraMap ℤ L)).roots, σ β = β) ↔
      (g.map (Int.castRingHom (ZMod (Ideal.absNorm 𝔭.asIdeal)))).Splits := by
  classical
  set p := Ideal.absNorm 𝔭.asIdeal with hpdef
  have hp : p.Prime := by
    rw [hpdef, Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact Rat.HeightOneSpectrum.prime_natGenerator 𝔭
  have : Fact p.Prime := ⟨hp⟩
  -- `p ∈ Q`, so `Q` is a maximal ideal with residue field of characteristic `p`
  have hpQ : (p : 𝓞 L) ∈ Q := by
    have h1 : (p : 𝓞 ℚ) ∈ 𝔭.asIdeal := Ideal.absNorm_mem 𝔭.asIdeal
    have h2 := (Ideal.mem_of_liesOver Q 𝔭.asIdeal (p : 𝓞 ℚ)).mp h1
    rwa [map_natCast] at h2
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpQ
    exact hp.ne_zero (by exact_mod_cast hpQ)
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  let : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  have : CharP (𝓞 L ⧸ Q) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    exact hpQ)
  set κ := 𝓞 L ⧸ Q
  set mk : 𝓞 L →+* κ := Ideal.Quotient.mk Q
  set ι : ZMod p →+* κ := ZMod.castHom (dvd_refl p) κ
  have hι : Function.Injective ι := ι.injective
  have hcard : Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) = p := by
    rw [← Q.over_def 𝔭.asIdeal, hpdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  -- the roots of `g` in `L` are algebraic integers
  set gL := g.map (algebraMap ℤ L) with hgL
  have hint : ∀ β ∈ gL.roots, β ∈ integralClosure ℤ L := by
    intro β hβ
    rw [mem_roots (hg.map _).ne_zero, IsRoot, eval_map_algebraMap] at hβ
    exact ⟨g, hg, hβ⟩
  let lift : {x // x ∈ gL.roots} → 𝓞 L := fun β => ⟨β.1, hint β.1 β.2⟩
  have hlift : ∀ β, algebraMap (𝓞 L) L (lift β) = β.1 := fun β => rfl
  set r : Multiset (𝓞 L) := gL.roots.attach.map lift with hrdef
  have hr_map : r.map (algebraMap (𝓞 L) L) = gL.roots := by
    rw [hrdef, Multiset.map_map]
    have hcomp : (algebraMap (𝓞 L) L ∘ lift) = Subtype.val := funext hlift
    rw [hcomp, Multiset.attach_map_val]
  have halg_inj : Function.Injective (algebraMap (𝓞 L) L) := RingOfIntegers.coe_injective
  have hmem_r : ∀ x : 𝓞 L, x ∈ r ↔ algebraMap (𝓞 L) L x ∈ gL.roots := by
    intro x
    constructor
    · intro hx
      rw [← hr_map]
      exact Multiset.mem_map_of_mem _ hx
    · intro hx
      rw [← hr_map, Multiset.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rwa [← halg_inj hyx]
  clear_value r
  clear hrdef
  -- `g = ∏ (X - α)` over `𝓞 L`, and its reduction modulo `Q`
  have hgO : g.map (algebraMap ℤ (𝓞 L)) = (r.map fun α => X - C α).prod := by
    apply map_injective (algebraMap (𝓞 L) L) halg_inj
    have hL : (g.map (algebraMap ℤ (𝓞 L))).map (algebraMap (𝓞 L) L) = gL := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have hR : (r.map fun α => X - C α).prod.map (algebraMap (𝓞 L) L) =
        ((r.map (algebraMap (𝓞 L) L)).map fun β => X - C β).prod := by
      rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro α _
      simp
    rw [hL, hR, hr_map]
    exact hsplit.eq_prod_roots_of_monic (hg.map _)
  set gκ := g.map (Int.castRingHom κ) with hgκ
  have hgκ_prod : gκ = ((r.map mk).map fun c => X - C c).prod := by
    have h1 : gκ = (g.map (algebraMap ℤ (𝓞 L))).map mk := by
      rw [hgκ, Polynomial.map_map]
      congr 1
    rw [h1, hgO, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro α _
    simp
  set gp := g.map (Int.castRingHom (ZMod p)) with hgp
  have hgκ_gp : gκ = gp.map ι := by
    rw [hgκ, hgp, Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hgp_monic : gp.Monic := hg.map _
  have hgκ_ne : gκ ≠ 0 := (hg.map _).ne_zero
  -- the reductions of the roots are distinct
  have hroots_κ : gκ.roots = r.map mk := by
    rw [hgκ_prod, roots_multiset_prod_X_sub_C]
  have hnodup : (r.map mk).Nodup := by
    rw [← hroots_κ, hgκ_gp]
    exact nodup_roots (hsep.map)
  have hinj : ∀ x ∈ r, ∀ y ∈ r, mk x = mk y → x = y :=
    Multiset.inj_on_of_nodup_map hnodup
  -- `σ` permutes the roots and acts on residues as `x ↦ x ^ p`
  have hσroot : ∀ α ∈ r, σ • α ∈ r := by
    intro α hα
    rw [hmem_r, algebraMap_smul_eq_apply]
    have hβ := (hmem_r α).mp hα
    rw [mem_roots (hg.map _).ne_zero, IsRoot, eval_map_algebraMap] at hβ ⊢
    have h := Polynomial.aeval_algHom_apply ((σ : L →ₐ[ℚ] L).restrictScalars ℤ)
      (algebraMap (𝓞 L) L α) g
    rw [hβ, map_zero] at h
    exact h
  have hσmk : ∀ α : 𝓞 L, mk (σ • α) = mk α ^ p := by
    intro α
    have h := hσ.mk_apply α
    rw [hcard] at h
    exact h
  have hXκ : (X ^ p - X : κ[X]) ≠ 0 := by
    intro h
    have h1 : (X ^ p - X : κ[X]).natDegree = p := by
      rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hp.one_lt]
    rw [h, natDegree_zero] at h1
    exact hp.ne_zero h1.symm
  have hmapX : (X ^ p - X : (ZMod p)[X]).map ι = X ^ p - X := by
    simp [Polynomial.map_sub, Polynomial.map_pow]
  rw [splits_iff_dvd_X_pow_sub_X hgp_monic hsep, ← map_dvd_map ι hι hgp_monic, hmapX,
    ← hgκ_gp]
  constructor
  · intro hfix
    rw [hgκ_prod, Multiset.prod_X_sub_C_dvd_iff_le_roots hXκ,
      Multiset.le_iff_subset hnodup]
    intro c hc
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hc
    have hfixα : σ • α = α := by
      apply halg_inj
      rw [algebraMap_smul_eq_apply]
      exact hfix _ ((hmem_r α).mp hα)
    rw [mem_roots hXκ, IsRoot, eval_sub, eval_pow, eval_X, ← hσmk, hfixα, sub_self]
  · intro hdvd β hβ
    have hα := (hmem_r ⟨β, hint β hβ⟩).mpr hβ
    set α : 𝓞 L := ⟨β, hint β hβ⟩
    have hroot : mk α ∈ gκ.roots := by
      rw [hroots_κ]
      exact Multiset.mem_map_of_mem _ hα
    have hrootX : mk α ∈ (X ^ p - X : κ[X]).roots := by
      rw [mem_roots hXκ]
      exact (mem_roots hgκ_ne).mp hroot |>.dvd hdvd
    rw [mem_roots hXκ, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero] at hrootX
    have heq : σ • α = α := hinj _ (hσroot α hα) _ hα (by rw [hσmk, hrootX])
    have := congrArg (algebraMap (𝓞 L) L) heq
    rwa [algebraMap_smul_eq_apply] at this

end SimultaneousPrimitiveRoots.Artin

end
