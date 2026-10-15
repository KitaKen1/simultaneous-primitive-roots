module

public import SimultaneousPrimitiveRoots.PrimeKummerSplitting
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.Cyclotomic.Gal

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Polynomial
noncomputable section

theorem prime_cyclotomic_primitiveRoots_nonempty (q : ℕ) [hq : Fact q.Prime] :
    (primitiveRoots q (CyclotomicField q ℚ)).Nonempty := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  exact ⟨_, (mem_primitiveRoots hq.out.pos).mpr
    (IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ))⟩

theorem primeKummer_relative_galois (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    IsGalois (CyclotomicField q ℚ) (PrimeKummerField a q) := by
  let : IsSplittingField (CyclotomicField q ℚ) (PrimeKummerField a q)
      (X ^ q - C (a : CyclotomicField q ℚ)) := primeKummerField_relative_splitting a q
  exact isGalois_of_isSplittingField_X_pow_sub_C
    (prime_cyclotomic_primitiveRoots_nonempty q)
    (cyclotomic_prime_radical_irreducible ha.out hq.out haq.out) _

theorem primeKummer_relative_galois_card (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    Nat.card Gal(PrimeKummerField a q/CyclotomicField q ℚ) = q := by
  let := primeKummer_relative_galois a q
  rw [IsGalois.card_aut_eq_finrank,
    primeKummerField_relative_degree ha.out hq.out haq.out]

theorem primeKummer_absolute_galois_card (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    Nat.card Gal(PrimeKummerField a q/ℚ) = q * (q - 1) := by
  let := primeKummerField_galois a q
  rw [IsGalois.card_aut_eq_finrank,
    primeKummerField_absolute_degree ha.out hq.out haq.out]

theorem primeKummer_relative_isCyclic (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    IsCyclic Gal(PrimeKummerField a q/CyclotomicField q ℚ) :=
  isCyclic_of_prime_card (primeKummer_relative_galois_card a q)

theorem primeKummer_relative_isAbelianGalois (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    IsAbelianGalois (CyclotomicField q ℚ) (PrimeKummerField a q) := by
  let := primeKummer_relative_galois a q
  let := primeKummer_relative_isCyclic a q
  exact IsAbelianGalois.of_isCyclic (CyclotomicField q ℚ) (PrimeKummerField a q)

/-- The root multiplier identifies the actual relative Galois group with
the q-th roots of unity of the cyclotomic base. -/
def primeKummerGaloisRootEquiv (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    Gal(PrimeKummerField a q/CyclotomicField q ℚ) ≃*
      rootsOfUnity q (CyclotomicField q ℚ) := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  exact (autAdjoinRootXPowSubCEquiv (prime_cyclotomic_primitiveRoots_nonempty q)
    (cyclotomic_prime_radical_irreducible ha.out hq.out haq.out)).symm

theorem primeKummerGaloisRootEquiv_action (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    (σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) :
    ((primeKummerGaloisRootEquiv a q σ : (CyclotomicField q ℚ)ˣ) :
      CyclotomicField q ℚ) • AdjoinRoot.root (primeRadicalPolynomial a q) =
        σ (AdjoinRoot.root (primeRadicalPolynomial a q)) := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  exact autAdjoinRootXPowSubCEquiv_symm_smul
    (prime_cyclotomic_primitiveRoots_nonempty q)
    (cyclotomic_prime_radical_irreducible ha.out hq.out haq.out) σ

/-- A fixed primitive root gives explicit additive coordinates on Gal(K/E).
No choice of a primitive element of the absolute field is used. -/
def primeKummerGaloisZmodEquiv (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    Gal(PrimeKummerField a q/CyclotomicField q ℚ) ≃* Multiplicative (ZMod q) := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  let : IsSplittingField (CyclotomicField q ℚ) (PrimeKummerField a q)
      (X ^ q - C (a : CyclotomicField q ℚ)) := primeKummerField_relative_splitting a q
  exact autEquivZmod (cyclotomic_prime_radical_irreducible ha.out hq.out haq.out)
    (PrimeKummerField a q) (IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ))

theorem primeKummerGaloisZmodEquiv_action (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] [NeZero q] (m : ℕ) :
    (primeKummerGaloisZmodEquiv a q).symm (Multiplicative.ofAdd (m : ZMod q))
      (AdjoinRoot.root (primeRadicalPolynomial a q)) =
        IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ) ^ m •
          AdjoinRoot.root (primeRadicalPolynomial a q) := by
  let : IsSplittingField (CyclotomicField q ℚ) (PrimeKummerField a q)
      (X ^ q - C (a : CyclotomicField q ℚ)) := primeKummerField_relative_splitting a q
  exact autEquivZmod_symm_apply_natCast
    (cyclotomic_prime_radical_irreducible ha.out hq.out haq.out)
    (PrimeKummerField a q)
    (by simpa only [map_natCast] using primeKummerField_root_pow a q)
    (IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ)) m

def primeKummerGenerator (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    Gal(PrimeKummerField a q/CyclotomicField q ℚ) :=
  (primeKummerGaloisZmodEquiv a q).symm (Multiplicative.ofAdd (1 : ZMod q))

theorem primeKummerGenerator_order (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    orderOf (primeKummerGenerator a q) = q := by
  rw [primeKummerGenerator, (primeKummerGaloisZmodEquiv a q).symm.orderOf_eq]
  exact ZMod.addOrderOf_one q

theorem primeKummerGenerator_pow_eq_coordinate (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (m : ℕ) :
    primeKummerGenerator a q ^ m =
      (primeKummerGaloisZmodEquiv a q).symm (Multiplicative.ofAdd (m : ZMod q)) := by
  rw [primeKummerGenerator, ← map_pow]
  congr 1
  change Multiplicative.ofAdd (m • (1 : ZMod q)) = _
  simp

theorem primeKummerGenerator_pow_action (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] [NeZero q] (m : ℕ) :
    (primeKummerGenerator a q ^ m) (AdjoinRoot.root (primeRadicalPolynomial a q)) =
      IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ) ^ m •
        AdjoinRoot.root (primeRadicalPolynomial a q) := by
  rw [primeKummerGenerator_pow_eq_coordinate]
  exact primeKummerGaloisZmodEquiv_action a q m

theorem primeKummerGalois_exists_unique_coordinate (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    (σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) :
    ∃! m : Fin q, primeKummerGenerator a q ^ m.val = σ := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  let r : ZMod q := Multiplicative.toAdd (primeKummerGaloisZmodEquiv a q σ)
  refine ⟨⟨r.val, ZMod.val_lt r⟩, ?_, ?_⟩
  · change primeKummerGenerator a q ^ r.val = σ
    rw [primeKummerGenerator_pow_eq_coordinate, ZMod.natCast_zmod_val]
    exact (primeKummerGaloisZmodEquiv a q).symm_apply_apply σ
  · intro m hm
    apply Fin.ext
    have h := congrArg (fun τ => Multiplicative.toAdd (primeKummerGaloisZmodEquiv a q τ)) hm
    rw [primeKummerGenerator_pow_eq_coordinate, MulEquiv.apply_symm_apply] at h
    have := congrArg ZMod.val h
    change (m.val : ZMod q).val = r.val at this
    simpa only [ZMod.val_natCast_of_lt m.isLt] using this

theorem primeKummerGalois_eq_iff_root (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (σ τ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) :
    σ = τ ↔ σ (AdjoinRoot.root (primeRadicalPolynomial a q)) =
      τ (AdjoinRoot.root (primeRadicalPolynomial a q)) := by
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  apply AlgEquiv.coe_toAlgHom_injective
  exact AdjoinRoot.algHom_ext h

end
end SimultaneousPrimitiveRoots
