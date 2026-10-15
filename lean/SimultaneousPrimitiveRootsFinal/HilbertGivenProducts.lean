import SimultaneousPrimitiveRootsFinal.HilbertPowerClasses
import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PairingProducts

/-!
# Complements for an already chosen coherent Hilbert family

When applying the global product formula, its chosen family must be preserved.
This API accepts that family instead of choosing unrelated local witnesses.
Local finiteness, global isotropy and the cardinality of E remain explicit here;
the actual local finiteness is available from CFT's `powerClassGroup_finite`.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open ClassFieldTheory Arithmetic

/-- **The complement construction preserves a supplied family of local pairings.** -/
theorem exists_given_hilbert_product_compl
    {ι : Type*} [Fintype ι] (K : ι → Type*) [∀ i, Field (K i)]
    (n : ℕ+) [Fact (n : ℕ).Prime] [∀ i, Finite (PowerClassGroup (K i) n)]
    (B : ∀ i, HilbertPairing (K i) n) (hB : ∀ i, (B i).IsLocalHilbertPairing)
    (halt : Odd (n : ℕ) ∨ ∀ i, ∃ u : (K i)ˣ, u ^ (n : ℕ) = -1)
    {μ : Type*} [CommGroup μ] (e : ∀ i, rootsOfUnity (n : ℕ) (K i) ≃* μ)
    (eμ : μ ≃* Multiplicative (ZMod (n : ℕ)))
    (H : ∀ i, PowerClassGroup (K i) n →* PowerClassGroup (K i) n →* μ)
    (hH : ∀ i x y, H i x y = e i (B i x y))
    {E : Subgroup (∀ i, PowerClassGroup (K i) n)}
    (hE : ∀ x ∈ E, ∀ y ∈ E, piPairing H x y = 1)
    (hcard : Nat.card E ^ 2 = Nat.card (∀ i, PowerClassGroup (K i) n)) :
    (∀ x, (∀ y ∈ E, piPairing H x y = 1) → x ∈ E) ∧
      ∃ C : Subgroup (∀ i, PowerClassGroup (K i) n), IsCompl E C ∧
        ∀ x ∈ C, ∀ y ∈ C, piPairing H x y = 1 := by
  have hV : ∀ i (x : PowerClassGroup (K i) n), x ^ (n : ℕ) = 1 := by
    intro i
    change ∀ x : PowerClass (K i)ˣ (n : ℕ), x ^ (n : ℕ) = 1
    exact powerClass_pow_eq_one (K i)ˣ (n : ℕ)
  have hnd : ∀ i x, (∀ y, H i x y = 1) → x = 1 := by
    intro i x hx
    apply (hB i).2.2.1.1
    intro y
    exact (e i).map_eq_one_iff.mp ((hH i x y).symm.trans (hx y))
  have hAlt : ∀ i x, H i x x = 1 := by
    intro i x
    rw [hH]
    rcases halt with hodd | hminus
    · rw [hilbertPairing_isAlt_of_odd (B i) (hB i).2.1 hodd, map_one]
    · rw [hilbertPairing_isAlt_of_minus_one_is_power (B i) (hB i).1 (hminus i), map_one]
  exact exists_piPairing_isotropic_compl (V := fun i => PowerClassGroup (K i) n)
    hV eμ H hnd hAlt hE hcard

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
