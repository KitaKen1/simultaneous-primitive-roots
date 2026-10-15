module

public import SimultaneousPrimitiveRoots.LocalResidues

@[expose] public section

namespace SimultaneousPrimitiveRoots

open scoped Function

theorem prime_ge_five_coprime_twenty_four {q : ℕ} (hq : q.Prime) (hfive : 5 ≤ q) :
    q.Coprime 24 := by
  have htwo : q.Coprime 2 := (Nat.coprime_primes hq Nat.prime_two).mpr (by omega)
  have hthree : q.Coprime 3 := (Nat.coprime_primes hq Nat.prime_three).mpr (by omega)
  simpa using (htwo.pow_right 3).mul_right hthree

/-- Assemble finitely many local choices. Empty S is allowed. -/
theorem exists_fixed_residue {S : Finset ℕ} {r : ℕ → ℕ} {b : ℕ}
    (hb : b < 24) (hbc : b.Coprime 24)
    (hS : ∀ q ∈ S, q.Prime ∧ 5 ≤ q)
    (hr : ∀ q ∈ S, r q < q ∧ r q ≠ 0 ∧ r q ≠ 1) :
    ∃ u : ℕ, u < 24 * (∏ q ∈ S, q) ∧
      u.Coprime (24 * (∏ q ∈ S, q)) ∧ u % 24 = b ∧
      ∀ q ∈ S, u % q = r q := by
  classical
  have hne : ∀ q ∈ S, q ≠ 0 := fun q hq => (hS q hq).1.ne_zero
  have hpair : Set.Pairwise (S : Set ℕ) (Nat.Coprime on fun q : ℕ => q) := by
    intro q hq t ht hqt
    exact (Nat.coprime_primes (hS q hq).1 (hS t ht).1).mpr hqt
  let w := Nat.chineseRemainderOfFinset r (fun q : ℕ => q) S hne hpair
  have hc : Nat.Coprime 24 (∏ q ∈ S, q) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    exact (prime_ge_five_coprime_twenty_four (hS q hq).1 (hS q hq).2).symm
  have hprod : (∏ q ∈ S, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  let u := Nat.chineseRemainder hc b w.val
  have huq : ∀ q ∈ S, u.val ≡ r q [MOD q] := by
    intro q hq
    exact (u.property.2.of_dvd (Finset.dvd_prod_of_mem (fun q : ℕ => q) hq)).trans
      (w.property q hq)
  refine ⟨u.val, Nat.chineseRemainder_lt_mul hc b w.val (by decide) hprod, ?_, ?_, ?_⟩
  · apply Nat.coprime_mul_iff_right.mpr
    constructor
    · change Nat.gcd u.val 24 = 1
      rw [u.property.1.gcd_eq]
      exact hbc
    · apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      change Nat.gcd u.val q = 1
      rw [(huq q hq).gcd_eq]
      exact (Nat.coprime_of_lt_prime (hr q hq).2.1 (hr q hq).1 (hS q hq).1).symm
  · simpa only [Nat.ModEq, Nat.mod_eq_of_lt hb] using u.property.1
  · intro q hq
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hr q hq).1] using huq q hq

theorem not_dvd_sub_one_of_local_residue {p q r : ℕ}
    (hp : 0 < p) (hq : 1 < q) (hr : r ≠ 1) (hmod : p % q = r) :
    ¬ q ∣ p - 1 := by
  rintro ⟨k, hk⟩
  have heq : p = q * k + 1 := by omega
  have hone : p % q = 1 := by simp [heq, Nat.add_mod, Nat.mod_eq_of_lt hq]
  exact hr (hmod.symm.trans hone)

/-- Every prime in the assembled class retains the base signs and avoids q | p-1. -/
theorem fixed_residue_prime_properties {S : Finset ℕ} {r : ℕ → ℕ} {u p : ℕ}
    [Fact p.Prime] (hp : 3 < p) (e₂ e₃ : ZMod 2)
    (hbase : u % 24 = baseResidue e₂ e₃)
    (hS : ∀ q ∈ S, 5 ≤ q)
    (hr : ∀ q ∈ S, r q < q ∧ r q ≠ 1 ∧ u % q = r q)
    (hpu : p ≡ u [MOD 24 * (∏ q ∈ S, q)]) :
    legendreSym p 2 = binarySign e₂ ∧ legendreSym p 3 = binarySign e₃ ∧
      ∀ q ∈ S, ¬ q ∣ p - 1 := by
  have hpbase : p % 24 = baseResidue e₂ e₃ := by
    calc p % 24 = u % 24 := hpu.of_dvd (dvd_mul_right 24 _)
         _ = baseResidue e₂ e₃ := hbase
  obtain ⟨h2, h3⟩ := baseResidue_realizes_signs hp e₂ e₃ hpbase
  refine ⟨h2, h3, ?_⟩
  intro q hq
  have hdvd : q ∣ 24 * (∏ t ∈ S, t) :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun t : ℕ => t) hq) 24
  have hpq : p % q = r q := by
    calc p % q = u % q := hpu.of_dvd hdvd
         _ = r q := (hr q hq).2.2
  exact not_dvd_sub_one_of_local_residue (by omega) (by have := hS q hq; omega)
    (hr q hq).2.1 hpq

end SimultaneousPrimitiveRoots
