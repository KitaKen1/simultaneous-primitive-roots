module

public import SimultaneousPrimitiveRoots.ResidueCRT
public import SimultaneousPrimitiveRoots.QuadraticSigns
public import Mathlib.Algebra.BigOperators.Associated

@[expose] public section

namespace SimultaneousPrimitiveRoots

theorem legendre_eq_binarySign_of_coordinates {p a : ℕ} [Fact p.Prime]
    (ha : a ≠ 0) (z : ℕ → ZMod 2)
    (hz : ∀ q ∈ a.factorization.support, legendreSym p q = binarySign (z q)) :
    legendreSym p a = binarySign
      (∑ q ∈ a.factorization.support, (a.factorization q : ZMod 2) * z q) := by
  classical
  have hfac : (a : ℤ) = ∏ q ∈ a.factorization.support, (q : ℤ) ^ a.factorization q := by
    have h := Nat.prod_factorization_pow_eq_self ha
    change (∏ q ∈ a.factorization.support, q ^ a.factorization q) = a at h
    exact_mod_cast h.symm
  rw [hfac]
  change (legendreSym.hom p) (∏ q ∈ a.factorization.support,
    (q : ℤ) ^ a.factorization q) = _
  rw [map_prod, binarySign_sum]
  apply Finset.prod_congr rfl
  intro q hq
  rw [map_pow, legendreSym.hom_apply, hz q hq, binarySign_nat_mul]

/-- A finite set of coordinate signs is realized on a single reduced residue class. -/
theorem exists_signed_fixed_residue {S : Finset ℕ}
    (hS : ∀ q ∈ S, q.Prime ∧ 5 ≤ q) (z : ℕ → ZMod 2) :
    ∃ u : ℕ, u < 24 * (∏ q ∈ S, q) ∧ u.Coprime (24 * (∏ q ∈ S, q)) ∧
      u % 24 = baseResidue (z 2) (z 3) ∧
      ∀ (p : ℕ) [Fact p.Prime], 3 < p → p ≡ u [MOD 24 * (∏ q ∈ S, q)] →
        legendreSym p 2 = binarySign (z 2) ∧ legendreSym p 3 = binarySign (z 3) ∧
          ∀ q ∈ S, legendreSym p q = binarySign (z q) ∧ ¬ q ∣ p - 1 := by
  classical
  let b := baseResidue (z 2) (z 3)
  have hex (q : ℕ) (hq : q ∈ S) : ∃ r : ℕ,
      r < q ∧ r ≠ 0 ∧ r ≠ 1 ∧
        @legendreSym q ⟨(hS q hq).1⟩ r = adjustedSign b q (z q) := by
    let : Fact q.Prime := ⟨(hS q hq).1⟩
    exact exists_local_residue (hS q hq).2 (adjustedSign_values b q (z q))
  let r : ℕ → ℕ := fun q => if hq : q ∈ S then Classical.choose (hex q hq) else 4
  have hr (q : ℕ) (hq : q ∈ S) :
      r q < q ∧ r q ≠ 0 ∧ r q ≠ 1 ∧
        @legendreSym q ⟨(hS q hq).1⟩ (r q) = adjustedSign b q (z q) := by
    simpa only [r, dif_pos hq] using Classical.choose_spec (hex q hq)
  obtain ⟨u, hu, huc, hub, huq⟩ := exists_fixed_residue
    (baseResidue_properties (z 2) (z 3)).1 (baseResidue_properties (z 2) (z 3)).2.1
    hS (fun q hq => ⟨(hr q hq).1, (hr q hq).2.1, (hr q hq).2.2.1⟩)
  refine ⟨u, hu, huc, hub, ?_⟩
  intro p _ hp hpu
  have hpbase : p % 24 = b := by
    calc p % 24 = u % 24 := hpu.of_dvd (dvd_mul_right 24 _)
         _ = b := hub
  obtain ⟨h2, h3, havoid⟩ := fixed_residue_prime_properties hp (z 2) (z 3) hub
    (fun q hq => (hS q hq).2)
    (fun q hq => ⟨(hr q hq).1, (hr q hq).2.2.1, huq q hq⟩) hpu
  refine ⟨h2, h3, ?_⟩
  intro q hq
  let : Fact q.Prime := ⟨(hS q hq).1⟩
  have hpq : p % q = r q := by
    calc p % q = u % q := hpu.of_dvd
           (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun q : ℕ => q) hq) 24)
         _ = r q := huq q hq
  exact ⟨legendre_of_local_residue hp (hS q hq).2 hpbase hpq (z q) (hr q hq).2.2.2,
    havoid q hq⟩

/-- SQ supplies a fixed reduced class with every a a nonsquare and with all
odd prime divisors up to Y removed from p-1. This is a residue construction,
not an assertion that the class contains enough candidate primes. -/
theorem exists_nonsquare_progression_strong {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hSQ : SquareCondition A) (Y : ℕ) :
    ∃ H u : ℕ, 0 < H ∧ u < H ∧ u.Coprime H ∧
      ∀ p : ℕ, p.Prime → 3 < p → p ≡ u [MOD H] →
        (∀ a ∈ A, ¬ IsSquare (a : ZMod p)) ∧
          ∀ q : ℕ, q.Prime → 3 ≤ q → (q ≤ Y ∨ q ∣ H) → ¬ q ∣ p - 1 := by
  classical
  obtain ⟨z, hz⟩ := exists_squareClass_coefficients hpos hSQ
  let S := ((A.biUnion fun a => a.factorization.support) ∪
    (Finset.range (Y + 1)).filter Nat.Prime).filter (fun q => 5 ≤ q)
  have hS : ∀ q ∈ S, q.Prime ∧ 5 ≤ q := by
    intro q hq
    obtain ⟨hmem, hfive⟩ := Finset.mem_filter.mp hq
    refine ⟨?_, hfive⟩
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · obtain ⟨a, _, hqa⟩ := Finset.mem_biUnion.mp hmem
      exact Nat.prime_of_mem_primeFactors hqa
    · exact (Finset.mem_filter.mp hmem).2
  obtain ⟨u, hu, huc, hub, hclass⟩ := exists_signed_fixed_residue hS z
  have hH : 0 < 24 * (∏ q ∈ S, q) := by
    apply Nat.mul_pos (by decide)
    exact Finset.prod_pos fun q hq => (hS q hq).1.pos
  refine ⟨24 * (∏ q ∈ S, q), u, hH, hu, huc, ?_⟩
  intro p hprime hp hpu
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨h2, h3, hq⟩ := hclass p hp hpu
  constructor
  · intro a ha
    have hcoord : ∀ q ∈ a.factorization.support, legendreSym p q = binarySign (z q) := by
      intro q hqa
      by_cases hqtwo : q = 2
      · simpa only [hqtwo, Nat.cast_ofNat] using h2
      by_cases hqthree : q = 3
      · simpa only [hqthree, Nat.cast_ofNat] using h3
      have hqprime := Nat.prime_of_mem_primeFactors hqa
      have hfive : 5 ≤ q := by
        have hodd := hqprime.eq_two_or_odd.resolve_left hqtwo
        have := hqprime.two_le
        omega
      apply (hq q ?_).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨a, ha, hqa⟩), hfive⟩
    have hleg : legendreSym p a = -1 := by
      rw [legendre_eq_binarySign_of_coordinates (by have := hpos a ha; omega) z hcoord,
        hz a ha]
      decide +kernel
    exact (legendreSym.eq_neg_one_iff' p).mp hleg
  · intro q hqprime hqthree hqrange
    by_cases hthree : q = 3
    · subst q
      have hp3 : p % 3 = 2 := by
        have hpbase : p % 24 = baseResidue (z 2) (z 3) := by
          calc p % 24 = u % 24 := hpu.of_dvd (dvd_mul_right 24 _)
               _ = baseResidue (z 2) (z 3) := hub
        have h := (baseResidue_properties (z 2) (z 3)).2.2
        omega
      exact not_dvd_sub_one_of_local_residue (by omega) (by decide) (by decide) hp3
    · have hfive : 5 ≤ q := by
        have hodd := hqprime.eq_two_or_odd.resolve_left (by omega)
        omega
      apply (hq q ?_).2
      rcases hqrange with hqY | hqH
      · exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hqprime⟩), hfive⟩
      · have hn24 : ¬ q ∣ 24 := hqprime.coprime_iff_not_dvd.mp
          (prime_ge_five_coprime_twenty_four hqprime hfive)
        have hqprod := (hqprime.dvd_mul.mp hqH).resolve_left hn24
        obtain ⟨t, ht, hqt⟩ := (hqprime.prime.dvd_finsetProd_iff (fun t : ℕ => t)).mp hqprod
        have heq : q = t := (Nat.dvd_prime (hS t ht).1).mp hqt |>.resolve_left hqprime.ne_one
        simpa only [heq] using ht

theorem exists_nonsquare_progression {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hSQ : SquareCondition A) (Y : ℕ) :
    ∃ H u : ℕ, 0 < H ∧ u < H ∧ u.Coprime H ∧
      ∀ p : ℕ, p.Prime → 3 < p → p ≡ u [MOD H] →
        (∀ a ∈ A, ¬ IsSquare (a : ZMod p)) ∧
          ∀ q : ℕ, q.Prime → 3 ≤ q → q ≤ Y → ¬ q ∣ p - 1 := by
  obtain ⟨H, u, hH, hu, huc, hclass⟩ := exists_nonsquare_progression_strong hpos hSQ Y
  refine ⟨H, u, hH, hu, huc, ?_⟩
  intro p hp hp3 hpu
  have h := hclass p hp hp3 hpu
  exact ⟨h.1, fun q hq hq3 hqY => h.2 q hq hq3 (Or.inl hqY)⟩

end SimultaneousPrimitiveRoots
