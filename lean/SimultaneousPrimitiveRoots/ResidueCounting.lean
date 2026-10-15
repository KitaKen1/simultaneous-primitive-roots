module

public import SimultaneousPrimitiveRoots.ResidueCRT
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Totient

@[expose] public section

namespace SimultaneousPrimitiveRoots

open scoped Function

def allowedLocalResidues (q : ℕ) : Finset ℕ := ((Finset.range q).erase 0).erase 1

theorem mem_allowedLocalResidues {q r : ℕ} :
    r ∈ allowedLocalResidues q ↔ r < q ∧ r ≠ 0 ∧ r ≠ 1 := by
  simp only [allowedLocalResidues, Finset.mem_erase, Finset.mem_range]
  tauto

theorem allowedLocalResidues_card {q : ℕ} (hq : 2 ≤ q) :
    (allowedLocalResidues q).card = q - 2 := by
  rw [allowedLocalResidues, Finset.card_erase_of_mem, Finset.card_erase_of_mem,
    Finset.card_range]
  · omega
  · exact Finset.mem_range.mpr (by omega)
  · simp only [Finset.mem_erase, Finset.mem_range]
    omega

/-- Extension of an arbitrary reduced base class, retaining every local choice. -/
theorem exists_crt_extension {M b : ℕ} {S : Finset ℕ} {r : ℕ → ℕ}
    (hM : 0 < M) (hb : b < M) (hbc : b.Coprime M)
    (hS : ∀ q ∈ S, q.Prime) (hc : ∀ q ∈ S, M.Coprime q)
    (hr : ∀ q ∈ S, r q < q ∧ r q ≠ 0) :
    ∃ u : ℕ, u < M * (∏ q ∈ S, q) ∧ u.Coprime (M * (∏ q ∈ S, q)) ∧
      u % M = b ∧ ∀ q ∈ S, u % q = r q := by
  classical
  have hne : ∀ q ∈ S, q ≠ 0 := fun q hq => (hS q hq).ne_zero
  have hpair : Set.Pairwise (S : Set ℕ) (Nat.Coprime on fun q : ℕ => q) := by
    intro q hq t ht hqt
    exact (Nat.coprime_primes (hS q hq) (hS t ht)).mpr hqt
  let w := Nat.chineseRemainderOfFinset r (fun q : ℕ => q) S hne hpair
  have hcop : M.Coprime (∏ q ∈ S, q) := Nat.coprime_prod_right_iff.mpr hc
  have hprod : (∏ q ∈ S, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  let u := Nat.chineseRemainder hcop b w.val
  have huq : ∀ q ∈ S, u.val ≡ r q [MOD q] := by
    intro q hq
    exact (u.property.2.of_dvd (Finset.dvd_prod_of_mem (fun q : ℕ => q) hq)).trans
      (w.property q hq)
  refine ⟨u.val, Nat.chineseRemainder_lt_mul hcop b w.val hM.ne' hprod, ?_, ?_, ?_⟩
  · apply Nat.coprime_mul_iff_right.mpr
    constructor
    · change Nat.gcd u.val M = 1
      rw [u.property.1.gcd_eq]
      exact hbc
    · apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      change Nat.gcd u.val q = 1
      rw [(huq q hq).gcd_eq]
      exact (Nat.coprime_of_lt_prime (hr q hq).2 (hr q hq).1 (hS q hq)).symm
  · simpa only [Nat.ModEq, Nat.mod_eq_of_lt hb] using u.property.1
  · intro q hq
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hr q hq).1] using huq q hq

def allowedExtensions (M b : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (M * (∏ q ∈ S, q))).filter fun u =>
    u.Coprime (M * (∏ q ∈ S, q)) ∧ u % M = b ∧ ∀ q ∈ S, u % q ≠ 1

theorem allowedExtensions_card_lower {M b : ℕ} {S : Finset ℕ}
    (hM : 0 < M) (hb : b < M) (hbc : b.Coprime M)
    (hS : ∀ q ∈ S, q.Prime) (hc : ∀ q ∈ S, M.Coprime q) :
    (∏ q ∈ S, (q - 2)) ≤ (allowedExtensions M b S).card := by
  classical
  let Choices := (q : S) → (allowedLocalResidues q.val)
  have hchoose (c : Choices) : ∃ u : ℕ,
      u ∈ allowedExtensions M b S ∧ ∀ q : S, u % q.val = (c q).val := by
    let r : ℕ → ℕ := fun q => if hq : q ∈ S then (c ⟨q, hq⟩).val else 0
    have hr (q : ℕ) (hq : q ∈ S) : r q < q ∧ r q ≠ 0 := by
      simpa only [r, dif_pos hq] using
        (mem_allowedLocalResidues.mp (c ⟨q, hq⟩).property).imp_right And.left
    obtain ⟨u, hu, huc, hub, huq⟩ := exists_crt_extension hM hb hbc hS hc hr
    refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu, huc, hub, ?_⟩, ?_⟩
    · intro q hq
      rw [huq q hq]
      have h := (mem_allowedLocalResidues.mp (c ⟨q, hq⟩).property).2.2
      simpa only [r, dif_pos hq] using h
    · intro q
      simpa only [r, dif_pos q.property] using huq q.val q.property
  let f : Choices → (allowedExtensions M b S) := fun c =>
    ⟨Classical.choose (hchoose c), (Classical.choose_spec (hchoose c)).1⟩
  have hf : Function.Injective f := by
    intro c d hcd
    funext q
    apply Subtype.ext
    calc
      (c q).val = (f c).val % q.val := (Classical.choose_spec (hchoose c)).2 q |>.symm
      _ = (f d).val % q.val := congrArg (fun u => u.val % q.val) hcd
      _ = (d q).val := (Classical.choose_spec (hchoose d)).2 q
  have hcard : Fintype.card Choices = ∏ q ∈ S, (q - 2) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_coe]
    calc
      (∏ q : S, (allowedLocalResidues q.val).card) = ∏ q : S, (q.val - 2) := by
        apply Finset.prod_congr rfl
        intro q _
        exact allowedLocalResidues_card (hS q.val q.property).two_le
      _ = ∏ q ∈ S, (q - 2) := Finset.prod_coe_sort S (fun q : ℕ => q - 2)
  rw [← hcard, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective f hf

theorem totient_prod_primes {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) :
    Nat.totient (∏ q ∈ S, q) = ∏ q ∈ S, (q - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
    have hprime : q.Prime := hS q (Finset.mem_insert_self q S)
    have hrest : ∀ t ∈ S, t.Prime := fun t ht => hS t (Finset.mem_insert_of_mem ht)
    have hc : q.Coprime (∏ t ∈ S, t) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro t ht
      exact (Nat.coprime_primes hprime (hrest t ht)).mpr (by rintro rfl; exact hq ht)
    rw [Finset.prod_insert hq, Nat.totient_mul hc, Nat.totient_prime hprime,
      ih hrest, Finset.prod_insert hq]

end SimultaneousPrimitiveRoots
