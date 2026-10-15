module

public import SimultaneousPrimitiveRoots.SquareClasses
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.Data.Nat.ChineseRemainder

@[expose] public section

namespace SimultaneousPrimitiveRoots

/-- The square branch can always use 4, avoiding a count of quadratic residues. -/
theorem exists_local_residue {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q)
    {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∃ r : ℕ, r < q ∧ r ≠ 0 ∧ r ≠ 1 ∧ legendreSym q r = s := by
  rcases hs with rfl | rfl
  · refine ⟨4, by omega, by decide, by decide, ?_⟩
    apply (legendreSym.eq_one_iff' q ?_).mpr
    · exact ⟨(2 : ZMod q), by norm_num⟩
    · intro hz
      have hdvd := (ZMod.natCast_eq_zero_iff 4 q).mp hz
      have hle := Nat.le_of_dvd (by decide : 0 < 4) hdvd
      omega
  · obtain ⟨z, hz⟩ := FiniteField.exists_nonsquare (F := ZMod q)
      ((ZMod.ringChar_zmod_n q).substr (by omega))
    refine ⟨z.val, ZMod.val_lt z, ?_, ?_, ?_⟩
    · intro hr
      have hzero : z = 0 := by rw [← ZMod.natCast_zmod_val z, hr, Nat.cast_zero]
      exact hz (hzero ▸ IsSquare.zero)
    · intro hr
      have hone : z = 1 := by rw [← ZMod.natCast_zmod_val z, hr, Nat.cast_one]
      exact hz (hone ▸ IsSquare.one)
    · apply (legendreSym.eq_neg_one_iff' q).mpr
      simpa only [ZMod.natCast_zmod_val] using hz

def binarySign (e : ZMod 2) : ℤ := if e = 0 then 1 else -1

theorem binarySign_add (e f : ZMod 2) : binarySign (e + f) = binarySign e * binarySign f := by
  have h : ∀ e f : ZMod 2, binarySign (e + f) = binarySign e * binarySign f := by
    decide +kernel
  exact h e f

theorem binarySign_nat_mul (n : ℕ) (e : ZMod 2) :
    binarySign ((n : ZMod 2) * e) = binarySign e ^ n := by
  induction n with
  | zero => simp [binarySign]
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, binarySign_add, ih, pow_succ]

theorem binarySign_sum {ι : Type*} (S : Finset ι) (f : ι → ZMod 2) :
    binarySign (∑ i ∈ S, f i) = ∏ i ∈ S, binarySign (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [binarySign]
  | @insert i S hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, binarySign_add, ih]

def baseResidue (e₂ e₃ : ZMod 2) : ℕ :=
  if e₂ = 0 then (if e₃ = 0 then 23 else 17)
  else (if e₃ = 0 then 11 else 5)

theorem baseResidue_properties (e₂ e₃ : ZMod 2) :
    baseResidue e₂ e₃ < 24 ∧ (baseResidue e₂ e₃).Coprime 24 ∧
      baseResidue e₂ e₃ % 3 = 2 := by
  unfold baseResidue
  split_ifs <;> decide

theorem legendre_at_three_of_mod_three {p : ℕ} [Fact p.Prime]
    (hp : p % 3 = 2) : legendreSym 3 p = -1 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod : (p : ℤ) % 3 = 2 := by exact_mod_cast hp
  rw [legendreSym.mod]
  norm_num only [Nat.cast_ofNat]
  rw [hmod]
  decide +kernel

theorem baseResidue_realizes_signs {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (e₂ e₃ : ZMod 2) (hmod : p % 24 = baseResidue e₂ e₃) :
    legendreSym p 2 = binarySign e₂ ∧ legendreSym p 3 = binarySign e₃ := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : p % 3 = 2 := by
    have h := (baseResidue_properties e₂ e₃).2.2
    omega
  have hthree := legendre_at_three_of_mod_three hp3
  constructor
  · rw [legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight]
    unfold baseResidue at hmod
    unfold binarySign
    split_ifs at hmod ⊢ <;> omega
  · unfold baseResidue at hmod
    unfold binarySign
    split_ifs at hmod ⊢
    all_goals
      first
      | have hfour : p % 4 = 1 := by omega
        have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := p) (q := 3)
          hfour (by decide)
        norm_num only [Nat.cast_ofNat] at hrec
        linarith
      | have hfour : p % 4 = 3 := by omega
        have hrec := legendreSym.quadratic_reciprocity_three_mod_four (p := p) (q := 3)
          hfour (by decide)
        norm_num only [Nat.cast_ofNat] at hrec
        linarith

/-- The sign required before quadratic reciprocity. -/
def adjustedSign (b q : ℕ) (e : ZMod 2) : ℤ :=
  if b % 4 = 3 ∧ q % 4 = 3 then -binarySign e else binarySign e

theorem adjustedSign_values (b q : ℕ) (e : ZMod 2) :
    adjustedSign b q e = 1 ∨ adjustedSign b q e = -1 := by
  unfold adjustedSign binarySign
  split_ifs <;> norm_num

theorem legendre_of_local_residue {p q b r : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 3 < p) (hq : 5 ≤ q) (hb : p % 24 = b) (hr : p % q = r)
    (e : ZMod 2) (hs : legendreSym q r = adjustedSign b q e) :
    legendreSym p q = binarySign e := by
  have hmod : (p : ℤ) % (q : ℤ) = (r : ℤ) := by exact_mod_cast hr
  have hlocal : legendreSym q p = adjustedSign b q e := by
    rw [legendreSym.mod, hmod]
    exact hs
  have hpodd : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left (by omega)
  have hqodd : q % 2 = 1 := ((Fact.out : q.Prime).eq_two_or_odd).resolve_left (by omega)
  have hbp : p % 4 = b % 4 := by omega
  by_cases hp4 : p % 4 = 1
  · have hrec := legendreSym.quadratic_reciprocity_one_mod_four (q := q) hp4 (by omega)
    have hb4 : b % 4 ≠ 3 := by omega
    simp only [adjustedSign, hb4, false_and, ite_false] at hlocal
    exact hrec.symm.trans hlocal
  · have hp4' : p % 4 = 3 := by omega
    by_cases hq4 : q % 4 = 1
    · have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := q) (q := p)
        hq4 (by omega)
      have hq4' : q % 4 ≠ 3 := by omega
      simp only [adjustedSign, hq4', and_false, ite_false] at hlocal
      exact hrec.trans hlocal
    · have hq4' : q % 4 = 3 := by omega
      have hb4 : b % 4 = 3 := by omega
      have hrec := legendreSym.quadratic_reciprocity_three_mod_four (q := q) hp4' hq4'
      simp only [adjustedSign, hb4, hq4', and_self, ite_true] at hlocal
      linarith

end SimultaneousPrimitiveRoots
