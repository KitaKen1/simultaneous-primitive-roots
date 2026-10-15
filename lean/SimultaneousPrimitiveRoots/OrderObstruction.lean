module

public import SimultaneousPrimitiveRoots.Statement
public import Mathlib.Tactic

@[expose] public section

namespace SimultaneousPrimitiveRoots

theorem primitiveRootMod_iff_prime_tests {a p : ℕ} (hp : p.Prime) :
    PrimitiveRootMod a p ↔ ¬ p ∣ a ∧
      ∀ q : ℕ, q.Prime → q ∣ p - 1 → (a : ZMod p) ^ ((p - 1) / q) ≠ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpge := hp.two_le
  constructor
  · rintro ⟨ha, ho⟩
    refine ⟨ha, fun q hq hqp => ?_⟩
    apply pow_ne_one_of_lt_orderOf
    · have := Nat.div_pos (Nat.le_of_dvd (by omega) hqp) hq.pos
      omega
    · rw [ho]
      exact Nat.div_lt_self (by omega) hq.one_lt
  · rintro ⟨ha, htests⟩
    refine ⟨ha, orderOf_eq_of_pow_and_pow_div_prime (by omega) ?_ htests⟩
    exact ZMod.pow_card_sub_one_eq_one (fun hz => ha ((ZMod.natCast_eq_zero_iff a p).mp hz))

theorem exists_prime_obstruction {a p : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a)
    (h : ¬ PrimitiveRootMod a p) :
    ∃ q : ℕ, q.Prime ∧ q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1 := by
  rw [primitiveRootMod_iff_prime_tests hp] at h
  push Not at h
  exact h ha

/-- After the small prime tests, every obstruction is either the marked prime
or a prime divisor of the remaining cofactor. -/
theorem obstruction_split {a p Q r Y : ℕ} (hp : p.Prime) (hQ : Q.Prime)
    (hfactor : p - 1 = Q * r) (ha : ¬ p ∣ a)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ≤ Y →
      (a : ZMod p) ^ ((p - 1) / q) ≠ 1)
    (hfail : ¬ PrimitiveRootMod a p) :
    ∃ q : ℕ, q.Prime ∧ Y < q ∧ (q = Q ∨ q ∣ r) ∧
      (a : ZMod p) ^ ((p - 1) / q) = 1 := by
  obtain ⟨q, hq, hqp, heq⟩ := exists_prime_obstruction hp ha hfail
  refine ⟨q, hq, ?_, ?_, heq⟩
  · by_contra hn
    exact hsmall q hq hqp (by omega) heq
  · rw [hfactor] at hqp
    rcases hq.dvd_mul.mp hqp with hqQ | hqr
    · exact Or.inl ((Nat.dvd_prime hQ).mp hqQ |>.resolve_left hq.ne_one)
    · exact Or.inr hqr

theorem primitiveRootMod_not_isSquare {a p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (ha : PrimitiveRootMod a p) : ¬ IsSquare (a : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  intro hs
  have hne : (a : ZMod p) ≠ 0 := by
    exact fun hz => ha.1 ((ZMod.natCast_eq_zero_iff a p).mp hz)
  have hpow := (ZMod.euler_criterion p hne).mp hs
  have hle := orderOf_le_of_pow_eq_one (by omega : 0 < p / 2) hpow
  rw [ha.2] at hle
  omega

theorem primitiveRootMod_legendre {a p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (ha : PrimitiveRootMod a p) : legendreSym p a = -1 := by
  exact (legendreSym.eq_neg_one_iff' p).mpr (primitiveRootMod_not_isSquare Fact.out hp2 ha)

theorem squareCondition_of_simultaneousAt {A : Finset ℕ} {p : ℕ}
    (hp2 : 2 < p) (h : SimultaneousAt A p) : SquareCondition A := by
  let : Fact p.Prime := ⟨h.1⟩
  intro B hBA hodd hs
  have hsym : legendreSym p (∏ a ∈ B, (a : ℤ)) = (-1 : ℤ) ^ B.card := by
    change (legendreSym.hom p) (∏ a ∈ B, (a : ℤ)) = _
    rw [map_prod]
    apply Finset.prod_eq_pow_card
    intro a ha
    exact primitiveRootMod_legendre hp2 (h.2 a (hBA ha))
  have hnonzero : ((∏ a ∈ B, a : ℕ) : ZMod p) ≠ 0 := by
    push_cast
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact fun hz => (h.2 a (hBA ha)).1 ((ZMod.natCast_eq_zero_iff a p).mp hz)
  have hsq : IsSquare ((∏ a ∈ B, a : ℕ) : ZMod p) := by
    rcases hs with ⟨r, hr⟩
    exact ⟨(r : ZMod p), by simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ZMod p)) hr⟩
  have hone := (legendreSym.eq_one_iff' p hnonzero).mpr hsq
  have hminus : legendreSym p (∏ a ∈ B, (a : ℤ)) = -1 := by
    rw [hsym, hodd.neg_one_pow]
  simp only [Nat.cast_prod] at hone
  omega

theorem no_simultaneousAt_of_not_squareCondition {A : Finset ℕ}
    (hA : ¬ SquareCondition A) {p : ℕ} (hp2 : 2 < p) : ¬ SimultaneousAt A p :=
  fun hp => hA (squareCondition_of_simultaneousAt hp2 hp)

end SimultaneousPrimitiveRoots
