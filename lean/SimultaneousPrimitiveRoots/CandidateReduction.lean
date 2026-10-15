module

public import SimultaneousPrimitiveRoots.SmallOrder

@[expose] public section

namespace SimultaneousPrimitiveRoots

/-- Nonsquareness handles q = 2; the chosen progressions exclude all other small q. -/
theorem small_prime_tests {a p Y : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (ha : ¬ p ∣ a) (hsq : ¬ IsSquare (a : ZMod p))
    (havoid : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≤ Y → ¬ q ∣ p - 1) :
    ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ≤ Y →
      (a : ZMod p) ^ ((p - 1) / q) ≠ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  intro q hq hqp hqY
  by_cases hq2 : q = 2
  · subst q
    have hpodd := hp.eq_two_or_odd.resolve_left (by omega)
    have heq : (p - 1) / 2 = p / 2 := by omega
    rw [heq]
    exact fun hz => hsq ((ZMod.euler_criterion p
      (fun hzero => ha ((ZMod.natCast_eq_zero_iff a p).mp hzero))).mpr hz)
  · exact (havoid q hq hq2 hqY hqp).elim

/-- The exact two exceptional sets needed by the counting argument. -/
theorem candidate_failure_cases {a p Q r Y N : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) (ha2 : 2 ≤ a)
    (ha : ¬ p ∣ a) (hsq : ¬ IsSquare (a : ZMod p))
    (havoid : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≤ Y → ¬ q ∣ p - 1)
    (hQ : Q.Prime) (hfactor : p - 1 = Q * r) (hrN : r ≤ N)
    (hfail : ¬ PrimitiveRootMod a p) :
    p ∣ smallOrderProduct a N ∨
      ∃ q : ℕ, q.Prime ∧ Y < q ∧ q ≤ N ∧ q ∣ p - 1 ∧
        (a : ZMod p) ^ ((p - 1) / q) = 1 := by
  have hr : 0 < r := by
    by_contra hn
    have hrzero : r = 0 := by omega
    simp only [hrzero, mul_zero] at hfactor
    omega
  obtain ⟨q, hq, hqY, hcases, hpow⟩ :=
    obstruction_split hp hQ hfactor ha (small_prime_tests hp hp2 ha hsq havoid) hfail
  rcases hcases with rfl | hqr
  · exact Or.inl (marked_prime_obstruction_dvd_product ha2 hQ hr hrN hfactor hpow)
  · refine Or.inr ⟨q, hq, hqY, (Nat.le_of_dvd hr hqr).trans hrN, ?_, hpow⟩
    rw [hfactor]
    exact dvd_mul_of_dvd_right hqr Q

end SimultaneousPrimitiveRoots
