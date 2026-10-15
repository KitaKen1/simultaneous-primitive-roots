import SimultaneousPrimitiveRootsFinal.MainClaim
import SimultaneousPrimitiveRoots.OrderObstruction
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Squarefree

namespace SimultaneousPrimitiveRootsChallenge

open SimultaneousPrimitiveRoots in
theorem natCard_eq_primeCount (A : Finset ℕ) (x : ℝ) :
    (Nat.card {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ p.Prime ∧
        ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} : ℝ) = primeCount A x := by
  classical
  unfold primeCount
  congr 1
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
  have hmem : p ∈ goodPrimes A x ↔ p ∈ Finset.range (⌊2 * x⌋₊ + 1) ∧
      (x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ SimultaneousAt A p) := by
    simp only [goodPrimes, Finset.mem_filter]
  rw [hmem, Finset.mem_range]
  simp only [SimultaneousAt, PrimitiveRootMod]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h2), h1, h2, h3⟩
  · rintro ⟨_, h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩


/-- The square condition implies a positive dyadic lower bound. -/
theorem positive_lower_density
    (A : Finset ℕ) (hA : A.Nonempty) (h2 : ∀ a ∈ A, 2 ≤ a)
    (hsq : ∀ B : Finset ℕ, B ⊆ A → Odd B.card → ¬ IsSquare (∏ a ∈ B, a)) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      c * (x / Real.log x) ≤
        (Nat.card {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ p.Prime ∧
          ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} : ℝ) := by
  obtain ⟨c, hc, x₀, hx₀, h⟩ := SimultaneousPrimitiveRoots.mainClaim A ⟨hA, h2, hsq⟩
  exact ⟨c, hc, x₀, hx₀, fun x hx =>
    (h x hx).trans_eq (natCard_eq_primeCount A x).symm⟩

private theorem square_condition_of_prime_bases
    (A : Finset ℕ) (hA : ∀ a ∈ A, a.Prime) :
    ∀ B : Finset ℕ, B ⊆ A → Odd B.card → ¬ IsSquare (∏ a ∈ B, a) := by
  classical
  intro B hBA hodd hsquare
  have hB : ∀ p ∈ B, p.Prime := fun p hp => hA p (hBA hp)
  have hsf : Squarefree (∏ p ∈ B, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      (fun p hp => (hB p hp).squarefree)
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hB p hp) (hB q hq)).mpr hpq)
  obtain ⟨r, hr⟩ := hsquare
  have hr1 : r = 1 := Nat.isUnit_iff.mp (hsf r (by rw [hr]))
  have hprod : ∏ p ∈ B, p = 1 := by simpa [hr1] using hr
  have hnonempty : B.Nonempty := Finset.card_pos.mp hodd.pos
  obtain ⟨p, hp⟩ := hnonempty
  have hdiv : p ∣ ∏ q ∈ B, q := Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
  rw [hprod] at hdiv
  exact (hB p hp).not_dvd_one hdiv

/-- The conclusion of OpenAI [OAI26, Theorem 1.1] without its four analytic hypotheses. -/
theorem simultaneous_primitive_roots_unconditional :
    ∀ A : Finset ℕ, A.Nonempty →
      (∀ a ∈ A, a.Prime) →
      ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        c * (x / (Real.log x) ^ 2) ≤
          (Nat.card {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ p.Prime ∧
            ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} : ℝ) := by
  classical
  intro A hA hprime
  obtain ⟨c, hc, x₀, hx₀, hbound⟩ := positive_lower_density A hA
    (fun a ha => (hprime a ha).two_le) (square_condition_of_prime_bases A hprime)
  refine ⟨c / 2, by positivity, max (x₀ + 1) (Real.exp 1 + 2), ?_, ?_⟩
  · have := le_max_left (x₀ + 1) (Real.exp 1 + 2)
    linarith
  intro x hx
  have hxstart : x₀ + 1 ≤ x := (le_max_left _ _).trans hx
  have hxexp : Real.exp 1 + 2 ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := by linarith [Real.exp_pos (1 : ℝ)]
  let n : ℕ := ⌊x⌋₊
  let y : ℝ := n
  have hxy : x < y + 1 := Nat.lt_floor_add_one x
  have hyle : y ≤ x := Nat.floor_le hxpos.le
  have hystart : x₀ ≤ y := by linarith
  have hy2 : 2 ≤ y := hx₀.trans hystart
  have hyn2 : 2 ≤ n := by
    have h : (2 : ℝ) ≤ (n : ℝ) := hy2
    exact_mod_cast h
  have hypos : 0 < y := by linarith
  have hyhalf : x / 2 ≤ y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogx : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (1 : ℝ)) (show Real.exp 1 ≤ x by linarith)
    simpa using h
  have hlogxpos : 0 < Real.log x := by linarith
  have hlogs : Real.log y ≤ Real.log x := Real.log_le_log hypos hyle
  have hweak : x / Real.log x ^ 2 ≤ x / Real.log x :=
    div_le_div_of_nonneg_left hxpos.le hlogxpos (by nlinarith)
  have hscale : (x / 2) / Real.log x ≤ y / Real.log y := by
    exact (div_le_div_of_nonneg_right hyhalf hlogxpos.le).trans
      (div_le_div_of_nonneg_left hypos.le hlogy hlogs)
  have hrealbound : (c / 2) * (x / Real.log x ^ 2) ≤
      c * (y / Real.log y) := by
    calc
      (c / 2) * (x / Real.log x ^ 2) ≤ (c / 2) * (x / Real.log x) :=
        mul_le_mul_of_nonneg_left hweak (by positivity)
      _ = c * ((x / 2) / Real.log x) := by ring
      _ ≤ c * (y / Real.log y) := mul_le_mul_of_nonneg_left hscale hc.le
  have hfinite : Set.Finite {p : ℕ | x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ p.Prime ∧
      ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} :=
    (Set.finite_le_nat ⌊2 * x⌋₊).subset (fun p hp => Nat.le_floor hp.2.1.le)
  have : Finite {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ p.Prime ∧
      ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} := hfinite.to_subtype
  have hcounts :
      Nat.card {p : ℕ // y < (p : ℝ) ∧ (p : ℝ) ≤ 2 * y ∧ p.Prime ∧
        ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} ≤
      Nat.card {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ p.Prime ∧
        ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} := by
    refine Nat.card_le_card_of_injective
      (fun (p : {p : ℕ // y < (p : ℝ) ∧ (p : ℝ) ≤ 2 * y ∧ p.Prime ∧
          ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1}) =>
        (⟨p.1, ?_⟩ : {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ p.Prime ∧
          ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1}))
      (by
        intro p q h
        apply Subtype.ext
        exact congrArg (fun r : {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ p.Prime ∧
          ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} => r.1) h)
    have hnp : n < p.1 := by
      have hh : (n : ℝ) < (p.1 : ℝ) := p.2.1
      exact_mod_cast hh
    have hsucc : (n : ℝ) + 1 ≤ (p.1 : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hnp
    have hleft : x < (p.1 : ℝ) := hxy.trans_le hsucc
    have hne : (p.1 : ℝ) ≠ 2 * y := by
      intro heq
      have hnat : p.1 = 2 * n := by
        change (p.1 : ℝ) = 2 * (n : ℝ) at heq
        exact_mod_cast heq
      have hprime' := p.2.2.2.1
      rw [hnat] at hprime'
      rcases Nat.prime_mul_iff.mp hprime' with h | h <;> omega
    exact ⟨hleft, (lt_of_le_of_ne p.2.2.1 hne).trans_le (by linarith), p.2.2.2⟩
  exact hrealbound.trans ((hbound y hystart).trans (by exact_mod_cast hcounts))


/-- If the square condition fails, no odd prime works. -/
theorem square_condition_necessary
    (A : Finset ℕ)
    (hsq : ¬ (∀ B : Finset ℕ, B ⊆ A → Odd B.card → ¬ IsSquare (∏ a ∈ B, a))) :
    ∀ p : ℕ, 2 < p →
      ¬ (p.Prime ∧ ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1) := by
  exact fun p hp => SimultaneousPrimitiveRoots.no_simultaneousAt_of_not_squareCondition hsq hp

end SimultaneousPrimitiveRootsChallenge

#print axioms SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots_unconditional
#print axioms SimultaneousPrimitiveRootsChallenge.positive_lower_density
#print axioms SimultaneousPrimitiveRootsChallenge.square_condition_necessary
