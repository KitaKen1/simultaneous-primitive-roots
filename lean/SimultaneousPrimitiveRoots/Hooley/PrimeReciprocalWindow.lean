module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import LeanPool.SelbergSieve4.Applications.PrimeCountingUpperBound

/-!
# Prime reciprocals over a multiplicative window

For primes `q ∈ (a, b]`, the sum of `1 / q` is at most `2C / log a` per doubling from `a`
to `b`, where `C` is a Chebyshev constant `π(n) ≤ C n / log n`. Group the primes by the
dyadic block `a 2^k < q ≤ a 2^(k+1)` containing them.

Only the Chebyshev upper bound of LeanPool is used; no Mertens asymptotic is needed.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Finset

/-- A prime `q` in the `k`-th block above `a` exceeds `a 2^k`. -/
theorem block_lower {a q : ℕ} (ha : 0 < a) (hq : a < q) :
    a * 2 ^ Nat.log 2 ((q - 1) / a) < q := by
  have hne : (q - 1) / a ≠ 0 := by
    apply Nat.pos_iff_ne_zero.mp
    exact Nat.div_pos (by omega) ha
  have hpow := Nat.pow_log_le_self 2 hne
  have hmul : a * 2 ^ Nat.log 2 ((q - 1) / a) ≤ a * ((q - 1) / a) :=
    Nat.mul_le_mul_left a hpow
  have hdiv : a * ((q - 1) / a) ≤ q - 1 := Nat.mul_div_le (q - 1) a
  omega

/-- A prime `q` in the `k`-th block above `a` is at most `a 2^(k+1)`. -/
theorem block_upper {a q : ℕ} (ha : 0 < a) :
    q ≤ a * 2 ^ (Nat.log 2 ((q - 1) / a) + 1) := by
  have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((q - 1) / a)
  have h := (Nat.div_lt_iff_lt_mul ha).mp hlt
  rw [Nat.succ_eq_add_one] at h
  have : q - 1 < a * 2 ^ (Nat.log 2 ((q - 1) / a) + 1) := by
    rw [mul_comm]
    exact h
  omega

/-- Primes at most `n` number `π(n)`. -/
theorem card_filter_prime_le_primeCounting {S : Finset ℕ} {n : ℕ}
    (hS : ∀ q ∈ S, q.Prime ∧ q ≤ n) : S.card ≤ Nat.primeCounting n := by
  have hsub : S ⊆ Nat.primesBelow (n + 1) := by
    intro q hq
    rw [Nat.mem_primesBelow]
    exact ⟨Nat.lt_succ_of_le (hS q hq).2, (hS q hq).1⟩
  calc S.card ≤ (Nat.primesBelow (n + 1)).card := card_le_card hsub
    _ = Nat.primeCounting' (n + 1) := Nat.primesBelow_card_eq_primeCounting' (n + 1)
    _ = Nat.primeCounting n := rfl

/-- **Prime reciprocals over a window.** With a Chebyshev constant `C` valid from `N`, the
primes `q ∈ (a, b]` satisfy `∑ 1/q ≤ (2C / log a) (log₂(b / a) + 1)` whenever `N ≤ a` and
`2 ≤ a`. -/
theorem prime_reciprocal_window_le {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hπ : ∀ n : ℕ, N ≤ n → (Nat.primeCounting n : ℝ) ≤ C * n / Real.log n)
    {a b : ℕ} (hN : N ≤ a) (ha : 2 ≤ a) :
    ∑ q ∈ (Ioc a b).filter Nat.Prime, (1 / (q : ℝ)) ≤
      2 * C / Real.log a * ((Nat.log 2 (b / a) : ℝ) + 1) := by
  classical
  set S := (Ioc a b).filter Nat.Prime with hSdef
  set J := Nat.log 2 (b / a) + 1 with hJ
  set j : ℕ → ℕ := fun q => Nat.log 2 ((q - 1) / a) with hj
  have ha0 : 0 < a := by omega
  have hmem : ∀ q ∈ S, q.Prime ∧ a < q ∧ q ≤ b := by
    intro q hq
    obtain ⟨hqI, hqp⟩ := mem_filter.mp hq
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hqI
    exact ⟨hqp, h1, h2⟩
  have hmaps : ∀ q ∈ S, j q ∈ range J := by
    intro q hq
    obtain ⟨_, _, hqb⟩ := hmem q hq
    apply mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    exact Nat.div_le_div_right (by omega)
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hlog_a : 0 < Real.log a := Real.log_pos (by exact_mod_cast (by omega : 1 < a))
  have hblock : ∀ k ∈ range J,
      ∑ q ∈ S with j q = k, (1 / (q : ℝ)) ≤ 2 * C / Real.log a := by
    intro k _
    set T := S.filter fun q => j q = k with hT
    have hlow : ∀ q ∈ T, (a : ℝ) * 2 ^ k < q := by
      intro q hq
      obtain ⟨hqS, hqk⟩ := mem_filter.mp hq
      obtain ⟨_, haq, _⟩ := hmem q hqS
      have h := block_lower ha0 haq
      simp only [hj] at hqk
      rw [hqk] at h
      exact_mod_cast h
    have hcard : (T.card : ℝ) ≤ Nat.primeCounting (a * 2 ^ (k + 1)) := by
      have h : T.card ≤ Nat.primeCounting (a * 2 ^ (k + 1)) := by
        apply card_filter_prime_le_primeCounting
        intro q hq
        obtain ⟨hqS, hqk⟩ := mem_filter.mp hq
        obtain ⟨hqp, _, _⟩ := hmem q hqS
        have h := block_upper (q := q) ha0
        simp only [hj] at hqk
        rw [hqk] at h
        exact ⟨hqp, h⟩
      exact_mod_cast h
    have hNle : N ≤ a * 2 ^ (k + 1) :=
      hN.trans (Nat.le_mul_of_pos_right a (pow_pos (by norm_num : 0 < 2) _))
    have hπk := hπ (a * 2 ^ (k + 1)) hNle
    have hpow0 : (0 : ℝ) < 2 ^ k := by positivity
    have ha0' : (0 : ℝ) < a := by exact_mod_cast ha0
    have hbig : Real.log a ≤ Real.log ((a * 2 ^ (k + 1) : ℕ) : ℝ) := by
      apply Real.log_le_log ha0'
      push_cast
      have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hlogbig : 0 < Real.log ((a * 2 ^ (k + 1) : ℕ) : ℝ) := hlog_a.trans_le hbig
    calc ∑ q ∈ T, (1 / (q : ℝ))
        ≤ ∑ _q ∈ T, 1 / ((a : ℝ) * 2 ^ k) := by
          apply sum_le_sum
          intro q hq
          exact one_div_le_one_div_of_le (by positivity) (hlow q hq).le
      _ = (T.card : ℝ) * (1 / ((a : ℝ) * 2 ^ k)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (Nat.primeCounting (a * 2 ^ (k + 1)) : ℝ) * (1 / ((a : ℝ) * 2 ^ k)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ C * ((a * 2 ^ (k + 1) : ℕ) : ℝ) / Real.log ((a * 2 ^ (k + 1) : ℕ) : ℝ) *
            (1 / ((a : ℝ) * 2 ^ k)) :=
          mul_le_mul_of_nonneg_right hπk (by positivity)
      _ = 2 * C / Real.log ((a * 2 ^ (k + 1) : ℕ) : ℝ) := by
          push_cast
          field_simp
          ring
      _ ≤ 2 * C / Real.log a :=
          div_le_div_of_nonneg_left (by positivity) hlog_a hbig
  calc ∑ k ∈ range J, ∑ q ∈ S with j q = k, (1 / (q : ℝ))
      ≤ ∑ _k ∈ range J, 2 * C / Real.log a := sum_le_sum hblock
    _ = 2 * C / Real.log a * ((Nat.log 2 (b / a) : ℝ) + 1) := by
        rw [sum_const, card_range, nsmul_eq_mul, hJ]
        push_cast
        ring

/-- A Chebyshev constant valid from some point on, with a nonnegative constant. -/
theorem exists_chebyshev_constant : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → (Nat.primeCounting n : ℝ) ≤ C * n / Real.log n := by
  obtain ⟨N, C, h⟩ := PrimeUpperBound.pi_le_mul
  refine ⟨max C 0, le_max_right _ _, max N 2, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  calc (Nat.primeCounting n : ℝ) ≤ C * n / Real.log n := h n hnN
    _ ≤ max C 0 * n / Real.log n := by
        apply div_le_div_of_nonneg_right _ hlog
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg n)

/-- `Nat.log 2 m` is at most `log m / log 2`. -/
theorem natLog_two_le_log_div {m : ℕ} (hm : m ≠ 0) :
    (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have hpow := Nat.pow_log_le_self 2 hm
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2]
  have h : Real.log ((2 : ℝ) ^ Nat.log 2 m) ≤ Real.log m :=
    Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  rwa [Real.log_pow] at h

end SimultaneousPrimitiveRoots
