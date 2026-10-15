import ArtinPrimitiveRoots.Sieve.Block
import SimultaneousPrimitiveRoots.Unconditional.Supply.ClassicalInputs

/-!
# The block sieve ([P] Lemma 2.6) from the vendored formalization of [A]

`ArtinPrimitiveRoots.Sieve.lem_block` (`vendor/ArtinPrimitiveRoots/Sieve/Block.lean`) is the block
sieve with bounded coefficients for a level `z ≥ 2`: finitely many weighted objects of an arbitrary
type, a bad condition at each designated prime `≤ z`, and a density `g` with `0 ≤ g(p) ≤ 1 - η₀`
and `∑_{w < p ≤ w²} g(p) ≤ C₀`.

The supply-side hypothesis `Supply.BlockSieve` (`Supply/ClassicalInputs.lean`) is the same
statement for objects indexed by natural numbers and every level `z ≥ 1`. For `2 ≤ z` it is
`lem_block`. For `1 ≤ z < 2` there is no designated prime; the sifted weight is the total weight
`X + r(1)`, and both assertions hold with any constant `M ≥ 1`.
-/

namespace SimultaneousPrimitiveRoots.Unconditional

open _root_.Classical in
/-- **The block sieve** ([P] Lemma 2.6, [S] `lem:sieve`) is a theorem: the supply-side hypothesis
`Supply.BlockSieve` holds. -/
theorem Supply.blockSieve : Supply.BlockSieve := by
  intro η₀ C₀ hη₀
  obtain ⟨K, -, H₀, hmain⟩ := ArtinPrimitiveRoots.Sieve.lem_block η₀ C₀ hη₀
  refine ⟨max K 1, H₀, ?_⟩
  intro Ω wt hwt z primes hz hprimes bad X hX g hg hC₀
  have hK1 : K ≤ max K 1 := le_max_left _ _
  have hM1 : (1 : ℝ) ≤ max K 1 := le_max_right _ _
  have hmain_nonneg : 0 ≤ X * ∏ p ∈ primes, (1 - g p) :=
    mul_nonneg hX (Finset.prod_nonneg fun p hp => by linarith [(hg p hp).2])
  have hrem_nonneg : ∀ y : ℝ, 0 ≤ Supply.sieveRemainderSum Ω wt bad X g primes y := fun y =>
    Finset.sum_nonneg fun D _ => abs_nonneg _
  by_cases hz2 : 2 ≤ z
  · -- the vendored lemma
    obtain ⟨h1, h2⟩ := hmain ℕ Ω wt hwt z hz2 primes hprimes bad X g hX hg hC₀
    refine ⟨fun h hh hev => ?_, ?_⟩
    · have h1' : |Supply.siftedWeight Ω wt bad primes - X * ∏ p ∈ primes, (1 - g p)| ≤
          K * Real.exp (-(h : ℝ)) * (X * ∏ p ∈ primes, (1 - g p)) +
            K * Supply.sieveRemainderSum Ω wt bad X g primes (z ^ (4 * h + 2)) := h1 h hev hh
      refine h1'.trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hK1 (Real.exp_pos _).le) hmain_nonneg
      · exact mul_le_mul_of_nonneg_right hK1 (hrem_nonneg _)
    · have h2' : Supply.siftedWeight Ω wt bad primes ≤
          K * (X * ∏ p ∈ primes, (1 - g p)) +
            K * Supply.sieveRemainderSum Ω wt bad X g primes (z ^ 10) := h2
      refine h2'.trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_right hK1 hmain_nonneg
      · exact mul_le_mul_of_nonneg_right hK1 (hrem_nonneg _)
  · -- no designated prime
    have hempty : primes = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => hz2 ?_
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprimes p hp).1.two_le
      exact h2.trans (hprimes p hp).2
    subst hempty
    have hsift : Supply.siftedWeight Ω wt bad ∅ = ∑ i ∈ Ω, wt i := by
      unfold Supply.siftedWeight
      refine Finset.sum_congr (Finset.filter_true_of_mem fun i _ p hp => ?_) fun _ _ => rfl
      exact absurd hp (Finset.notMem_empty p)
    have hrem : ∀ y : ℝ, 1 ≤ y →
        Supply.sieveRemainderSum Ω wt bad X g ∅ y = |(∑ i ∈ Ω, wt i) - X| := by
      intro y hy
      have hw : Supply.sieveWeight Ω wt bad ∅ = ∑ i ∈ Ω, wt i := by
        unfold Supply.sieveWeight
        refine Finset.sum_congr (Finset.filter_true_of_mem fun i _ p hp => ?_) fun _ _ => rfl
        exact absurd hp (Finset.notMem_empty p)
      unfold Supply.sieveRemainderSum
      rw [Finset.powerset_empty, Finset.filter_true_of_mem fun D hD => ?_, Finset.sum_singleton]
      · unfold Supply.sieveRemainder
        rw [hw, Finset.prod_empty, mul_one]
      · rw [Finset.mem_singleton.mp hD, Finset.prod_empty, Nat.cast_one]
        exact hy
    have hz1 : ∀ n : ℕ, (1 : ℝ) ≤ z ^ n := fun n => one_le_pow₀ hz
    have hT : |(∑ i ∈ Ω, wt i) - X| ≤ max K 1 * |(∑ i ∈ Ω, wt i) - X| :=
      le_mul_of_one_le_left (abs_nonneg _) hM1
    refine ⟨fun h _ _ => ?_, ?_⟩
    · rw [hsift, hrem _ (hz1 _), Finset.prod_empty, mul_one]
      have h0 : 0 ≤ max K 1 * Real.exp (-(h : ℝ)) * X :=
        mul_nonneg (mul_nonneg (le_trans zero_le_one hM1) (Real.exp_pos _).le) hX
      linarith
    · rw [hsift, hrem _ (hz1 _), Finset.prod_empty, mul_one]
      have hX' : X ≤ max K 1 * X := le_mul_of_one_le_left hX hM1
      linarith [le_abs_self ((∑ i ∈ Ω, wt i) - X)]

end SimultaneousPrimitiveRoots.Unconditional
