module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Nat.Factors

/-!
# The factorial coefficient estimate

`primePowerNorm : PrimePowerNorm` (`[P-06:0781–0789]`): "Unique factorization gives squared
coefficient norm for `P_s^{j_0}` at most `j_0! (P^{-2} ∑_{p_s ≍ P} |b_s(p_s)|²)^{j_0}`", the
"factorial prime-polynomial coefficient estimate, as in [Soundararajan 2009, Lemma 3]".

For a finite set of primes `G`, coefficients `b` and `j ≥ 0`, the coefficient of `n` in
`(∑_{p ∈ G} b_p p^{it})^j` is the sum of `∏_i b_{p_i}` over the ordered `j`-tuples of elements
of `G` with product `n`. There are at most `j!` such tuples (`card_filter_prod_le`: by unique
factorization each is a rearrangement of the list of prime factors of `n`), so by Cauchy–Schwarz
the squared coefficient is at most `j! ∑_{tuples} ∏_i |b_{p_i}|²`, and the sum over `n` of the
right sides is `j! (∑_{p ∈ G} |b_p|²)^j`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-- An integer has at most `j!` representations as an ordered product of `j` primes. -/
theorem card_filter_prod_le {G : Finset ℕ} (hG : ∀ p ∈ G, p.Prime) (j n : ℕ) :
    ((Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n)).card ≤
      j.factorial := by
  by_cases hne : ((Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n)).Nonempty
  · obtain ⟨f₀, hf₀⟩ := hne
    have hperm : ∀ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
        List.ofFn f ∈ (n.primeFactorsList.permutations).toFinset := by
      intro f hf
      obtain ⟨hfG, hfn⟩ := Finset.mem_filter.mp hf
      have hprime : ∀ p ∈ List.ofFn f, p.Prime := by
        intro p hp
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
        rw [← hi]
        exact hG _ (Fintype.mem_piFinset.mp hfG i)
      have hprod : (List.ofFn f).prod = n := by
        rw [List.prod_ofFn]
        exact hfn
      exact List.mem_toFinset.mpr
        (List.mem_permutations.mpr (Nat.primeFactorsList_unique hprod hprime))
    have hlen : n.primeFactorsList.length = j := by
      have h1 := List.mem_permutations.mp (List.mem_toFinset.mp (hperm f₀ hf₀))
      rw [← h1.length_eq, List.length_ofFn]
    calc ((Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n)).card
        ≤ (n.primeFactorsList.permutations).toFinset.card :=
          Finset.card_le_card_of_injOn (fun f => List.ofFn f) (fun f hf => hperm f hf)
            (fun f _ g _ h => List.ofFn_injective h)
      _ ≤ (n.primeFactorsList.permutations).length := List.toFinset_card_le _
      _ = j.factorial := by rw [List.length_permutations, hlen]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

/-- **The factorial coefficient estimate** (`[P-06:0781–0789]`). -/
theorem primePowerNorm : PrimePowerNorm := by
  intro G hG b j
  have hnorm : ∀ f : Fin j → ℕ, ‖∏ i, b (f i)‖ ^ 2 = ∏ i, ‖b (f i)‖ ^ 2 := fun f => by
    rw [norm_prod, Finset.prod_pow]
  have hfiber : ∀ n : ℕ,
      ‖∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
          ∏ i, b (f i)‖ ^ 2 ≤
        (j.factorial : ℝ) *
          ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
            ∏ i, ‖b (f i)‖ ^ 2 := by
    intro n
    have h1 : ‖∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
          ∏ i, b (f i)‖ ≤
        ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
          ‖∏ i, b (f i)‖ := norm_sum_le _ _
    have h2 : (∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
          ‖∏ i, b (f i)‖) ^ 2 ≤
        (((Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n)).card : ℝ) *
          ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
            ‖∏ i, b (f i)‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    have h3 : ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
          ‖∏ i, b (f i)‖ ^ 2 =
        ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
          ∏ i, ‖b (f i)‖ ^ 2 := Finset.sum_congr rfl fun f _ => hnorm f
    have h4 : (((Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n)).card : ℝ) ≤
        (j.factorial : ℝ) := by
      exact_mod_cast card_filter_prod_le hG j n
    have h5 : 0 ≤ ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
        ∏ i, ‖b (f i)‖ ^ 2 :=
      Finset.sum_nonneg fun f _ => Finset.prod_nonneg fun i _ => sq_nonneg _
    rw [h3] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
      (h2.trans (mul_le_mul_of_nonneg_right h4 h5))
  have hfib : ∑ n ∈ (Fintype.piFinset fun _ : Fin j => G).image (fun f => ∏ i, f i),
        ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
          ∏ i, ‖b (f i)‖ ^ 2 =
      ∑ f ∈ Fintype.piFinset fun _ : Fin j => G, ∏ i, ‖b (f i)‖ ^ 2 :=
    Finset.sum_fiberwise_of_maps_to (fun f hf => Finset.mem_image_of_mem _ hf) _
  have hprod : ∑ f ∈ Fintype.piFinset fun _ : Fin j => G, ∏ i, ‖b (f i)‖ ^ 2 =
      (∑ p ∈ G, ‖b p‖ ^ 2) ^ j := by
    have h1 : ∑ f ∈ Fintype.piFinset fun _ : Fin j => G, ∏ i, ‖b (f i)‖ ^ 2 =
        ∏ _i : Fin j, ∑ p ∈ G, ‖b p‖ ^ 2 :=
      (Finset.prod_univ_sum (fun _ : Fin j => G) (fun _ p => ‖b p‖ ^ 2)).symm
    rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ∑ n ∈ (Fintype.piFinset fun _ : Fin j => G).image (fun f => ∏ i, f i),
        ‖∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
            ∏ i, b (f i)‖ ^ 2
      ≤ ∑ n ∈ (Fintype.piFinset fun _ : Fin j => G).image (fun f => ∏ i, f i),
          (j.factorial : ℝ) *
            ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
              ∏ i, ‖b (f i)‖ ^ 2 := Finset.sum_le_sum fun n _ => hfiber n
    _ = (j.factorial : ℝ) *
          ∑ n ∈ (Fintype.piFinset fun _ : Fin j => G).image (fun f => ∏ i, f i),
            ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
              ∏ i, ‖b (f i)‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ = (j.factorial : ℝ) * (∑ p ∈ G, ‖b p‖ ^ 2) ^ j := by rw [hfib, hprod]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
