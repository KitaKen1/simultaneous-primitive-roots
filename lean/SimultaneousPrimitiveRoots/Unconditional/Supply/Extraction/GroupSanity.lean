module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Objects

/-!
# Sanity lemmas for sub-systems of active groups

`restrictGroups 𝔊 P` (`Extraction/Objects.lean`) turns a set `P` of group indices into a system of
active groups, by listing the small and the big indices of `P` in increasing order. These lemmas
check that it is the sub-system the manuscript means (`[P-07:0527–0542]`: the active set
`P = S ∪ T`, `s_P = |P|`, the active one-mark weight `W_{1,q₀}`):

* `restrictGroups_numGroups`: `s_P = |P|`;
* `prod_restrictGroups`: a product over the groups of the sub-system is the product over `P`;
* `restrictGroups_oneMark`: `W_{1,q₀}` of the sub-system is `∏_{g ∈ P} q₀^{ω_g - 1} ω_g / V_g`;
* `restrictGroups_allPrimes_subset`: its primes are primes of the system.

They are used in the allocation step (`AllocationLink`), not in the proved chain.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

/-- `s_P = |P|`. -/
theorem restrictGroups_numGroups (𝔊 : ActiveGroups) (P : Finset 𝔊.Index) :
    (restrictGroups 𝔊 P).numGroups = P.card :=
  Finset.card_toLeft_add_card_toRight

/-- The primes of a sub-system are primes of the system. -/
theorem restrictGroups_allPrimes_subset (𝔊 : ActiveGroups) (P : Finset 𝔊.Index) :
    (restrictGroups 𝔊 P).allPrimes ⊆ 𝔊.allPrimes := by
  intro p hp
  obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hp
  rcases g with i | i
  · exact Finset.mem_biUnion.mpr
      ⟨Sum.inl (P.toLeft.orderEmbOfFin rfl i), Finset.mem_univ _, hg⟩
  · exact Finset.mem_biUnion.mpr
      ⟨Sum.inr (P.toRight.orderEmbOfFin rfl i), Finset.mem_univ _, hg⟩

/-- A product over the groups of the sub-system is the product over the index set. -/
theorem prod_restrictGroups (𝔊 : ActiveGroups) (P : Finset 𝔊.Index) (F : Finset ℕ → ℝ) :
    ∏ g : (restrictGroups 𝔊 P).Index, F ((restrictGroups 𝔊 P).group g) =
      ∏ g ∈ P, F (𝔊.group g) := by
  have hL : ∏ i : Fin P.toLeft.card, F (𝔊.group (Sum.inl (P.toLeft.orderEmbOfFin rfl i))) =
      ∏ a ∈ P.toLeft, F (𝔊.group (Sum.inl a)) := by
    have h := Finset.prod_map Finset.univ (P.toLeft.orderEmbOfFin rfl).toEmbedding
      (fun a => F (𝔊.group (Sum.inl a)))
    rw [Finset.map_orderEmbOfFin_univ] at h
    exact h.symm
  have hR : ∏ i : Fin P.toRight.card, F (𝔊.group (Sum.inr (P.toRight.orderEmbOfFin rfl i))) =
      ∏ a ∈ P.toRight, F (𝔊.group (Sum.inr a)) := by
    have h := Finset.prod_map Finset.univ (P.toRight.orderEmbOfFin rfl).toEmbedding
      (fun a => F (𝔊.group (Sum.inr a)))
    rw [Finset.map_orderEmbOfFin_univ] at h
    exact h.symm
  calc ∏ g : (restrictGroups 𝔊 P).Index, F ((restrictGroups 𝔊 P).group g)
      = (∏ i : Fin P.toLeft.card, F (𝔊.group (Sum.inl (P.toLeft.orderEmbOfFin rfl i)))) *
          ∏ i : Fin P.toRight.card, F (𝔊.group (Sum.inr (P.toRight.orderEmbOfFin rfl i))) :=
        Fintype.prod_sum_type _
    _ = (∏ a ∈ P.toLeft, F (𝔊.group (Sum.inl a))) *
          ∏ a ∈ P.toRight, F (𝔊.group (Sum.inr a)) := by rw [hL, hR]
    _ = ∏ g ∈ P.toLeft.disjSum P.toRight, F (𝔊.group g) :=
        (Finset.prod_disjSum P.toLeft P.toRight fun g => F (𝔊.group g)).symm
    _ = ∏ g ∈ P, F (𝔊.group g) := by rw [Finset.toLeft_disjSum_toRight]

/-- The active one-mark weight of the sub-system `P`:
`W_{1,q₀}(n) = ∏_{g ∈ P} q₀^{ω_g(n)-1} ω_g(n) / V_g` (`[P-07:0539–0542]`). -/
theorem restrictGroups_oneMark (𝔊 : ActiveGroups) (P : Finset 𝔊.Index) (q₀ : ℝ) (n : ℕ) :
    (restrictGroups 𝔊 P).oneMark q₀ n =
      ((∏ g ∈ P, markFactor q₀ (𝔊.group g) n : ℝ) : ℂ) := by
  rw [ActiveGroups.oneMark_eq]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (prod_restrictGroups 𝔊 P fun T => markFactor q₀ T n)

/-- The product of the coin probabilities over an active set (`[P-07:0527–0529]`,
(ext:active-term)):
`∏_{g ∈ P} s_g(u, v) = c₁^{|P|} · ∏_{g ∈ P} q₀^{ω_g(u)-1} ω_g(u)/V_g ·
  ∏_{g ∈ P} (q₀/j)^{ω_g(v)-1} ω_g(v)/V_g`. -/
theorem prod_coinProb (𝔊 : ActiveGroups) (c₁ q₀ : ℝ) (j u : ℕ) (P : Finset 𝔊.Index) :
    ∏ g ∈ P, coinProb 𝔊 c₁ q₀ j u g =
      c₁ ^ P.card * (∏ g ∈ P, markFactor q₀ (𝔊.group g) u) *
        ∏ g ∈ P, markFactor (q₀ / (j : ℝ)) (𝔊.group g) (u + 1) := by
  unfold coinProb
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
