import ArtinPrimitiveRoots.TypeII.PP.Results
import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ClassicalInputs

/-!
# [P] Lemmas 2.3 and 2.4 from the vendored formalization

`Supply.EndpointProof.LongPrimePolynomial` and `Supply.EndpointProof.LogPhase`
(`Supply/EndpointProof/ClassicalInputs.lean`) are the statements of
`ArtinPrimitiveRoots.TypeII.PP.prime_polynomial` and `ArtinPrimitiveRoots.TypeII.PP.log_phase`
(`vendor/ArtinPrimitiveRoots/TypeII/PP/Results.lean`) for the intervals
`I = {n : N₁ ≤ n ≤ N₂}`, with the sums `primeDirichletPolynomial`, `residuePhaseSum` unfolded, the
`let`-bound abbreviations unfolded and `Real.rpow` written `^`.
-/

namespace SimultaneousPrimitiveRoots.Unconditional

/-- A set of natural numbers cut out by two real bounds is an interval. -/
theorem Supply.EndpointProof.isNatInterval_realBounds (N₁ N₂ : ℝ) :
    ArtinPrimitiveRoots.TypeII.IsNatInterval {p : ℕ | N₁ ≤ (p : ℝ) ∧ (p : ℝ) ≤ N₂} := by
  intro m n k hm hn hmin hmax
  simp only [Set.mem_setOf_eq] at hm hn ⊢
  constructor
  · have h : N₁ ≤ ((min m n : ℕ) : ℝ) := by
      rcases min_choice m n with h | h <;> rw [h]
      · exact hm.1
      · exact hn.1
    exact h.trans (by exact_mod_cast hmin)
  · have h : ((max m n : ℕ) : ℝ) ≤ N₂ := by
      rcases max_choice m n with h | h <;> rw [h]
      · exact hm.2
      · exact hn.2
    exact (show (k : ℝ) ≤ ((max m n : ℕ) : ℝ) by exact_mod_cast hmax).trans h

/-- **Long prime polynomials** ([P] Lemma 2.3) is a theorem: the supply-side hypothesis
`Supply.EndpointProof.LongPrimePolynomial` holds. -/
theorem Supply.EndpointProof.longPrimePolynomial : Supply.EndpointProof.LongPrimePolynomial := by
  intro τ η C A hτ hτη hη hC hA
  obtain ⟨B₀, C₀, x₀, hB₀, hC₀, hx₀, h⟩ :=
    ArtinPrimitiveRoots.TypeII.PP.prime_polynomial τ η C A hτ hτη hη hC hA
  refine ⟨B₀, C₀, x₀, hB₀, hC₀, hx₀,
    fun x hx N hN₁ hN₂ q hq hqL χ t ht₁ ht₂ N₁ N₂ hlo hhi => ?_⟩
  have h' := h x hx N hN₁ hN₂ q hq hqL χ t ht₁ ht₂
    {p : ℕ | N₁ ≤ (p : ℝ) ∧ (p : ℝ) ≤ N₂}
    (Supply.EndpointProof.isNatInterval_realBounds N₁ N₂)
    (fun p hp => ⟨hlo.trans hp.1, hp.2.trans hhi⟩)
  have hsum : ArtinPrimitiveRoots.TypeII.PP.primeDirichletPolynomial N q χ t
        {p : ℕ | N₁ ≤ (p : ℝ) ∧ (p : ℝ) ≤ N₂} =
      ∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun p : ℕ =>
          p.Prime ∧ N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N ∧ N₁ ≤ (p : ℝ) ∧ (p : ℝ) ≤ N₂),
        χ (p : ZMod q) *
          Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)) := by
    unfold ArtinPrimitiveRoots.TypeII.PP.primeDirichletPolynomial
    refine Finset.sum_congr ?_ fun p _ => rfl
    ext p
    simp only [Finset.mem_filter, Set.mem_setOf_eq]
  rw [hsum] at h'
  exact h'

/-- **Logarithmic phases on progressions** ([P] Lemma 2.4) is a theorem: the supply-side
hypothesis `Supply.EndpointProof.LogPhase` holds. -/
theorem Supply.EndpointProof.logPhase : Supply.EndpointProof.LogPhase := by
  obtain ⟨C₃, hC₃, h⟩ := ArtinPrimitiveRoots.TypeII.PP.log_phase
  refine ⟨C₃, hC₃, fun C hC => ?_⟩
  obtain ⟨C₀, x₀, hC₀, hx₀, h'⟩ := h C hC
  refine ⟨C₀, x₀, hC₀, hx₀, fun x hx N' hN₁ hN₂ q hq hqL a v hv₁ hv₂ N₁ N₂ hlo hhi => ?_⟩
  have h'' := h' x hx N' hN₁ hN₂ q hq hqL a v hv₁ hv₂ N₁ N₂ hlo hhi
  have hsum : ArtinPrimitiveRoots.TypeII.PP.residuePhaseSum N' q a v
        {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂} =
      ∑ n ∈ (Finset.range (⌊2 * N'⌋₊ + 1)).filter (fun n : ℕ =>
          N' ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N' ∧ (N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂) ∧
            (n : ZMod q) = a),
        Complex.exp (Complex.I * (v : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
    unfold ArtinPrimitiveRoots.TypeII.PP.residuePhaseSum
    refine Finset.sum_congr ?_ fun n _ => rfl
    ext n
    simp only [Finset.mem_filter, Set.mem_setOf_eq]
  rw [hsum] at h''
  exact h''

end SimultaneousPrimitiveRoots.Unconditional
