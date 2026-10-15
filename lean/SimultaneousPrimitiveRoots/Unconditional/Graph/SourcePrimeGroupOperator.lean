module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourceGhostCoefficients
public import SimultaneousPrimitiveRoots.Unconditional.Graph.PrimeGroupGhostNorm
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostGeneralRows
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostFockSymmetry

/-!
# Completed ghost operators with the actual source coefficients and prime law

One weight v is chosen before all visits and prime groups. Every admissible
actual tilted law gives a bounded operator with the exact original normalized
counting matrix and symmetric outputs. Prime sizes remain explicit; eventual
source prime choice, tensors and full conditional transference are not asserted.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

theorem exists_source_prime_group_continuous_operators {I : Type*}
    (R : ℕ → Type*) [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (q ρ Vplus : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hρ : 0 < ρ)
    (hgap : Real.sqrt q < ρ ^ 2) :
    ∃ v : ℝ, 1 < v ∧ ∀ (s : Finset ℕ), s.Nonempty →
      (∀ p ∈ s, Nat.Prime p) → ∀ (visits : Finset I) (η : I → ℝ),
      (∀ i ∈ visits, η i ≤ 1) → (∀ p ∈ s, 2 * visits.card ≤ p) →
      primeGroupReciprocalMass s ≤ Vplus → ∀ (qi γ : ℝ),
      (qi = q ∨ qi = Real.sqrt q) → 0 ≤ γ → γ ≤ 2 →
      ∃ T : lp (fun _ : InfiniteMemory (Σ p : s, R p.val) => ℂ) 2 →L[ℂ]
        lp (fun _ : InfiniteMemory (Σ p : s, R p.val) => ℂ) 2,
        ‖T‖ ≤ Real.sqrt (Real.exp ((2 * max 1 Vplus / ρ) * v * 2) *
          Real.exp ((1 / ρ) * v * 2)) ∧
        (∀ x y, T (lpCoordinateVector y) x =
          normalizedInfiniteGhostKernel (fun p : s => tiltedPrimeGroupLaw s visits η p.val)
            (sourceGhostA qi ρ) (sourceGhostD qi ρ)
            (γ * sourceGhostC (primeGroupReciprocalMass s) qi ρ) x y) ∧
        (∀ f (x : InfiniteMemory (Σ p : s, R p.val)) (σ : Equiv.Perm (Fin x.1)),
          T f ⟨x.1, x.2 ∘ σ⟩ = T f x) := by
  obtain ⟨v, hv, hcoef⟩ := exists_source_ghost_uniform_weight q ρ Vplus hq0 hq1 hρ hgap
  refine ⟨v, hv, ?_⟩
  intro s hne hp visits η hη hsize hV qi γ hqi hγ0 hγ
  have hV0 : 0 ≤ primeGroupReciprocalMass s :=
    (prime_group_reciprocal_mass_pos s hne hp).le
  obtain ⟨hA, hbaseD, hbaseC, hD, hC⟩ :=
    hcoef qi (primeGroupReciprocalMass s) γ hqi hV0 hV hγ0 hγ
  let ν : s → ℝ := fun p => tiltedPrimeGroupLaw s visits η p.val
  have hν : ∀ p, 0 < ν p := tilted_prime_group_subtype_pos s hne hp visits η hη hsize
  have hM : ∑ p, ν p ≤ 2 := tilted_prime_group_subtype_total_le_two s hne hp visits η hη hsize
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  let T := infiniteGhostContinuousOperator (R := fun p : s => R p.val) ν
    (sourceGhostA qi ρ) (sourceGhostD qi ρ)
    (γ * sourceGhostC (primeGroupReciprocalMass s) qi ρ)
    v (2 * max 1 Vplus / ρ) (1 / ρ) 2 hν hA hv0 hbaseD.le hbaseC.le hC hD hM
  refine ⟨T, ?_, ?_, ?_⟩
  · exact infinite_ghost_continuous_operator_opnorm_bound ν _ _ _
      v (2 * max 1 Vplus / ρ) (1 / ρ) 2 hν hA hv0 hbaseD.le hbaseC.le hC hD hM
  · intro x y
    exact infinite_ghost_continuous_operator_matrix ν _ _ _
      v (2 * max 1 Vplus / ρ) (1 / ρ) 2 hν hA hv0 hbaseD.le hbaseC.le hC hD hM x y
  · intro f x σ
    exact infinite_ghost_continuous_operator_symmetric ν _ _ _
      v (2 * max 1 Vplus / ρ) (1 / ρ) 2 hν hA hv0 hbaseD.le hbaseC.le hC hD hM f x σ

end SimultaneousPrimitiveRoots.Unconditional.Graph
