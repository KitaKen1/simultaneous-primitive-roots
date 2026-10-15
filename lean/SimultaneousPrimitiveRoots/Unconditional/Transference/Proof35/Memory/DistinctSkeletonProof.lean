module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.HistorySkeleton
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The memory path integral by skeletons: `DistinctSkeleton`

Source: `verification/stage7-sources/S-02.tex`, lines 516–534 (`[S-02:0516–0534]`).

`distinctSkeleton : DistinctSkeleton` is proved here:

`distinctSum Bc θ = E_y Σ_sk common(θ, y, sk) · memSum(sk, Bc)`,

the mean over the small residues `y` of the sum over the skeletons of the common part times the
memory sum.

A history is its small residues, its skeleton and its decoration (`histSkelEquiv`); its weight is
the Haar mass, its common part and its memory part (`History.weight_eq`); the common part is that
of the skeleton (`Skel.commonPart_hist`); the memory part and the births do not depend on the
small residues (`Skel.memPart_hist`, `Skel.birth_hist`). So the sum over the decorations of a
skeleton, with the distinct-birth rule, is the Haar mass times the common part times `Skel.memSum`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-- **(B) The memory path integral by skeletons** [S-02:0516–0534]:
`distinctSum Bc θ = E_y Σ_sk common(θ, y, sk) · memSum(sk, Bc)`, for every family of groups, all
parameters and every cutoff. -/
theorem distinctSkeleton : DistinctSkeleton := by
  intro S B _ _ _ _ 𝒢 J ℓ N _ D Bc θ
  classical
  -- the term of the history of `(y, sk, d)`
  have hw : ∀ (y : ResVec (smallPrimes 𝒢)) (sk : Skel D) (d : Deco 𝒢 J ℓ Bc D.n),
      (if Graph.PerformedBirthsDistinct (sk.hist y d).birth then (sk.hist y d).weight θ
        else 0) =
        ((haarMass (smallPrimes 𝒢) : ℝ) : ℂ) * (sk.common θ y *
          (((if Graph.PerformedBirthsDistinct (sk.hist (fun _ => 0) d).birth then
            (sk.hist (fun _ => 0) d).memPart else 0 : ℝ)) : ℂ)) := by
    intro y sk d
    rw [sk.birth_hist y (fun _ => 0) d, History.weight_eq, sk.commonPart_hist,
      sk.memPart_hist y d, sk.memPart_hist (fun _ => 0) d]
    by_cases hb : Graph.PerformedBirthsDistinct (sk.hist (fun _ => 0) d).birth
    · rw [if_pos hb, if_pos hb]
      ring
    · rw [if_neg hb, if_neg hb, Complex.ofReal_zero, mul_zero, mul_zero]
  -- the sum over the histories is the sum over the triples
  have hsum : distinctSum D Bc θ =
      ∑ y : ResVec (smallPrimes 𝒢), ∑ sk : Skel D, ∑ d : Deco 𝒢 J ℓ Bc D.n,
        (if Graph.PerformedBirthsDistinct (sk.hist y d).birth then (sk.hist y d).weight θ
          else 0) := by
    unfold distinctSum
    refine Eq.trans (Finset.sum_congr rfl fun h _ => ?_)
      (sum_equiv_triple (histSkelEquiv D Bc)
        (fun (y : ResVec (smallPrimes 𝒢)) (sk : Skel D) (d : Deco 𝒢 J ℓ Bc D.n) =>
          if Graph.PerformedBirthsDistinct (sk.hist y d).birth then (sk.hist y d).weight θ
          else 0))
    exact (congrArg
      (fun h' : History D Bc =>
        if Graph.PerformedBirthsDistinct h'.birth then h'.weight θ else 0)
      ((histSkelEquiv D Bc).left_inv h)).symm
  -- the sum over the decorations of a skeleton
  have hd : ∀ (y : ResVec (smallPrimes 𝒢)) (sk : Skel D),
      (∑ d : Deco 𝒢 J ℓ Bc D.n,
        (if Graph.PerformedBirthsDistinct (sk.hist y d).birth then (sk.hist y d).weight θ
          else 0)) =
        ((haarMass (smallPrimes 𝒢) : ℝ) : ℂ) * (sk.common θ y * ((sk.memSum Bc : ℝ) : ℂ)) := by
    intro y sk
    rw [Finset.sum_congr rfl fun d _ => hw y sk d, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold Skel.memSum
    rw [Complex.ofReal_sum]
  have hsum2 : (∑ y : ResVec (smallPrimes 𝒢), ∑ sk : Skel D, ∑ d : Deco 𝒢 J ℓ Bc D.n,
        (if Graph.PerformedBirthsDistinct (sk.hist y d).birth then (sk.hist y d).weight θ
          else 0)) =
      ((haarMass (smallPrimes 𝒢) : ℝ) : ℂ) *
        ∑ y : ResVec (smallPrimes 𝒢), ∑ sk : Skel D,
          sk.common θ y * ((sk.memSum Bc : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun sk _ => hd y sk
  rw [hsum, hsum2]
  unfold haarMass
  rw [Complex.ofReal_inv]

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
