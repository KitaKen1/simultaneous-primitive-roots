module

public import SimultaneousPrimitiveRoots.Unconditional.SupplyBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerZetaGap

/-!
# Assembly of the unconditional route

`mainClaim_of_longPrimeStatistic_and_zetaGap`: the fixed-class long-prime statistic of the public
paper (`prop:ap`, `FixedClassLongPrimeStatistic (1 - η) β`) and a zero gap of width `δ > η` for the
Dedekind zeta functions of the Kummer fields (`UniformKummerZetaGap`) give `MainClaim`.

Both inputs are hypotheses; nothing is assumed as an axiom. The paper's parameters are
`δ = 10⁻⁶` (the width of `thm:hecke-zero-free` of [A]), `α = 1 - η`, `β = 1 - η / 2` with
`0 < η < δ`; any such choice is admissible here (`η < 1/5`).

The remaining work is to prove the two inputs:
* the zero gap from [A]'s Hecke zero-free strip, through Hecke continuation for ray class
  characters, Kummer reciprocity over `ℚ(ζ_{12q})`, and the abelian factorizations of
  `ζ_{K̃}` (`K̃ = ℚ(ζ_{12q}, a^{1/q})`);
* `prop:ap` from the marked correlation inputs (M1)–(M3) of [P], [S] and [A, §8].
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Unconditional

noncomputable section

/-- **`MainClaim` from the fixed-class long-prime statistic and a Kummer zero gap.** -/
theorem mainClaim_of_longPrimeStatistic_and_zetaGap {δ η β : ℝ}
    (hη : 0 < η) (hηδ : η < δ) (hηfifth : η < 1 / 5) (hδ : δ ≤ 1)
    (hβ : 1 - η < β) (hβ1 : β < 1)
    (hstat : FixedClassLongPrimeStatistic (1 - η) β)
    (hgap : ∀ A : Finset ℕ, Admissible A → ∃ B : Set ℕ,
      Summable (badReciprocalWeight B) ∧ Explicit.UniformKummerZetaGap A δ η B) :
    MainClaim := by
  obtain ⟨θ, hθ, hsup⟩ :=
    candidateSupplyBound_of_fixedClassLongPrimeStatistic (by linarith) hβ hβ1 hstat
  exact Explicit.mainClaim_of_supply_and_zetaGap hη.le hηδ hηfifth hδ
    (fun A _ => ⟨θ, hθ, hsup A⟩) hgap

/-- The paper's parameters: `δ = 10⁻⁶`, `η = δ / 2`, `α = 1 - η`, `β = 1 - η / 2`. -/
theorem mainClaim_of_paperParameters
    (hstat : FixedClassLongPrimeStatistic (1 - (10 : ℝ)⁻¹ ^ 6 / 2)
      (1 - (10 : ℝ)⁻¹ ^ 6 / 4))
    (hgap : ∀ A : Finset ℕ, Admissible A → ∃ B : Set ℕ,
      Summable (badReciprocalWeight B) ∧
        Explicit.UniformKummerZetaGap A ((10 : ℝ)⁻¹ ^ 6) ((10 : ℝ)⁻¹ ^ 6 / 2) B) :
    MainClaim := by
  refine mainClaim_of_longPrimeStatistic_and_zetaGap (δ := (10 : ℝ)⁻¹ ^ 6)
    (η := (10 : ℝ)⁻¹ ^ 6 / 2) (β := 1 - (10 : ℝ)⁻¹ ^ 6 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?_ hgap
  have h : (1 : ℝ) - (10 : ℝ)⁻¹ ^ 6 / 2 = 1 - (10 : ℝ)⁻¹ ^ 6 / 2 := rfl
  exact hstat

end

end SimultaneousPrimitiveRoots.Unconditional
