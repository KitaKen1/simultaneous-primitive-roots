module

public import SimultaneousPrimitiveRoots.Unconditional.HeckeStatement

/-!
# The Kummer zero-free input, field by field

[A, Lemma `spl:field-bounds`] concludes, from [A, Theorem 1.2], that
`ζ_{K_q}(s) ≠ 0` for `Re s > 1 - 10⁻⁶`, `s ≠ 1`, for every prime `q` large in terms of `a`
(`q ≠ ℓ` and `q > v_ℓ(a)` for one prime `ℓ ∣ a`; `q > a` suffices). Its proof is classical:
the abelian factorizations of `ζ_{K̃}`, `K̃ = K_q(ζ₁₂)`, over `ℚ(ζ_{12q})` and over `K_q`.

`KummerZetaZeroFree a q δ` is that conclusion for the entire function `(s - 1) ζ_K(s)`.
`uniformKummerZetaGap_of_kummerZetaZeroFree` turns it, for all primes `q > a`, into the uniform
zero gap of the Lean reduction with no exceptional set, and
`mainClaim_of_longPrimeStatistic_and_kummerZetaZeroFree` assembles the unconditional route
from the two field-level inputs:

* `FixedClassLongPrimeStatistic (1 - η) β` (the public paper's `prop:ap`);
* `KummerZetaZeroFree a q δ` for all `a ≥ 2` and primes `q > a` ([A]'s `spl:field-bounds`).

Both are hypotheses, not axioms.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Unconditional

open Filter

noncomputable section

/-- `(s - 1) ζ_K(s)` has no zero in `Re s > 1 - δ`, for `K = ℚ(ζ_q, a^{1/q})`
(the conclusion of [A, Lemma `spl:field-bounds`]). -/
def KummerZetaZeroFree (a q : ℕ) [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (δ : ℝ) : Prop :=
  ∀ s : ℂ, 1 - δ < s.re → Hecke.dedekindZetaEntire (PrimeKummerField a q) s ≠ 0

/-- `KummerZetaZeroFree a q δ` for every base `a ≥ 2` and every prime `q > a`. -/
def AllKummerZetaZeroFree (δ : ℝ) : Prop :=
  ∀ a q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q,
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    KummerZetaZeroFree a q δ

/-- **Zero-freeness field by field gives the uniform gap**, with no exceptional set and no
height restriction. -/
theorem uniformKummerZetaGap_of_kummerZetaZeroFree {δ : ℝ} (h : AllKummerZetaZeroFree δ)
    (A : Finset ℕ) (η : ℝ) : Explicit.UniformKummerZetaGap A δ η ∅ := by
  filter_upwards with x
  intro a _ q ha hq haq _ _ i _ _
  by_contra hlt
  push Not at hlt
  exact h a q ha hq haq _ hlt (fullQuotientIndexedZero_is_zero _ i)

/-- The empty exceptional set has summable reciprocal weight. -/
theorem summable_badReciprocalWeight_empty : Summable (badReciprocalWeight ∅) := by
  have : badReciprocalWeight ∅ = fun _ => 0 := by
    funext q
    simp [badReciprocalWeight]
  rw [this]
  exact summable_zero

/-- **`MainClaim` from the two field-level inputs.** -/
theorem mainClaim_of_longPrimeStatistic_and_kummerZetaZeroFree {δ η β : ℝ}
    (hη : 0 < η) (hηδ : η < δ) (hηfifth : η < 1 / 5) (hδ : δ ≤ 1)
    (hβ : 1 - η < β) (hβ1 : β < 1)
    (hstat : FixedClassLongPrimeStatistic (1 - η) β)
    (hzero : AllKummerZetaZeroFree δ) : MainClaim :=
  mainClaim_of_longPrimeStatistic_and_zetaGap hη hηδ hηfifth hδ hβ hβ1 hstat
    fun A _ => ⟨∅, summable_badReciprocalWeight_empty,
      uniformKummerZetaGap_of_kummerZetaZeroFree hzero A η⟩

end

end SimultaneousPrimitiveRoots.Unconditional
