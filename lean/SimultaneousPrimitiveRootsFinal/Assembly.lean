import SimultaneousPrimitiveRootsFinal.CFTArtin
import ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocity
import SimultaneousPrimitiveRoots.Unconditional.KummerTower
import SimultaneousPrimitiveRoots.Unconditional.HeckeAscent
import SimultaneousPrimitiveRoots.Unconditional.CyclotomicDescent
import SimultaneousPrimitiveRoots.Unconditional.KummerZeroFree
import SimultaneousPrimitiveRoots.Unconditional.TwoEvaluations

/-!
# From [A]'s Hecke zero-free strip to the Kummer zero-free input (steps Z3 and Z5)

* `exists_rayArtinData`: every finite abelian extension `L/K` of number fields has an Artin map
  through a TauCeti ray class group with proper finite part (ClassFieldTheory's
  `finiteAbelianGlobalReciprocity` and the bridge `CFTBridge.rayArtinDataOfReciprocity`).
* `allKummerZetaZeroFree_of_heckeZeroFreeStrip`: for `δ ≤ 1`, `HeckeZeroFreeStrip δ` ([A],
  Theorem 1.2) gives `AllKummerZetaZeroFree δ` ([A], Lemma `spl:field-bounds`). For `a ≥ 2` and a
  prime `q > a`, with `M = lcm(12, q)`, `F = ℚ(ζ_M)`, `K_q = ℚ(ζ_q, a^{1/q})` and
  `K̃ = ℚ(ζ_M, a^{1/q}) = K_q(ζ_M)`:
  - `K̃ / F` is abelian (Kummer), so `(s - 1) ζ_{K̃}` has no zeros in `{Re s > 1 - δ} \ {1}`
    (`dedekindZetaEntire_ne_zero_of_hecke`, the Artin map from class field theory);
  - `K̃ / K_q` is the `M`-th cyclotomic extension, so the zeros descend
    (`dedekindZetaEntire_ne_zero_of_cyclotomic'`).
* `mainClaim_of_longPrimeStatistic_and_heckeZeroFreeStrip`: `MainClaim` from the public paper's
  `prop:ap` (`FixedClassLongPrimeStatistic`) and [A]'s Theorem 1.2 (`HeckeZeroFreeStrip`).
* `mainClaim_of_longPrimeStatistic_and_heckeTwoEvaluations`: the same with [A]'s Theorem 1.2
  replaced by its two evaluations of the common signal (`HeckeTwoEvaluations`, [A] §§3–6), through
  the Mellin-signal steps of `MellinSignal.lean`, `GaussianSignal.lean` and `TwoEvaluations.lean`.

Both remaining inputs are hypotheses, not axioms. This file is not a `module`: it imports
ClassFieldTheory.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional

open NumberField TauCeti TauCeti.GlobalNumberFields

/-- **Class field theory, in the form used by the descent and ascent.** Every finite abelian
extension `L/K` of number fields has an Artin map through the ray class group of a TauCeti modulus
with proper finite part. -/
theorem exists_rayArtinData (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    ∃ 𝔪 : Modulus K, 𝔪.finitePart ≠ ⊤ ∧ Nonempty (RayArtinData K L 𝔪) := by
  obtain ⟨D⟩ := ClassFieldTheory.finiteAbelianGlobalReciprocity K L
  exact ⟨_, CFTBridge.domModulus_finitePart_ne_top _,
    ⟨CFTBridge.rayArtinDataOfReciprocity D⟩⟩

/-- **[A, Theorem 1.2] gives [A, Lemma `spl:field-bounds`]**: the Hecke zero-free strip of width
`δ ≤ 1` over the cyclotomic fields `F ⊇ μ₁₂` makes `(s - 1) ζ_{K_q}` zero-free on `Re s > 1 - δ`
for every `a ≥ 2` and every prime `q > a`. -/
theorem allKummerZetaZeroFree_of_heckeZeroFreeStrip {δ : ℝ} (hδ : δ ≤ 1)
    (hA : HeckeZeroFreeStrip δ) : AllKummerZetaZeroFree δ := by
  intro a q ha hq haq
  let : Fact (2 ≤ a) := ⟨ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  -- ascent: `K̃ / ℚ(ζ_M)` is abelian
  obtain ⟨𝔪, hnt, ⟨D⟩⟩ :=
    exists_rayArtinData (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q)
  have hL := dedekindZetaEntire_ne_zero_of_hecke hδ hA (twelve_dvd_kummerLevel q) D hnt
  -- descent: `K̃ = K_q(ζ_M)`
  exact dedekindZetaEntire_ne_zero_of_cyclotomic' (K := PrimeKummerField a q)
    (L := KummerTop a q) (m := kummerLevel q) (by have := two_lt_kummerLevel q; omega) hδ hL

/-- **`MainClaim` from the public paper's `prop:ap` and [A]'s Theorem 1.2.** -/
theorem mainClaim_of_longPrimeStatistic_and_heckeZeroFreeStrip {δ η β : ℝ}
    (hη : 0 < η) (hηδ : η < δ) (hηfifth : η < 1 / 5) (hδ : δ ≤ 1)
    (hβ : 1 - η < β) (hβ1 : β < 1)
    (hstat : FixedClassLongPrimeStatistic (1 - η) β)
    (hA : HeckeZeroFreeStrip δ) : MainClaim :=
  mainClaim_of_longPrimeStatistic_and_kummerZetaZeroFree hη hηδ hηfifth hδ hβ hβ1 hstat
    (allKummerZetaZeroFree_of_heckeZeroFreeStrip hδ hA)

/-- The paper's parameters: `δ = 10⁻⁶`, `η = δ / 2`, `α = 1 - η`, `β = 1 - η / 2`. -/
theorem mainClaim_of_paperParameters_and_heckeZeroFreeStrip
    (hstat : FixedClassLongPrimeStatistic (1 - (10 : ℝ)⁻¹ ^ 6 / 2)
      (1 - (10 : ℝ)⁻¹ ^ 6 / 4))
    (hA : HeckeZeroFreeStrip ((10 : ℝ)⁻¹ ^ 6)) : MainClaim :=
  mainClaim_of_longPrimeStatistic_and_heckeZeroFreeStrip (δ := (10 : ℝ)⁻¹ ^ 6)
    (η := (10 : ℝ)⁻¹ ^ 6 / 2) (β := 1 - (10 : ℝ)⁻¹ ^ 6 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hstat hA

/-- **`MainClaim` from the public paper's `prop:ap` and [A]'s two evaluations** (the paper's
parameters, `δ = 10⁻⁶ ≤ 1/20000`). -/
theorem mainClaim_of_longPrimeStatistic_and_heckeTwoEvaluations
    (hstat : FixedClassLongPrimeStatistic (1 - (10 : ℝ)⁻¹ ^ 6 / 2)
      (1 - (10 : ℝ)⁻¹ ^ 6 / 4))
    (hA : HeckeTwoEvaluations) : MainClaim :=
  mainClaim_of_paperParameters_and_heckeZeroFreeStrip hstat
    (heckeZeroFreeStrip_of_heckeTwoEvaluations (by norm_num) (by norm_num) hA)

end SimultaneousPrimitiveRoots.Unconditional

end
