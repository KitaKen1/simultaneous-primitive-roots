module

public import SimultaneousPrimitiveRoots.Unconditional.KummerTower
public import SimultaneousPrimitiveRoots.Unconditional.CyclotomicDescent
public import SimultaneousPrimitiveRoots.Unconditional.KummerZeroFree
public import SimultaneousPrimitiveRoots.Unconditional.MeromorphicTransfer

/-!
# The Kummer zero-free input from a zero-free factorization of `ζ_L`

`CyclotomicAbelianZetaFactorization δ` is the part of [A] that the unconditional route needs on
the Hecke side, stated with Mathlib notions only: for every `n` with `12 ∣ n` and every finite
abelian extension `L` of `ℚ(ζ_n)`, the Dedekind zeta function of `L` is, on `Re s > 1`, a product

`ζ_L(s) = E(s) * ∏ i ∈ X, Λ i s`

in which `E` is analytic and nonvanishing on `Re s > 0` (the finite Euler correction at the
primes dividing the modulus) and every `Λ i` is meromorphic on `Re s > 1 - δ` with meromorphic
order `≤ 0` at each point (a continued Hecke `L`-function with no zeros; a pole is allowed).

Classically this is the Artin factorization of `ζ_L` over the characters of `Gal(L / ℚ(ζ_n))`
(class field theory) together with [A, Theorem 1.2] for each Hecke `L`-function. The statement
does not mention ray class groups, moduli or Hecke characters, so any formalization of
[A, Theorem 1.2], in whatever language it states Hecke `L`-functions, can supply it without an
identification of ray class groups.

From it:

* `dedekindZetaEntire_ne_zero_of_factorization`: `(s - 1) ζ_L(s)` has no zeros in
  `{Re s > 1 - δ} \ {1}` (`ne_zero_of_meromorphic_factorization`);
* `allKummerZetaZeroFree_of_factorization`: `AllKummerZetaZeroFree δ`, by the cyclotomic descent
  from `K̃ = K_q(ζ_M)` to `K_q` (`dedekindZetaEntire_ne_zero_of_cyclotomic'`);
* `mainClaim_of_longPrimeStatistic_and_factorization`: `MainClaim` from the public paper's
  `prop:ap` and this factorization.

`CyclotomicAbelianZetaFactorization` is a hypothesis of these theorems, not an axiom.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Unconditional

open NumberField

noncomputable section

/-- **Zero-free factorization of `ζ_L` for abelian `L` over the cyclotomic fields `F ⊇ μ₁₂`.**
For every `n` with `12 ∣ n` and every abelian extension `L / ℚ(ζ_n)` of number fields there are
finitely many functions `Λ i`, meromorphic of order `≤ 0` on `Re s > 1 - δ`, and a function `E`,
analytic and nonvanishing on `Re s > 0`, with `ζ_L(s) = E(s) * ∏ i ∈ X, Λ i s` for `Re s > 1`. -/
def CyclotomicAbelianZetaFactorization (δ : ℝ) : Prop :=
  ∀ (n : ℕ) [NeZero n], 12 ∣ n →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra (CyclotomicField n ℚ) L]
      [IsAbelianGalois (CyclotomicField n ℚ) L],
      ∃ (ι : Type) (X : Finset ι) (E : ℂ → ℂ) (Λ : ι → ℂ → ℂ),
        (∀ s : ℂ, 0 < s.re → AnalyticAt ℂ E s) ∧ (∀ s : ℂ, 0 < s.re → E s ≠ 0) ∧
        (∀ i ∈ X, MeromorphicOn (Λ i) {s : ℂ | 1 - δ < s.re}) ∧
        (∀ i ∈ X, ∀ s : ℂ, 1 - δ < s.re → meromorphicOrderAt (Λ i) s ≤ 0) ∧
        ∀ s : ℂ, 1 < s.re → dedekindZeta L s = E s * ∏ i ∈ X, Λ i s

/-- The factorization makes `(s - 1) ζ_L(s)` zero-free on `{Re s > 1 - δ} \ {1}`. -/
theorem dedekindZetaEntire_ne_zero_of_factorization {δ : ℝ} (hδ : δ ≤ 1)
    (h : CyclotomicAbelianZetaFactorization δ) {n : ℕ} [NeZero n] (h12 : 12 ∣ n)
    (L : Type) [Field L] [NumberField L] [Algebra (CyclotomicField n ℚ) L]
    [IsAbelianGalois (CyclotomicField n ℚ) L] :
    ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 → Hecke.dedekindZetaEntire L s ≠ 0 := by
  obtain ⟨ι, X, E, Λ, hE, hEne, hΛ, hord, hfac⟩ := h n h12 L
  refine ne_zero_of_meromorphic_factorization X hδ (Hecke.differentiable_dedekindZetaEntire L)
    hE hEne hΛ hord fun s hs => ?_
  rw [Hecke.dedekindZetaEntire_eq_mul L hs, hfac s hs]

/-- **The factorization gives [A, Lemma `spl:field-bounds`]**: for `δ ≤ 1`, `(s - 1) ζ_{K_q}` is
zero-free on `Re s > 1 - δ` for every `a ≥ 2` and every prime `q > a`. -/
theorem allKummerZetaZeroFree_of_factorization {δ : ℝ} (hδ : δ ≤ 1)
    (h : CyclotomicAbelianZetaFactorization δ) : AllKummerZetaZeroFree δ := by
  intro a q ha hq haq
  let : Fact (2 ≤ a) := ⟨ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  -- ascent: `K̃ / ℚ(ζ_M)` is abelian
  have hL := dedekindZetaEntire_ne_zero_of_factorization hδ h (twelve_dvd_kummerLevel q)
    (KummerTop a q)
  -- descent: `K̃ = K_q(ζ_M)`
  exact dedekindZetaEntire_ne_zero_of_cyclotomic' (K := PrimeKummerField a q)
    (L := KummerTop a q) (m := kummerLevel q) (by have := two_lt_kummerLevel q; omega) hδ hL

/-- **`MainClaim` from the public paper's `prop:ap` and the zero-free factorization.** -/
theorem mainClaim_of_longPrimeStatistic_and_factorization {δ η β : ℝ}
    (hη : 0 < η) (hηδ : η < δ) (hηfifth : η < 1 / 5) (hδ : δ ≤ 1)
    (hβ : 1 - η < β) (hβ1 : β < 1)
    (hstat : FixedClassLongPrimeStatistic (1 - η) β)
    (h : CyclotomicAbelianZetaFactorization δ) : MainClaim :=
  mainClaim_of_longPrimeStatistic_and_kummerZetaZeroFree hη hηδ hηfifth hδ hβ hβ1 hstat
    (allKummerZetaZeroFree_of_factorization hδ h)

/-- The paper's parameters: `δ = 10⁻⁶`, `η = δ / 2`, `α = 1 - η`, `β = 1 - η / 2`. -/
theorem mainClaim_of_paperParameters_and_factorization
    (hstat : FixedClassLongPrimeStatistic (1 - (10 : ℝ)⁻¹ ^ 6 / 2)
      (1 - (10 : ℝ)⁻¹ ^ 6 / 4))
    (h : CyclotomicAbelianZetaFactorization ((10 : ℝ)⁻¹ ^ 6)) : MainClaim :=
  mainClaim_of_longPrimeStatistic_and_factorization (δ := (10 : ℝ)⁻¹ ^ 6)
    (η := (10 : ℝ)⁻¹ ^ 6 / 2) (β := 1 - (10 : ℝ)⁻¹ ^ 6 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hstat h

end

end SimultaneousPrimitiveRoots.Unconditional
