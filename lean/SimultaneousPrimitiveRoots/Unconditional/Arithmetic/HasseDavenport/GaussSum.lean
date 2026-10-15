module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.Norm.Transitivity
public import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.HasseDavenport.Lift
public import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.HasseDavenport.MonicPolynomials

/-!
# The Hasse--Davenport lifting relation for Gauss sums

Let `K / k` be an extension of finite fields of degree `n`, let `χ` be a nontrivial multiplicative
character and `ψ` an additive character of `k`, with values in a commutative domain `R`. Then

`-g(χ ∘ N_{K/k}, ψ ∘ Tr_{K/k}) = (-g(χ, ψ)) ^ n`

(`hasseDavenport_gaussSum`; `hasseDavenport_gaussSum'` is the same statement in the form
`g(χ ∘ N, ψ ∘ Tr) = (-1) ^ (n - 1) * g(χ, ψ) ^ n`). No hypothesis on `ψ` is needed. The relation
also holds for the trivial multiplicative character (with the convention `χ(0) = 0`) when `ψ` is
nontrivial (`hasseDavenport_gaussSum_of_addChar_ne_one`); it fails in general when both
characters are trivial.

## The proof

We follow Ireland--Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 11, §4.
For a monic polynomial `f = X ^ d - c₁ X ^ (d - 1) + ⋯ + (-1) ^ d c_d` over `k` put
`λ(f) = ψ(c₁) χ(c_d)` (`hasseDavenportWeight`). Then:

* `λ` is multiplicative on monic polynomials (`hasseDavenportWeight_mul`) and `λ(1) = 1`;
* the sum of `λ` over the monic polynomials of degree `1` is the Gauss sum `g(χ, ψ)`
  (`monicSum_hasseDavenportWeight_one`);
* the sum of `λ` over the monic polynomials of degree `d ≥ 2` vanishes, because the constant
  coefficient varies independently of the second coefficient and `χ` is nontrivial
  (`monicSum_hasseDavenportWeight_eq_zero`).

Hence the generating series of `λ` is `1 + g(χ, ψ) T`, and the Newton recursion of
`MonicPolynomials.lean` gives `-N_s = (-g(χ, ψ)) ^ s` for the weighted prime power sums
`N_s = ∑_{deg P ∣ s} deg P • λ(P) ^ (s / deg P)` (`neg_primePowerSum_eq_pow`).

On the other hand, for `α ∈ K` with minimal polynomial `P` over `k` of degree `d`, the trace and
norm of `α` are read off from the characteristic polynomial `P ^ (n / d)`, which gives
`χ(N α) ψ(Tr α) = λ(P) ^ (n / d)` (`hasseDavenportWeight_minpoly_pow`); and every monic
irreducible `P` of degree `d ∣ n` is the minimal polynomial of exactly `d` elements of `K`
(`card_filter_minpoly_eq`). Grouping the elements of `K` by their minimal polynomials therefore
identifies the lifted Gauss sum with `N_n` (`gaussSum_normLift_traceLift`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

open Polynomial Finset IntermediateField

/-! ### The Hasse--Davenport weight of a monic polynomial -/

section Weight

variable {k : Type*} [Field k] {R : Type*} [CommRing R]

/-- The weight `λ(f) = ψ(c₁) χ(c_d)` of a monic polynomial
`f = X ^ d - c₁ X ^ (d - 1) + ⋯ + (-1) ^ d c_d`, where `c₁ = -f.nextCoeff` is the sum and
`c_d = (-1) ^ d * f.coeff 0` is the product of the roots of `f`. -/
noncomputable def hasseDavenportWeight (χ : MulChar k R) (ψ : AddChar k R) (f : k[X]) : R :=
  ψ (-f.nextCoeff) * χ ((-1) ^ f.natDegree * f.coeff 0)

theorem hasseDavenportWeight_one (χ : MulChar k R) (ψ : AddChar k R) :
    hasseDavenportWeight χ ψ 1 = 1 := by
  simp [hasseDavenportWeight, nextCoeff]

/-- The weight is multiplicative on monic polynomials. -/
theorem hasseDavenportWeight_mul (χ : MulChar k R) (ψ : AddChar k R) {f g : k[X]}
    (hf : f.Monic) (hg : g.Monic) :
    hasseDavenportWeight χ ψ (f * g) =
      hasseDavenportWeight χ ψ f * hasseDavenportWeight χ ψ g := by
  have h : (-1 : k) ^ (f.natDegree + g.natDegree) * (f.coeff 0 * g.coeff 0) =
      ((-1) ^ f.natDegree * f.coeff 0) * ((-1) ^ g.natDegree * g.coeff 0) := by ring
  simp only [hasseDavenportWeight]
  rw [hf.nextCoeff_mul hg, hf.natDegree_mul hg, mul_coeff_zero, neg_add, AddChar.map_add_eq_mul,
    h, map_mul]
  ring

/-- The weight of `X - a` is `χ(a) ψ(a)`. -/
theorem hasseDavenportWeight_X_sub_C (χ : MulChar k R) (ψ : AddChar k R) (a : k) :
    hasseDavenportWeight χ ψ (X - C a) = χ a * ψ a := by
  rw [hasseDavenportWeight, nextCoeff_X_sub_C, natDegree_X_sub_C, neg_neg, pow_one, coeff_sub,
    coeff_X_zero, coeff_C_zero, zero_sub, neg_one_mul, neg_neg, mul_comm]

/-- The sum of the weights of the monic polynomials of degree `1` is the Gauss sum. -/
theorem monicSum_hasseDavenportWeight_one [Fintype k] (χ : MulChar k R) (ψ : AddChar k R) :
    monicSum (hasseDavenportWeight χ ψ) 1 = gaussSum χ ψ := by
  rw [monicSum, sum_monicsOfDegree_one, gaussSum]
  exact Finset.sum_congr rfl fun a _ => hasseDavenportWeight_X_sub_C χ ψ a

/-- Adding a constant to a polynomial of degree at least `2` does not change its second
coefficient. -/
theorem nextCoeff_add_C_of_two_le_natDegree {f : k[X]} (hf : 2 ≤ f.natDegree) (a : k) :
    (f + C a).nextCoeff = f.nextCoeff := by
  rw [nextCoeff_of_natDegree_pos (by rw [natDegree_add_C]; omega),
    nextCoeff_of_natDegree_pos (by omega), natDegree_add_C, coeff_add,
    coeff_C_of_ne_zero (by omega), add_zero]

variable [Finite k] [IsDomain R]

/-- For a nontrivial multiplicative character `χ`, the sum of the weights of the monic
polynomials of degree `d ≥ 2` vanishes: rescaling the constant coefficient by a unit `u` with
`χ u ≠ 1` permutes these polynomials and multiplies the weights by `χ u`. -/
theorem monicSum_hasseDavenportWeight_eq_zero {χ : MulChar k R} (hχ : χ ≠ 1) (ψ : AddChar k R)
    {d : ℕ} (hd : 2 ≤ d) : monicSum (hasseDavenportWeight χ ψ) d = 0 := by
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hχ
  refine eq_zero_of_mul_eq_self_left hu ?_
  have hmem : ∀ (c : k) (f : k[X]), f ∈ monicsOfDegree k d → f + C c ∈ monicsOfDegree k d := by
    intro c f hf
    rw [mem_monicsOfDegree] at hf ⊢
    obtain ⟨hfm, hfd⟩ := hf
    refine ⟨hfm.add_of_left (degree_C_le.trans_lt ?_), by rw [natDegree_add_C, hfd]⟩
    exact natDegree_pos_iff_degree_pos.mp (by omega)
  have hinv : ∀ v w : k, w * v = 1 → ∀ f : k[X],
      (f + C ((v - 1) * f.coeff 0)) +
        C ((w - 1) * (f + C ((v - 1) * f.coeff 0)).coeff 0) = f := by
    intro v w hvw f
    have h0 : (v - 1) * f.coeff 0 + (w - 1) * (f.coeff 0 + (v - 1) * f.coeff 0) = 0 := by
      linear_combination f.coeff 0 * hvw
    rw [coeff_add, coeff_C_zero, add_assoc, ← C_add, h0, C_0, add_zero]
  rw [monicSum, Finset.mul_sum]
  refine Finset.sum_nbij' (fun f => f + C (((u : k) - 1) * f.coeff 0))
    (fun f => f + C ((((u⁻¹ : kˣ) : k) - 1) * f.coeff 0)) ?_ ?_ ?_ ?_ ?_
  · exact fun f hf => hmem _ f hf
  · exact fun f hf => hmem _ f hf
  · exact fun f _ => hinv _ _ (Units.inv_mul u) f
  · exact fun f _ => hinv _ _ (Units.mul_inv u) f
  · intro f hf
    rw [mem_monicsOfDegree] at hf
    obtain ⟨-, hfd⟩ := hf
    have h : (-1 : k) ^ f.natDegree * (f.coeff 0 + ((u : k) - 1) * f.coeff 0) =
        (u : k) * ((-1) ^ f.natDegree * f.coeff 0) := by ring
    simp only [hasseDavenportWeight]
    rw [nextCoeff_add_C_of_two_le_natDegree (f := f) (by omega), natDegree_add_C, coeff_add,
      coeff_C_zero, h, map_mul χ (u : k)]
    ring

end Weight

/-! ### Elements of the extension field and their minimal polynomials -/

section Extension

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K] {R : Type*} [CommRing R]

/-- For an element `α` of a finite extension `K / k` with minimal polynomial `P`, the
characteristic polynomial of `α` is `P ^ ([K : k] / deg P)`; reading off the trace and the norm
gives `λ(P) ^ ([K : k] / deg P) = χ(N α) ψ(Tr α)`. -/
theorem hasseDavenportWeight_minpoly_pow [FiniteDimensional k K] (χ : MulChar k R)
    (ψ : AddChar k R) (α : K) :
    hasseDavenportWeight χ ψ (minpoly k α) ^ (Module.finrank k K / (minpoly k α).natDegree) =
      χ (Algebra.norm k α) * ψ (Algebra.trace k K α) := by
  have hα : IsIntegral k α := .of_finite k α
  have hd : 0 < (minpoly k α).natDegree := minpoly.natDegree_pos hα
  have hde : (minpoly k α).natDegree * Module.finrank k⟮α⟯ K = Module.finrank k K := by
    rw [← IntermediateField.adjoin.finrank hα]
    exact Module.finrank_mul_finrank k k⟮α⟯ K
  have hdiv : Module.finrank k K / (minpoly k α).natDegree = Module.finrank k⟮α⟯ K := by
    rw [← hde]
    exact Nat.mul_div_cancel_left _ hd
  have htr : Algebra.trace k K α = Module.finrank k⟮α⟯ K • (-(minpoly k α).nextCoeff) := by
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, nsmul_eq_mul]
  have hnorm : Algebra.norm k α =
      ((-1) ^ (minpoly k α).natDegree * (minpoly k α).coeff 0) ^ Module.finrank k⟮α⟯ K := by
    rw [Algebra.norm_eq_norm_adjoin k α]
    congr 1
    simpa [IntermediateField.minpoly_gen] using
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hα)
  rw [hdiv, hasseDavenportWeight, mul_pow, ← AddChar.map_nsmul_eq_pow, ← map_pow, ← htr, ← hnorm,
    mul_comm]

variable [Finite k]

/-- A monic irreducible polynomial over a finite field `k` whose degree `d` divides the degree of
a finite extension `K / k` is the minimal polynomial of exactly `d` elements of `K`. -/
theorem card_filter_minpoly_eq [Fintype K] [DecidableEq k[X]] {P : k[X]}
    (hP : P ∈ irreducibleMonicsDvd k (Module.finrank k K)) :
    (Finset.univ.filter fun α : K => minpoly k α = P).card = P.natDegree := by
  classical
  rw [mem_irreducibleMonicsDvd] at hP
  obtain ⟨hm, hi, hd⟩ := hP
  have hdvd : P.natDegree ∣ Module.finrank k K := (Nat.mem_divisors.mp hd).1
  have h1 : P ∣ X ^ Nat.card k ^ Module.finrank k K - X :=
    hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hdvd
  have hsplit : (P.map (algebraMap k K)).Splits := by
    have h2 : P.map (algebraMap k K) ∣ (X ^ Nat.card K - X : K[X]) := by
      have h3 := Polynomial.map_dvd (algebraMap k K) h1
      rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        ← Module.natCard_eq_pow_finrank] at h3
    exact (splits_X_pow_nat_card_sub_X (K := K)).of_dvd
      (FiniteField.X_pow_card_sub_X_ne_zero K Finite.one_lt_card) h2
  have hsep : P.Separable := PerfectField.separable_of_irreducible hi
  have hroots : (Finset.univ.filter fun α : K => minpoly k α = P) = (P.aroots K).toFinset := by
    ext α
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_aroots, eq_comm,
      minpoly.eq_iff_aeval_eq_zero hi hm]
    simp [hm.ne_zero]
  rw [hroots, Multiset.toFinset_card_of_nodup (nodup_roots hsep.map),
    ← hsplit.natDegree_eq_card_roots, natDegree_map]

/-- The Gauss sum of the lifted characters is the weighted prime power sum of the
Hasse--Davenport weight, in degree `[K : k]`: group the elements of `K` by their minimal
polynomials. -/
theorem gaussSum_normLift_traceLift [Fintype K] (χ : MulChar k R) (ψ : AddChar k R) :
    gaussSum (normLift K χ) (traceLift K ψ) =
      primePowerSum (hasseDavenportWeight χ ψ) (Module.finrank k K) := by
  classical
  have hmaps : ∀ α ∈ (Finset.univ : Finset K),
      minpoly k α ∈ irreducibleMonicsDvd k (Module.finrank k K) := by
    intro α _
    have hα : IsIntegral k α := .of_finite k α
    rw [mem_irreducibleMonicsDvd, Nat.mem_divisors]
    exact ⟨minpoly.monic hα, minpoly.irreducible hα, minpoly.degree_dvd hα,
      Module.finrank_pos.ne'⟩
  rw [gaussSum, primePowerSum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hconst : ∀ α ∈ Finset.univ.filter (fun α : K => minpoly k α = P),
      normLift K χ α * traceLift K ψ α =
        hasseDavenportWeight χ ψ P ^ (Module.finrank k K / P.natDegree) := by
    intro α hα
    rw [Finset.mem_filter] at hα
    rw [normLift_apply, traceLift_apply, ← hasseDavenportWeight_minpoly_pow, hα.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_filter_minpoly_eq hP]

end Extension

/-! ### The Hasse--Davenport relation -/

section HasseDavenport

variable {k : Type*} [Field k] [Fintype k] (K : Type*) [Field K] [Fintype K] [Algebra k K]
  {R : Type*} [CommRing R] [IsDomain R]

/-- **The Hasse--Davenport lifting relation for Gauss sums.** Let `K / k` be an extension of
finite fields of degree `n`, `χ` a nontrivial multiplicative character and `ψ` an additive
character of `k`. Then the Gauss sum of the lifted characters `χ ∘ N_{K/k}` and `ψ ∘ Tr_{K/k}`
satisfies `-g(χ ∘ N, ψ ∘ Tr) = (-g(χ, ψ)) ^ n`. -/
theorem hasseDavenport_gaussSum {χ : MulChar k R} (hχ : χ ≠ 1) (ψ : AddChar k R) :
    -gaussSum (normLift K χ) (traceLift K ψ) = (-gaussSum χ ψ) ^ Module.finrank k K := by
  rw [gaussSum_normLift_traceLift, ← monicSum_hasseDavenportWeight_one]
  exact neg_primePowerSum_eq_pow _ (fun f g hf hg => hasseDavenportWeight_mul χ ψ hf hg)
    (hasseDavenportWeight_one χ ψ) (fun d hd => monicSum_hasseDavenportWeight_eq_zero hχ ψ hd)
    Module.finrank_pos.ne'

/-- The Hasse--Davenport lifting relation for Gauss sums with the sign made explicit:
`g(χ ∘ N, ψ ∘ Tr) = (-1) ^ (n - 1) * g(χ, ψ) ^ n`. -/
theorem hasseDavenport_gaussSum' {χ : MulChar k R} (hχ : χ ≠ 1) (ψ : AddChar k R) :
    gaussSum (normLift K χ) (traceLift K ψ) =
      (-1) ^ (Module.finrank k K - 1) * gaussSum χ ψ ^ Module.finrank k K := by
  have h := hasseDavenport_gaussSum K hχ ψ
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := k) (M := K)).ne'
  rw [hm, Nat.succ_eq_add_one] at h ⊢
  rw [neg_pow, pow_succ (-1 : R) m] at h
  rw [Nat.add_sub_cancel]
  linear_combination -h

/-- The Hasse--Davenport lifting relation for an arbitrary multiplicative character `χ` (possibly
trivial) and a nontrivial additive character `ψ`. For trivial `χ` both Gauss sums are `-1`. -/
theorem hasseDavenport_gaussSum_of_addChar_ne_one (χ : MulChar k R) {ψ : AddChar k R}
    (hψ : ψ ≠ 1) :
    -gaussSum (normLift K χ) (traceLift K ψ) = (-gaussSum χ ψ) ^ Module.finrank k K := by
  rcases eq_or_ne χ 1 with rfl | hχ
  · rw [normLift_one, gaussSum_one_left (traceLift_ne_one K hψ), gaussSum_one_left hψ, neg_neg,
      one_pow]
  · exact hasseDavenport_gaussSum K hχ ψ

end HasseDavenport

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
