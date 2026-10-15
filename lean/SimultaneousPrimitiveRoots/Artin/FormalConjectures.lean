module

public import SimultaneousPrimitiveRoots.Artin.CumulativeDensity
public import TauCeti.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Formal Conjectures' `conditional_artin_primitive_roots.parts.i` for `a ≥ 2`

The definitions below are verbatim copies of those of Formal Conjectures
(`FormalConjecturesForMathlib/Data/Set/Density.lean` and
`FormalConjectures/.../ArtinPrimitiveRootsConjecture`), which is not a dependency of this
project:

* `partialDensity`, `HasDensity` (natural density relative to a set);
* `IsDedekindZeta`, `DedekindZetaRH`, `HooleyHypothesis` (RH for the Dedekind zeta functions of
  the splitting fields of `X^k - a`, `k` squarefree);
* `S a`, the primes with primitive root `a`.

`conditional_artin_primitive_roots_parts_i_of_two_le` proves the Formal Conjectures statement
`conditional_artin_primitive_roots.parts.i` (Hooley 1967, `research solved` with proof `sorry`
there) for every integer `a ≥ 2`. Only the fields with `k = q` prime, `q > a`, are used
(`kummerZetaGRH_of_hooleyHypothesis`). Negative `a` is not covered.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.FC

open Polynomial Filter NumberField
open scoped Topology

/-! ### Verbatim copies of the Formal Conjectures definitions -/

/-- Formal Conjectures' `Set.partialDensity`. -/
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Set.Iio b).ncard / (A ∩ Set.Iio b).ncard

/-- Formal Conjectures' `Set.HasDensity`. -/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => partialDensity S A b) atTop (𝓝 α)

/-- `Z` is a Dedekind zeta function of the number field `K`. -/
def IsDedekindZeta (K : Type*) [Field K] [NumberField K] (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re → Z s = NumberField.dedekindZeta K s

/-- The Riemann hypothesis for the Dedekind zeta function of `K`. -/
def DedekindZetaRH (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ Z : ℂ → ℂ, IsDedekindZeta K Z → ∀ s : ℂ, 0 < s.re → s.re < 1 → Z s = 0 → s.re = 1 / 2

/-- **Hooley's hypothesis** for `a`. -/
def HooleyHypothesis (a : ℤ) : Prop :=
  ∀ k : ℕ, Squarefree k →
    letI := NumberField.of_module_finite ℚ (X ^ k - C (a : ℚ)).SplittingField
    DedekindZetaRH (X ^ k - C (a : ℚ)).SplittingField

/-- The primes with primitive root `a`. -/
abbrev S (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ orderOf (a : ZMod p) = (p-1 : ℕ)}

/-! ### Isomorphism invariance of `ζ_K` -/

theorem dedekindZeta_eq_of_ringEquiv {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃+* K') :
    NumberField.dedekindZeta K = NumberField.dedekindZeta K' := by
  funext s
  unfold NumberField.dedekindZeta
  congr 1
  funext n
  congr 1
  set e' := RingOfIntegers.mapRingEquiv e
  apply Nat.card_congr
  refine
    { toFun := fun I => ⟨I.1.map e', by rw [Ideal.absNorm_map_of_ringEquiv]; exact I.2⟩
      invFun := fun J => ⟨J.1.map e'.symm, by rw [Ideal.absNorm_map_of_ringEquiv]; exact J.2⟩
      left_inv := fun I => Subtype.ext ?_
      right_inv := fun J => Subtype.ext ?_ }
  · show (I.1.map (e' : 𝓞 K →+* 𝓞 K')).map (e'.symm : 𝓞 K' →+* 𝓞 K) = I.1
    exact Ideal.map_of_equiv e'
  · show (J.1.map (e'.symm : 𝓞 K' →+* 𝓞 K)).map (e'.symm.symm : 𝓞 K →+* 𝓞 K') = J.1
    exact Ideal.map_of_equiv e'.symm

/-! ### `PrimeKummerField a q` is the splitting field of `X^q - a` -/

theorem isSplittingField_radical (a q : ℕ) [ha : Fact (2 ≤ a)] [hq : Fact q.Prime]
    [haq : Fact (a < q)] :
    IsSplittingField ℚ (PrimeKummerField a q) (X ^ q - C (a : ℚ)) := by
  set K := PrimeKummerField a q
  have hspl := (primeKummerField_absolute_splitting a q)
  have hprodne : kummerSplittingPolynomial a q ≠ 0 := by
    unfold kummerSplittingPolynomial
    exact mul_ne_zero (cyclotomic_ne_zero q ℚ) (X_pow_sub_C_ne_zero hq.out.pos _)
  have hdvd : (X ^ q - C (a : ℚ)) ∣ kummerSplittingPolynomial a q :=
    dvd_mul_left _ _
  have hsplits : ((X ^ q - C (a : ℚ)).map (algebraMap ℚ K)).Splits :=
    (IsSplittingField.splits K (kummerSplittingPolynomial a q)).of_dvd
      (Polynomial.map_ne_zero hprodne) (Polynomial.map_dvd _ hdvd)
  refine ⟨hsplits, ?_⟩
  -- the roots of `Φ_q` are ratios of roots of `X^q - a`
  set A := Algebra.adjoin ℚ ((X ^ q - C (a : ℚ)).rootSet K)
  have hradne : (X ^ q - C (a : ℚ)) ≠ 0 := X_pow_sub_C_ne_zero hq.out.pos _
  have ha0 : (a : ℚ) ≠ 0 := by
    have := ha.out
    exact_mod_cast (by omega : a ≠ 0)
  -- a root of `X^q - a`
  obtain ⟨β, hβ⟩ : ∃ β : K, β ^ q = algebraMap ℚ K (a : ℚ) := by
    obtain ⟨β, hβ⟩ := hsplits.exists_eval_eq_zero (by
      rw [degree_map, degree_X_pow_sub_C hq.out.pos]
      exact_mod_cast hq.out.ne_zero)
    refine ⟨β, ?_⟩
    simpa [eval_map, sub_eq_zero] using hβ
  have hβne : β ≠ 0 := by
    intro h
    rw [h, zero_pow hq.out.ne_zero] at hβ
    exact ha0 ((algebraMap ℚ K).injective (by rw [← hβ, map_zero]))
  have hrootmem : ∀ γ : K, γ ^ q = algebraMap ℚ K (a : ℚ) → γ ∈ A := by
    intro γ hγ
    apply Algebra.subset_adjoin
    rw [mem_rootSet_of_ne hradne]
    simp [hγ]
  have hβA : β ∈ A := hrootmem β hβ
  have hle : Algebra.adjoin ℚ ((kummerSplittingPolynomial a q).rootSet K) ≤ A := by
    apply Algebra.adjoin_le
    intro x hx
    rw [mem_rootSet_of_ne hprodne] at hx
    unfold kummerSplittingPolynomial at hx
    rw [map_mul] at hx
    rcases mul_eq_zero.mp hx with hc | hr
    · -- `x` is a `q`-th root of unity: `x = (x β) / β`
      have hxq : x ^ q = 1 := by
        have h1 : IsRoot (cyclotomic q K) x := by
          rw [IsRoot, ← map_cyclotomic q (algebraMap ℚ K), eval_map, ← aeval_def]
          exact hc
        have : NeZero (q : K) := ⟨by exact_mod_cast hq.out.ne_zero⟩
        exact ((isRoot_cyclotomic_iff).mp h1).pow_eq_one
      have hxβ : x * β ∈ A := hrootmem _ (by rw [mul_pow, hxq, one_mul, hβ])
      have hinv : β⁻¹ ∈ A :=
        A.inv_mem_of_algebraic (x := ⟨β, hβA⟩) (Algebra.IsAlgebraic.isAlgebraic β)
      have : x = (x * β) * β⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hβne, mul_one]
      rw [this]
      exact A.mul_mem hxβ hinv
    · apply hrootmem
      simpa [sub_eq_zero] using hr
  have htop := IsSplittingField.adjoin_rootSet K (kummerSplittingPolynomial a q)
  rw [htop] at hle
  exact eq_top_iff.mpr hle

/-! ### Hooley's hypothesis gives GRH for the prime Kummer fields -/

theorem dedekindZetaGRH_of_rh {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃+* K') (h : DedekindZetaRH K') :
    Explicit.DedekindZetaGRH K := by
  intro ρ hρ h0 h1
  set Z : ℂ → ℂ := fun s => Hecke.dedekindZetaEntire K s / (s - 1)
  have hZ : IsDedekindZeta K' Z := by
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
      exact ((Hecke.differentiable_dedekindZetaEntire K s).div
        (differentiableAt_id.sub_const 1) hs1).differentiableWithinAt
    · have hs1 : s - 1 ≠ 0 := by
        intro hz
        have := congrArg Complex.re hz
        simp at this
        linarith
      simp only [Z]
      rw [Hecke.dedekindZetaEntire_eq_mul K hs, ← dedekindZeta_eq_of_ringEquiv e,
        mul_div_cancel_left₀ _ hs1]
  have hρ1 : ρ - 1 ≠ 0 := by
    intro hz
    have := congrArg Complex.re hz
    simp at this
    linarith
  exact h Z hZ ρ h0 h1 (by simp only [Z, hρ, zero_div])

theorem kummerZetaGRH_of_hooleyHypothesis {a : ℕ} (h : HooleyHypothesis (a : ℤ)) :
    ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q,
      letI : Fact (2 ≤ a) := ⟨ha⟩
      letI : Fact q.Prime := ⟨hq⟩
      letI : Fact (a < q) := ⟨haq⟩
      Explicit.DedekindZetaGRH (PrimeKummerField a q) := by
  intro q ha hq haq
  let : Fact (2 ≤ a) := ⟨ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  have hk := h q hq.squarefree
  have hcast : ((a : ℤ) : ℚ) = (a : ℚ) := Int.cast_natCast a
  have hpoly : (X ^ q - C (((a : ℤ) : ℚ)) : ℚ[X]) = X ^ q - C (a : ℚ) := by rw [hcast]
  let : IsSplittingField ℚ (PrimeKummerField a q) (X ^ q - C (((a : ℤ) : ℚ))) := by
    rw [hpoly]
    exact isSplittingField_radical a q
  let := NumberField.of_module_finite ℚ (X ^ q - C (((a : ℤ) : ℚ))).SplittingField
  exact dedekindZetaGRH_of_rh
    (IsSplittingField.algEquiv (PrimeKummerField a q) (X ^ q - C (((a : ℤ) : ℚ)))).toRingEquiv
    hk

/-! ### From `upCount` ratios to `HasDensity` -/

theorem mem_S_iff {a p : ℕ} (hp : p.Prime) :
    p ∈ S (a : ℤ) ↔ Artin.IsPrimitiveRootPrime a p := by
  simp only [S, Set.mem_ofPred_eq, Artin.IsPrimitiveRootPrime, PrimitiveRootMod, Int.cast_natCast]
  constructor
  · rintro ⟨hpp, hord⟩
    refine ⟨hpp, ?_, hord⟩
    intro hdvd
    have h0 : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a p).mpr hdvd
    rw [h0] at hord
    have : Fact p.Prime := ⟨hp⟩
    have horder : orderOf (0 : ZMod p) = 0 := orderOf_eq_zero_iff'.mpr fun n hn => by
      rw [zero_pow hn.ne']
      exact zero_ne_one
    rw [horder] at hord
    have := hp.two_le
    omega
  · rintro ⟨hpp, _, hord⟩
    exact ⟨hpp, hord⟩

theorem ncard_eq_upCount (P : ℕ → Prop) [DecidablePred P] {b : ℕ} (hb : 1 ≤ b) :
    ({n : ℕ | P n} ∩ Set.Iio b).ncard = Artin.upCount P ((b : ℝ) - 1) := by
  unfold Artin.upCount
  have hfloor : ⌊(b : ℝ) - 1⌋₊ + 1 = b := by
    rw [show (b : ℝ) - 1 = ((b - 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub hb]; ring,
      Nat.floor_natCast]
    omega
  rw [hfloor]
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [Finset.mem_range, and_comm]

/-- **Formal Conjectures' `conditional_artin_primitive_roots.parts.i` for `a ≥ 2`.** Under
Hooley's hypothesis, the primes with primitive root `a` have a positive density among the
primes. -/
theorem conditional_artin_primitive_roots_parts_i_of_two_le (a : ℤ) (ha2 : 2 ≤ a)
    (ha : ¬IsSquare a) (_ha' : a ≠ -1) (h : HooleyHypothesis a) :
    ∃ x > 0, HasDensity (S a) x {p | p.Prime} := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n := ⟨a.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hn2 : 2 ≤ n := by exact_mod_cast ha2
  have hnsq : ¬ IsSquare n := by
    rintro ⟨m, hm⟩
    exact ha ⟨m, by rw [hm]; push_cast; ring⟩
  obtain ⟨δ, hδ, hT⟩ := Artin.primitiveRoot_density_of_dedekindZetaGRH hn2 hnsq
    (kummerZetaGRH_of_hooleyHypothesis h)
  refine ⟨δ, hδ, ?_⟩
  unfold HasDensity
  have hcomp : Tendsto (fun b : ℕ => ((b : ℝ) - 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop |>.congr
      (fun b => by ring)
  apply (hT.comp hcomp).congr'
  filter_upwards [eventually_ge_atTop 1] with b hb
  simp only [Function.comp_apply, partialDensity]
  have hSP : S (n : ℤ) ∩ {p | p.Prime} = {p : ℕ | Artin.IsPrimitiveRootPrime n p} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hS, hp⟩
      exact (mem_S_iff hp).mp hS
    · intro hpr
      exact ⟨(mem_S_iff hpr.1).mpr hpr, hpr.1⟩
  rw [hSP, ncard_eq_upCount _ hb, ncard_eq_upCount Nat.Prime hb]

end SimultaneousPrimitiveRoots.FC
