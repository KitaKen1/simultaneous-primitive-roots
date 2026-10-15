module

public import SimultaneousPrimitiveRoots.Hecke.ClassSum
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# The Dedekind zeta function as a sum over ideals and over ideal classes

For real `σ > 1`, Mathlib's `dedekindZeta K σ` (an `LSeries` of ideal counts) equals
`∑_{I ≠ 0} N(I)^{-σ}`, and splitting by ideal class,

`ζ_K(σ) = ∑_c ∑_{I ∈ c} N(I)^{-σ}`.

The convergence for `σ > 1` uses Mathlib's ideal counting asymptotics
(`Ideal.tendsto_norm_le_div_atTop₀`), as in the proof of the class number formula.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Ideal Filter Topology
open scoped nonZeroDivisors ENNReal

variable (K : Type*) [Field K] [NumberField K]

/-- The coefficients of the Dedekind zeta function. -/
def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

theorem dedekindZeta_eq_LSeries (s : ℂ) :
    dedekindZeta K s = LSeries (fun n => (idealCount K n : ℂ)) s := rfl

theorem exists_tendsto_idealCount :
    ∃ l : ℝ, Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / (n : ℝ))
      atTop (𝓝 l) := by
  refine ⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n ↦ ?_⟩
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum, idealCount]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem dedekindZeta_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) s := by
  obtain ⟨l, hl⟩ := exists_tendsto_idealCount K
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) :=
    Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hl)
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO
    (fun n => Nat.cast_nonneg (idealCount K n)) zero_le_one hs
  simpa using this

/-- The real terms `idealCount n · n^{-σ}` (`0` at `n = 0`). -/
def zetaTerm (σ : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else (idealCount K n : ℝ) * (n : ℝ) ^ (-σ)

theorem zetaTerm_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ zetaTerm K σ n := by
  unfold zetaTerm
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem hasSum_zetaTerm {σ : ℝ} (hσ : 1 < σ) :
    HasSum (zetaTerm K σ) (dedekindZeta K σ).re := by
  have h : HasSum (LSeries.term (fun n => (idealCount K n : ℂ)) σ) (dedekindZeta K σ) :=
    (dedekindZeta_summable K (s := (σ : ℂ)) (by simpa using hσ)).LSeriesHasSum
  have h2 := (Complex.reCLM.hasSum h)
  refine h2.congr_fun ?_
  intro n
  simp only [Complex.reCLM_apply]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    simp [zetaTerm, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, zetaTerm, if_neg hn]
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hc : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hn']
      push_cast
      rfl
    rw [hc, Real.rpow_neg hn', ← div_eq_mul_inv]
    rw [show ((idealCount K n : ℂ)) = (((idealCount K n : ℝ)) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_div, Complex.ofReal_re]

theorem finite_nzIdeal_fiber (n : ℕ) :
    Finite {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} := by
  have hfin : Finite {I : Ideal (𝓞 K) // absNorm I = n} := (finite_setOfPred_absNorm_eq n).to_subtype
  refine Finite.of_injective (fun I => (⟨I.1.1, I.2⟩ : {I : Ideal (𝓞 K) // absNorm I = n}))
    (fun I J h => ?_)
  have h' := congrArg Subtype.val h
  simp only at h'
  exact Subtype.ext (Subtype.ext h')

theorem natCard_nzIdeal_fiber {n : ℕ} (hn : n ≠ 0) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} = idealCount K n := by
  unfold idealCount
  refine Nat.card_congr ⟨fun I => ⟨I.1.1, I.2⟩, fun I => ⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero ?_⟩,
    I.2⟩, fun I => rfl, fun I => rfl⟩
  intro h0
  have := I.2
  rw [h0, map_zero] at this
  exact hn this.symm

theorem natCard_nzIdeal_fiber_zero :
    Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = 0} = 0 := by
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun I => ?_⟩
  have h := I.2
  rw [absNorm_eq_zero_iff] at h
  exact nonZeroDivisors.coe_ne_zero I.1 h

/-- **`ζ_K(σ) = ∑_{I ≠ 0} N(I)^{-σ}`** for real `σ > 1`, in `ℝ≥0∞`. -/
theorem tsum_ideal_eq_dedekindZeta {σ : ℝ} (hσ : 1 < σ) :
    ∑' I : (Ideal (𝓞 K))⁰, ENNReal.ofReal ((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-σ)) =
      ENNReal.ofReal (dedekindZeta K σ).re := by
  have hS := hasSum_zetaTerm K hσ
  rw [← hS.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (zetaTerm_nonneg K σ) hS.summable,
    ← (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => absNorm (I : Ideal (𝓞 K)))).tsum_eq,
    ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  have hconst : ∀ I : {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n},
      ENNReal.ofReal ((absNorm
        (((Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => absNorm (I : Ideal (𝓞 K))))
          ⟨n, I⟩ : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-σ)) =
        ENNReal.ofReal ((n : ℝ) ^ (-σ)) := fun I => by
    simp only [Equiv.sigmaFiberEquiv_apply]
    rw [I.2]
  simp_rw [hconst]
  have := finite_nzIdeal_fiber K n
  let := Fintype.ofFinite {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n}
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} : ℝ≥0∞) =
      (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} : ℝ≥0∞) := by
    rw [Nat.card_eq_fintype_card]
  rw [hcard]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [natCard_nzIdeal_fiber_zero]
    simp [zetaTerm]
  · rw [natCard_nzIdeal_fiber K hn, zetaTerm, if_neg hn,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- Splitting the ideal sum by ideal class. -/
theorem tsum_ideal_eq_sum_class (F : (Ideal (𝓞 K))⁰ → ℝ≥0∞) :
    ∑' I : (Ideal (𝓞 K))⁰, F I =
      ∑ c : ClassGroup (𝓞 K), ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c}, F I := by
  rw [← (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I)).tsum_eq,
    ENNReal.tsum_sigma', tsum_fintype]
  rfl

end SimultaneousPrimitiveRoots.Hecke

end
