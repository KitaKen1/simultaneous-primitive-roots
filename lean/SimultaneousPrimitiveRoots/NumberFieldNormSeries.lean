module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.BigOperators.Ring.Nat

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Filter Ideal
open scoped Topology
noncomputable section

/-- The existing ideal asymptotic, expressed in the exact coefficient
prefix needed by the general L-series convergence theorem. -/
theorem numberField_idealCount_prefix_limit (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.Icc 1 n,
        (Nat.card {I : Ideal (𝓞 K) // I.absNorm = k} : ℝ)) / (n : ℝ))
      atTop (𝓝 (dedekindZeta_residue K)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // I.absNorm = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- Absolute convergence of the actual ideal-counting L-series throughout
Re(s)>1, with no uniformity in the number field asserted. -/
theorem numberField_idealCount_lseriesSummable (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 K) // I.absNorm = n} : ℂ)) s := by
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n => (Nat.card {I : Ideal (𝓞 K) // I.absNorm = n} : ℝ))
    _ (fun _ => Nat.cast_nonneg _) zero_le_one hs
  exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (by simpa using numberField_idealCount_prefix_limit K)

/-- Sum over actual ideals, using their norm fibers rather than a
separate enumeration. The zero ideal contributes zero. -/
theorem numberField_idealNorm_rpow_summable (K : Type*) [Field K] [NumberField K]
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 K) => (I.absNorm : ℝ) ^ (-σ)) := by
  classical
  have hS := numberField_idealCount_lseriesSummable K (s := (σ : ℂ)) (by simpa using hσ)
  have hcoeff : Summable (fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 K) // I.absNorm = n} : ℝ) * (n : ℝ) ^ (-σ)) := by
    apply (summable_norm_iff.mpr hS).congr
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · simp [hn, Real.zero_rpow (by linarith : -σ ≠ 0)]
    · simp [hn, Real.rpow_neg, div_eq_mul_inv]
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => I.absNorm)
  apply e.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr
  refine ⟨?_, ?_⟩
  · intro n
    let : Finite {I : Ideal (𝓞 K) // I.absNorm = n} :=
      (finite_setOfPred_absNorm_eq n).to_subtype
    let := Fintype.ofFinite {I : Ideal (𝓞 K) // I.absNorm = n}
    exact (hasSum_fintype _).summable
  · apply hcoeff.congr
    intro n
    let : Finite {I : Ideal (𝓞 K) // I.absNorm = n} :=
      (finite_setOfPred_absNorm_eq n).to_subtype
    change _ = ∑' I : {I : Ideal (𝓞 K) // I.absNorm = n}, (I.val.absNorm : ℝ) ^ (-σ)
    calc
      _ = ∑' _I : {I : Ideal (𝓞 K) // I.absNorm = n}, (n : ℝ) ^ (-σ) := by
        simp only [tsum_const, nsmul_eq_mul]
      _ = _ := tsum_congr fun I => by rw [I.property]

/-- In particular the prime-ideal norm series is summable for σ>1. -/
theorem numberField_primeNorm_rpow_summable (K : Type*) [Field K] [NumberField K]
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      (v.asIdeal.absNorm : ℝ) ^ (-σ)) := by
  exact (numberField_idealNorm_rpow_summable K hσ).comp_injective
    (fun v w h => IsDedekindDomain.HeightOneSpectrum.ext h)

end
end SimultaneousPrimitiveRoots
