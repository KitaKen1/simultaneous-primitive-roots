module

public import SimultaneousPrimitiveRoots.Hecke.DedekindHecke
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Analytic continuation of the Dedekind zeta function (Hecke)

`dedekindZetaHecke K s = ∑_c zetaCoef K c s · Λ_c(ns/2)`, where each coefficient
`N(J_c)^s |det| π^{ns/2} ∏_w m_w^{s m_w/2} Γ(s m_w/2)⁻¹ / w` is entire and each Hecke `Λ_c` is
holomorphic away from `0` and `n/2`. So `dedekindZetaHecke K` is holomorphic on `ℂ \ {0, 1}`.
It agrees with Mathlib's `dedekindZeta K` for real `s > 1`, hence on the half-plane `re s > 1` by the
identity theorem.

Main result: `exists_dedekindZeta_continuation`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Ideal NumberField.Units Module Filter Topology
open scoped nonZeroDivisors Real

variable (K : Type*) [Field K] [NumberField K]

/-- The real coefficient `N(J_c)^σ |det| π^{nσ/2} ∏_w m_w^{σ m_w/2} Γ(σ m_w/2)⁻¹ / w`. -/
def zetaCoefReal (c : ClassGroup (𝓞 K)) (σ : ℝ) : ℝ :=
  (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ σ *
    |LinearMap.det (heckeLin (R := Fin (rank K)) (placeLog (K := K)))| *
    π ^ ((finrank ℚ K : ℝ) * σ / 2) *
    (∏ o, placeMult (K := K) o ^ (σ * placeMult (K := K) o / 2) *
      (Real.Gamma (σ * placeMult (K := K) o / 2))⁻¹) / (torsionOrder K : ℝ)

/-- The entire coefficient of the class `c`. -/
def zetaCoef (c : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  ((absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) : ℂ) ^ s *
    ((|LinearMap.det (heckeLin (R := Fin (rank K)) (placeLog (K := K)))| : ℝ) : ℂ) *
    (π : ℂ) ^ ((finrank ℚ K : ℂ) * s / 2) *
    (∏ o, ((placeMult (K := K) o : ℝ) : ℂ) ^ (s * placeMult (K := K) o / 2) *
      (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹) / (torsionOrder K : ℂ)

theorem differentiable_zetaCoef (c : ClassGroup (𝓞 K)) : Differentiable ℂ (zetaCoef K c) := by
  have hN : ((absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (absNorm_classRep_pos K c).ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have h1 : Differentiable ℂ fun s : ℂ => ((absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) : ℂ) ^ s :=
    differentiable_id.const_cpow (Or.inl hN)
  have h2 : Differentiable ℂ fun s : ℂ => (π : ℂ) ^ ((finrank ℚ K : ℂ) * s / 2) :=
    (by fun_prop : Differentiable ℂ fun s : ℂ => (finrank ℚ K : ℂ) * s / 2).const_cpow (Or.inl hπ)
  have h3 : ∀ o : Option (Fin (rank K)), Differentiable ℂ fun s : ℂ =>
      ((placeMult (K := K) o : ℝ) : ℂ) ^ (s * placeMult (K := K) o / 2) *
        (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹ := fun o => by
    have hm : ((placeMult (K := K) o : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (placeMult_pos o).ne'
    have ha : Differentiable ℂ fun s : ℂ => s * (placeMult (K := K) o : ℂ) / 2 := by fun_prop
    exact (ha.const_cpow (Or.inl hm)).mul (Complex.differentiable_one_div_Gamma.comp ha)
  have h4 : Differentiable ℂ fun s : ℂ => ∏ o, ((placeMult (K := K) o : ℝ) : ℂ) ^
      (s * placeMult (K := K) o / 2) * (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹ := by
    intro s
    exact DifferentiableAt.fun_finsetProd (u := Finset.univ) (fun o _ => (h3 o) s)
  unfold zetaCoef
  exact (((h1.mul_const _).mul h2).mul h4).div_const _

theorem zetaCoef_ofReal (c : ClassGroup (𝓞 K)) (σ : ℝ) :
    zetaCoef K c σ = (zetaCoefReal K c σ : ℂ) := by
  have hN : (0 : ℝ) ≤ absNorm (classRep K c : Ideal (𝓞 K)) := Nat.cast_nonneg _
  have e1 : ((absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (σ : ℂ) =
      (((absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ σ : ℝ) : ℂ) :=
    (Complex.ofReal_cpow hN σ).symm
  have e3 : (π : ℂ) ^ ((finrank ℚ K : ℂ) * (σ : ℂ) / 2) =
      ((π ^ ((finrank ℚ K : ℝ) * σ / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow Real.pi_pos.le]
    norm_cast
  have e4 : ∀ o : Option (Fin (rank K)),
      ((placeMult (K := K) o : ℝ) : ℂ) ^ ((σ : ℂ) * placeMult (K := K) o / 2) *
        (Complex.Gamma ((σ : ℂ) * placeMult (K := K) o / 2))⁻¹ =
      ((placeMult (K := K) o ^ (σ * placeMult (K := K) o / 2) *
        (Real.Gamma (σ * placeMult (K := K) o / 2))⁻¹ : ℝ) : ℂ) := fun o => by
    have hm : (0 : ℝ) ≤ placeMult (K := K) o := (placeMult_pos o).le
    rw [show (σ : ℂ) * (placeMult (K := K) o : ℂ) / 2 = ((σ * placeMult (K := K) o / 2 : ℝ) : ℂ) by
        push_cast; ring, ← Complex.ofReal_cpow hm, Complex.Gamma_ofReal]
    push_cast
    rfl
  unfold zetaCoef zetaCoefReal
  rw [e1, e3, Finset.prod_congr rfl (fun o _ => e4 o)]
  push_cast
  rfl

/-- The real coefficient matches the one in Hecke's formula. -/
theorem zetaCoefReal_eq (c : ClassGroup (𝓞 K)) {σ : ℝ} (hσ : 0 < σ) :
    zetaCoefReal K c σ = (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ σ /
        (torsionOrder K * (π ^ (-(finrank ℚ K * σ / 2)) * Real.Gamma (finrank ℚ K * σ / 2) *
          heckeConst K (finrank ℚ K * σ / 2))) := by
  set n : ℝ := (finrank ℚ K : ℝ) with hn
  have hn0 : 0 < n := by
    rw [hn]
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  set s' : ℝ := n * σ / 2 with hs'
  have hs'0 : 0 < s' := by positivity
  have hprod : ∏ o, Real.Gamma (s' * placeMult (K := K) o / n) *
      placeMult (K := K) o ^ (-(s' * placeMult (K := K) o / n)) =
      (∏ o, placeMult (K := K) o ^ (σ * placeMult (K := K) o / 2) *
        (Real.Gamma (σ * placeMult (K := K) o / 2))⁻¹)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro o _
    have hm := placeMult_pos (K := K) o
    have he : s' * placeMult (K := K) o / n = σ * placeMult (K := K) o / 2 := by
      rw [hs']
      field_simp
    rw [he, Real.rpow_neg hm.le, mul_inv, inv_inv, mul_comm]
  have hP : 0 < ∏ o, placeMult (K := K) o ^ (σ * placeMult (K := K) o / 2) *
      (Real.Gamma (σ * placeMult (K := K) o / 2))⁻¹ := by
    refine Finset.prod_pos fun o _ => ?_
    have hm := placeMult_pos (K := K) o
    exact mul_pos (Real.rpow_pos_of_pos hm _) (inv_pos.mpr (Real.Gamma_pos_of_pos (by positivity)))
  have hdet : 0 < |LinearMap.det (heckeLin (R := Fin (rank K)) (placeLog (K := K)))| :=
    abs_pos.mpr det_heckeLin_ne_zero
  have hw : (0 : ℝ) < torsionOrder K := by exact_mod_cast torsionOrder_pos K
  have hΓ : 0 < Real.Gamma s' := Real.Gamma_pos_of_pos hs'0
  have hπ : 0 < π ^ s' := Real.rpow_pos_of_pos Real.pi_pos _
  unfold zetaCoefReal heckeConst
  rw [← hn, ← hs', hprod, Real.rpow_neg Real.pi_pos.le]
  field_simp

/-- **Hecke's continuation of the Dedekind zeta function.** -/
def dedekindZetaHecke (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K), zetaCoef K c s * (classFEPair K c).Λ ((finrank ℚ K : ℂ) * s / 2)

theorem dedekindZetaHecke_ofReal {σ : ℝ} (hσ : 1 < σ) :
    dedekindZetaHecke K σ = dedekindZeta K σ := by
  rw [dedekindZeta_eq_sum_classFEPair K hσ, dedekindZetaHecke]
  apply Finset.sum_congr rfl
  intro c _
  rw [zetaCoef_ofReal, zetaCoefReal_eq K c (by linarith)]
  congr 2
  push_cast
  ring

theorem differentiableAt_dedekindZetaHecke {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (dedekindZetaHecke K) s := by
  classical
  have hn : (finrank ℚ K : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  unfold dedekindZetaHecke
  refine DifferentiableAt.fun_sum (u := (Finset.univ : Finset (ClassGroup (𝓞 K))))
    (A := fun c s => zetaCoef K c s * (classFEPair K c).Λ ((finrank ℚ K : ℂ) * s / 2))
    (fun c _ => ?_)
  refine (differentiable_zetaCoef K c s).mul ?_
  have h1 : (finrank ℚ K : ℂ) * s / 2 ≠ 0 := by
    intro h
    apply hs0
    have : (finrank ℚ K : ℂ) * s = 0 := by linear_combination 2 * h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hn
    · exact h'
  have h2 : (finrank ℚ K : ℂ) * s / 2 ≠ (((Fintype.card (classIdx K c) : ℝ) / 2 : ℝ) : ℂ) := by
    rw [card_classIdx_eq_finrank]
    intro h
    apply hs1
    push_cast at h
    have : (finrank ℚ K : ℂ) * (s - 1) = 0 := by linear_combination 2 * h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hn
    · exact sub_eq_zero.mp h'
  have hΛ := heckeFEPair_differentiableAt (classBasis K c) (classEmb K c) h1 h2
  have hlin : DifferentiableAt ℂ (fun s : ℂ => (finrank ℚ K : ℂ) * s / 2) s := by fun_prop
  exact hΛ.comp s hlin

theorem abscissaOfAbsConv_idealCount_le :
    LSeries.abscissaOfAbsConv (fun n => (idealCount K n : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    dedekindZeta_summable K (by simpa using hy)

/-- **The continuation agrees with `ζ_K` on `re s > 1`.** -/
theorem dedekindZetaHecke_eq {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaHecke K s = dedekindZeta K s := by
  set U : Set ℂ := {z | (1 : ℝ) < z.re} with hU
  have hUopen : IsOpen U := Complex.isOpen_re_gt 1
  have hne : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 := fun z hz => by
    have hz' : (1 : ℝ) < z.re := hz
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, Complex.zero_re] at hz'
      linarith
    · rw [h, Complex.one_re] at hz'
      linarith
  have hZ : AnalyticOnNhd ℂ (dedekindZetaHecke K) U :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      (differentiableAt_dedekindZetaHecke K (hne z hz).1 (hne z hz).2).differentiableWithinAt)
      hUopen
  have hζ : AnalyticOnNhd ℂ (dedekindZeta K) U := by
    have h := LSeries_analyticOnNhd (fun n => (idealCount K n : ℂ))
    refine h.mono fun z hz => ?_
    have hz' : (1 : ℝ) < z.re := hz
    show LSeries.abscissaOfAbsConv (fun n => (idealCount K n : ℂ)) < z.re
    calc LSeries.abscissaOfAbsConv (fun n => (idealCount K n : ℂ)) ≤ 1 :=
          abscissaOfAbsConv_idealCount_le K
      _ < z.re := by exact_mod_cast hz'
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 1).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), dedekindZetaHecke K z = dedekindZeta K z := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := (Complex.continuous_ofReal.tendsto (2 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := {(2 : ℝ)}ᶜ))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        intro h
        apply hx
        simp only [Set.mem_singleton_iff] at h ⊢
        exact_mod_cast h
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] (2 : ℝ), dedekindZetaHecke K x = dedekindZeta K x := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))] with x hx
      exact dedekindZetaHecke_ofReal K hx
    exact ht.frequently hev.frequently
  exact hZ.eqOn_of_preconnected_of_frequently_eq hζ hpre h2 hfreq hs

/-- **Hecke (1917): the Dedekind zeta function continues holomorphically to `ℂ \ {0, 1}`.** -/
theorem exists_dedekindZeta_continuation :
    ∃ Z : ℂ → ℂ, (∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ Z s) ∧
      ∀ s, 1 < s.re → Z s = dedekindZeta K s :=
  ⟨dedekindZetaHecke K, fun _ hs0 hs1 => differentiableAt_dedekindZetaHecke K hs0 hs1,
    fun _ hs => dedekindZetaHecke_eq K hs⟩

end SimultaneousPrimitiveRoots.Hecke

end
