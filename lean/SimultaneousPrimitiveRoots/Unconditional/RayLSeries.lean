module

public import SimultaneousPrimitiveRoots.Unconditional.HeckeStatement
public import SimultaneousPrimitiveRoots.Hecke.RayContinuation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Regroup
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Complex.Convex

/-!
# Hecke's continuation of the `L`-series of a ray class character (step Z2)

Let `𝔪` be a modulus of `K` with no infinite part (automatic when `K` is totally complex,
`Modulus.infinitePart_eq_empty`) and finite part `≠ 𝓞`. For every ray class character `χ`,

`L(s, χ) = ∑_{(𝔞, 𝔪) = 1} χ(𝔞) N𝔞^{-s} = ∑_C χ(C) ζ(s, C)`   (`Re s > 1`)

and each partial zeta function `ζ(s, C)` continues holomorphically to `ℂ \ {1}`
(`Hecke.exists_rayPartialZeta_continuation`). Hence `rayClassLSeries χ` continues
holomorphically to `ℂ \ {1}` (`exists_rayClassLSeries_continuation`): this is the existence of
the continuation that `RayClassLZeroFree χ δ` speaks about, and the input for the zero transfer
(steps Z4–Z5 of `docs/unconditional-roadmap.md`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional

open TauCeti TauCeti.GlobalNumberFields NumberField Filter Topology
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- The ray class group is finite (`finite_rayClassGroup`). -/
noncomputable local instance (𝔪 : Modulus K) : Fintype (RayClassGroup 𝔪) := Fintype.ofFinite _

/-- In a totally complex field every modulus has empty infinite part. -/
theorem Modulus.infinitePart_eq_empty [NumberField.IsTotallyComplex K] (𝔪 : Modulus K) :
    𝔪.infinitePart = ∅ := by
  have : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr
      (NumberField.IsTotallyComplex.isComplex w.1)) w.2⟩
  exact Finset.eq_empty_of_isEmpty _

theorem norm_rayClassCharacter (χ : RayClassCharacter 𝔪) (c : RayClassGroup 𝔪) :
    ‖((χ c : ℂˣ) : ℂ)‖ = 1 := by
  have hn : Nat.card (RayClassGroup 𝔪) ≠ 0 := Nat.card_pos.ne'
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card (RayClassGroup 𝔪)) ?_ hn
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

theorem norm_rayCoeff_le (χ : RayClassCharacter 𝔪) (I : (Ideal (𝓞 K))⁰) :
    ‖rayCoeff χ I‖ ≤ 1 := by
  unfold rayCoeff
  split_ifs with h
  · rw [RayClassCharacter.onIdeals_apply]
    exact (norm_rayClassCharacter χ _).le
  · simp

theorem summable_idealTerm_rayCoeff (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    Summable (idealTerm K (rayCoeff χ) s) := by
  rw [← summable_norm_iff]
  refine ((summable_absNorm_rpow_ideal_iff (K := K) (s := s.re)).mpr hs).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun I => ?_
  rw [norm_idealTerm, Real.rpow_neg (Nat.cast_nonneg _), ← one_div]
  exact div_le_div_of_nonneg_right (norm_rayCoeff_le χ I)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem abscissaOfAbsConv_rayClassLSeries_le (χ : RayClassCharacter 𝔪) :
    LSeries.abscissaOfAbsConv (normCoeff K (rayCoeff χ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_normCoeff K (summable_idealTerm_rayCoeff χ (by simpa using hy))

/-- **The `L`-series of `χ` as a combination of partial zeta functions**, at real `σ > 1`. -/
theorem rayClassLSeries_ofReal (χ : RayClassCharacter 𝔪) {σ : ℝ} (hσ : 1 < σ) :
    rayClassLSeries χ σ = ∑ c : RayClassGroup 𝔪, ((χ c : ℂˣ) : ℂ) *
      ((∑' 𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c},
        (Ideal.absNorm (𝔞.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  classical
  have hsum := summable_idealTerm_rayCoeff χ (s := (σ : ℂ)) (by simpa using hσ)
  rw [rayClassLSeries, LSeries_normCoeff K hsum]
  set P := integralIdealsPrimeTo 𝔪
  -- the terms on the ideals prime to `𝔪`
  set g : P → ℂ := fun 𝔞 => ((χ (idealClass 𝔪 𝔞) : ℂˣ) : ℂ) *
    (((Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) ^ (-σ) : ℝ) : ℂ) with hg
  have hterm : ∀ 𝔞 : P, idealTerm K (rayCoeff χ) σ
      ⟨(𝔞 : Ideal (𝓞 K)), mem_nonZeroDivisors_of_ne_zero (Hecke.coe_ne_bot_of_mem 𝔪 𝔞)⟩ =
        g 𝔞 := fun 𝔞 => by
    have hN : (0 : ℝ) ≤ Ideal.absNorm (𝔞 : Ideal (𝓞 K)) := Nat.cast_nonneg _
    have hc : rayCoeff χ ⟨(𝔞 : Ideal (𝓞 K)),
        mem_nonZeroDivisors_of_ne_zero (Hecke.coe_ne_bot_of_mem 𝔪 𝔞)⟩ =
          ((χ (idealClass 𝔪 𝔞) : ℂˣ) : ℂ) := by
      unfold rayCoeff
      rw [dif_pos 𝔞.2, RayClassCharacter.onIdeals_apply]
    rw [idealTerm_def, hc, hg]
    show ((χ (idealClass 𝔪 𝔞) : ℂˣ) : ℂ) / ((Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (σ : ℂ) =
      ((χ (idealClass 𝔪 𝔞) : ℂˣ) : ℂ) * (((Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) ^ (-σ) : ℝ) : ℂ)
    rw [Real.rpow_neg hN, Complex.ofReal_inv, Complex.ofReal_cpow hN, div_eq_mul_inv]
    push_cast
    rfl
  -- the terms vanish off the ideals prime to `𝔪`
  have hsupp : Function.support (idealTerm K (rayCoeff χ) σ) ⊆
      {I : (Ideal (𝓞 K))⁰ | (I : Ideal (𝓞 K)) ∈ P} := by
    intro I hI
    by_contra h
    have h' : ¬ ((I : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪) := h
    apply hI
    rw [idealTerm_def, rayCoeff, dif_neg h', zero_div]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  -- reindex by `P`
  let e : {I : (Ideal (𝓞 K))⁰ | (I : Ideal (𝓞 K)) ∈ P} ≃ P :=
    { toFun := fun I => ⟨(I.1 : Ideal (𝓞 K)), I.2⟩
      invFun := fun 𝔞 => ⟨⟨(𝔞 : Ideal (𝓞 K)),
        mem_nonZeroDivisors_of_ne_zero (Hecke.coe_ne_bot_of_mem 𝔪 𝔞)⟩, 𝔞.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.symm.tsum_eq]
  simp_rw [show ∀ 𝔞 : P, idealTerm K (rayCoeff χ) σ (e.symm 𝔞 : (Ideal (𝓞 K))⁰) = g 𝔞 from
    hterm]
  -- summability of `g` and of its class blocks
  have hgsum : Summable g := by
    have := (hsum.subtype {I : (Ideal (𝓞 K))⁰ | (I : Ideal (𝓞 K)) ∈ P}).comp_injective
      e.symm.injective
    refine this.congr fun 𝔞 => ?_
    exact hterm 𝔞
  -- split by ray class
  have hs2 : Summable fun p : (Σ c : RayClassGroup 𝔪, {𝔞 : P // idealClass 𝔪 𝔞 = c}) =>
      g ((Equiv.sigmaFiberEquiv (idealClass 𝔪)) p) :=
    hgsum.comp_injective (Equiv.sigmaFiberEquiv (idealClass 𝔪)).injective
  rw [← (Equiv.sigmaFiberEquiv (idealClass 𝔪)).tsum_eq, hs2.tsum_sigma, tsum_fintype]
  apply Finset.sum_congr rfl
  intro c _
  have hblock : ∀ 𝔞 : {𝔞 : P // idealClass 𝔪 𝔞 = c},
      g ((Equiv.sigmaFiberEquiv (idealClass 𝔪)) ⟨c, 𝔞⟩) = ((χ c : ℂˣ) : ℂ) *
        (((Ideal.absNorm (𝔞.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) : ℝ) : ℂ) := fun 𝔞 => by
    simp only [Equiv.sigmaFiberEquiv_apply, hg, 𝔞.2]
  simp_rw [hblock]
  rw [tsum_mul_left, Complex.ofReal_tsum]

/-! ### The continuation -/

/-- **Hecke's continuation of `L(s, χ)`**: `∑_C χ(C) ζ(s, C)` with each `ζ(s, C)` continued. -/
def rayLHecke (hnt : 𝔪.finitePart ≠ ⊤) (χ : RayClassCharacter 𝔪) (s : ℂ) : ℂ :=
  ∑ c : RayClassGroup 𝔪, ((χ c : ℂˣ) : ℂ) * Hecke.rayZetaHecke hnt c s

theorem differentiableAt_rayLHecke (hnt : 𝔪.finitePart ≠ ⊤) (χ : RayClassCharacter 𝔪) {s : ℂ}
    (hs1 : s ≠ 1) : DifferentiableAt ℂ (rayLHecke hnt χ) s := by
  classical
  unfold rayLHecke
  exact DifferentiableAt.fun_sum (u := Finset.univ) fun c _ =>
    (Hecke.differentiableAt_rayZetaHecke hnt c hs1).const_mul _

theorem rayLHecke_ofReal (hinf : 𝔪.infinitePart = ∅) (hnt : 𝔪.finitePart ≠ ⊤)
    (χ : RayClassCharacter 𝔪) {σ : ℝ} (hσ : 1 < σ) :
    rayLHecke hnt χ σ = rayClassLSeries χ σ := by
  rw [rayClassLSeries_ofReal χ hσ, rayLHecke]
  apply Finset.sum_congr rfl
  intro c _
  rw [Hecke.rayZetaHecke_ofReal hinf hnt c hσ]

/-- **The continuation agrees with the `L`-series on `Re s > 1`.** -/
theorem rayLHecke_eq (hinf : 𝔪.infinitePart = ∅) (hnt : 𝔪.finitePart ≠ ⊤)
    (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    rayLHecke hnt χ s = rayClassLSeries χ s := by
  set U : Set ℂ := {z | (1 : ℝ) < z.re} with hU
  have hUopen : IsOpen U := Complex.isOpen_re_gt 1
  have hne : ∀ z ∈ U, z ≠ 1 := fun z hz h => by
    have hz' : (1 : ℝ) < z.re := hz
    rw [h, Complex.one_re] at hz'
    exact lt_irrefl _ hz'
  have hZ : AnalyticOnNhd ℂ (rayLHecke hnt χ) U :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      (differentiableAt_rayLHecke hnt χ (hne z hz)).differentiableWithinAt) hUopen
  have hL : AnalyticOnNhd ℂ (rayClassLSeries χ) U := by
    have h := LSeries_analyticOnNhd (normCoeff K (rayCoeff χ))
    refine h.mono fun z hz => ?_
    have hz' : (1 : ℝ) < z.re := hz
    show LSeries.abscissaOfAbsConv (normCoeff K (rayCoeff χ)) < z.re
    calc LSeries.abscissaOfAbsConv (normCoeff K (rayCoeff χ)) ≤ 1 :=
          abscissaOfAbsConv_rayClassLSeries_le χ
      _ < z.re := by exact_mod_cast hz'
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 1).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), rayLHecke hnt χ z = rayClassLSeries χ z := by
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
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] (2 : ℝ), rayLHecke hnt χ x = rayClassLSeries χ x := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))] with x hx
      exact rayLHecke_ofReal hinf hnt χ hx
    exact ht.frequently hev.frequently
  exact hZ.eqOn_of_preconnected_of_frequently_eq hL hpre h2 hfreq hs

/-- **Hecke: the `L`-series of a ray class character continues holomorphically to `ℂ \ {1}`**,
for a modulus with no infinite part and finite part `≠ 𝓞`. -/
theorem exists_rayClassLSeries_continuation (hinf : 𝔪.infinitePart = ∅)
    (hnt : 𝔪.finitePart ≠ ⊤) (χ : RayClassCharacter 𝔪) :
    ∃ f : ℂ → ℂ, (∀ s, s ≠ 1 → DifferentiableAt ℂ f s) ∧
      ∀ s : ℂ, 1 < s.re → f s = rayClassLSeries χ s :=
  ⟨rayLHecke hnt χ, fun _ hs => differentiableAt_rayLHecke hnt χ hs,
    fun _ hs => rayLHecke_eq hinf hnt χ hs⟩

/-- Under `RayClassLZeroFree χ δ`, Hecke's continuation has no zeros in `Re s > 1 - δ`,
`s ≠ 1`. -/
theorem rayLHecke_ne_zero {δ : ℝ} (hinf : 𝔪.infinitePart = ∅) (hnt : 𝔪.finitePart ≠ ⊤)
    {χ : RayClassCharacter 𝔪} (hχ : RayClassLZeroFree χ δ) {s : ℂ} (hs : 1 - δ < s.re)
    (hs1 : s ≠ 1) : rayLHecke hnt χ s ≠ 0 :=
  hχ (rayLHecke hnt χ) (fun _ hz => (differentiableAt_rayLHecke hnt χ hz.2).differentiableWithinAt)
    (fun _ hz => rayLHecke_eq hinf hnt χ hz) s hs hs1

end SimultaneousPrimitiveRoots.Unconditional

end
