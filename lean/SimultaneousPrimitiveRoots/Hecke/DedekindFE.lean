module

public import SimultaneousPrimitiveRoots.Hecke.DualClass
public import SimultaneousPrimitiveRoots.Hecke.DedekindEntire
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# The functional equation of the Dedekind zeta function

For an ideal class `c` with representative `J_c ∈ c⁻¹`, put `Ξ_c(s) = N(J_c)^s Λ_c(ns/2)`. For real
`t > 1` this is `Gr(t) · ∑_{I ∈ c} N(I)^{-t}` with a factor `Gr` that does not depend on `c`. The dual
side of Hecke's functional equation is the cone sum of `J_c^∨ = (J_c 𝔡)⁻¹`, which is a class sum
over `c* = c⁻¹ [𝔡]` (`tsum_coneSet_dualFrac`). With the covolume `√|d_K| N(J_c)` and
`N(J_c 𝔡) = N(J_c) |d_K|` this gives

`Ξ_c(1 - s) = |d_K|^{s - 1/2} Ξ_{c*}(s)`,

first for real `s > 1` and then on `ℂ \ {0, 1}` by the identity theorem. Since `c ↦ c*` is a
bijection of the class group, `Ξ_K = ∑_c Ξ_c` satisfies `Ξ_K(1 - s) = |d_K|^{s - 1/2} Ξ_K(s)`, and
`ζ_K = zetaCoefCommon · Ξ_K` with an entire `zetaCoefCommon` (`1/` the Gamma factor).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Ideal NumberField.Units Module Filter Topology
open scoped nonZeroDivisors ENNReal Real

variable (K : Type*) [Field K] [NumberField K]

/-- `c* = c⁻¹ [𝔡]`, the class of `J_c 𝔡`. -/
def classStar (c : ClassGroup (𝓞 K)) : ClassGroup (𝓞 K) :=
  c⁻¹ * ClassGroup.mk0 (diff0 K)

theorem mk0_jd_classRep (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk0 (jd (classRep K c)) = classStar K c := by
  rw [jd, map_mul, classRep_spec, classStar]

theorem dualDen_classRep (c : ClassGroup (𝓞 K)) :
    (dualDen (classRep K c) : ℝ) =
      (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) * |((discr K : ℤ) : ℝ)| := by
  unfold dualDen jd
  rw [Submonoid.coe_mul, _root_.map_mul]
  push_cast
  congr 1
  have h := absNorm_differentIdeal K (𝓞 K)
  have : ((diff0 K : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = differentIdeal ℤ (𝓞 K) := rfl
  rw [this, h, Nat.cast_natAbs, Int.cast_abs]

/-- The `c`-independent real factor `π^{-nt/2} Γ(nt/2) heckeConst(nt/2) w`. -/
def gammaReal (t : ℝ) : ℝ :=
  π ^ (-((finrank ℚ K : ℝ) * t / 2)) * Real.Gamma ((finrank ℚ K : ℝ) * t / 2) *
    heckeConst K ((finrank ℚ K : ℝ) * t / 2) * torsionOrder K

/-- The class sum `A_c(t) = ∑_{I ∈ c} N(I)^{-t}`. -/
def classSum (c : ClassGroup (𝓞 K)) (t : ℝ) : ℝ :=
  ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c}, (absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-t)

/-- `Ξ_c(s) = N(J_c)^s Λ_c(ns/2)`. -/
def classXi (c : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  ((absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) : ℂ) ^ s *
    (classFEPair K c).Λ ((finrank ℚ K : ℂ) * s / 2)

theorem finrank_pos_real : (0 : ℝ) < finrank ℚ K := by
  exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))

/-- The class sum is finite (it is bounded by `ζ_K`). -/
theorem classSum_ennreal_ne_top {t : ℝ} (ht : 1 < t) (c : ClassGroup (𝓞 K)) :
    ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c},
      ENNReal.ofReal ((absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-t)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_comp_le_tsum_of_injective
    (Subtype.val_injective (p := fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I = c))
    (fun I : (Ideal (𝓞 K))⁰ => ENNReal.ofReal ((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-t))))
  rw [tsum_ideal_eq_dedekindZeta K ht]
  exact ENNReal.ofReal_ne_top

theorem classSum_ennreal_eq {t : ℝ} (ht : 1 < t) (c : ClassGroup (𝓞 K)) :
    ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c},
      ENNReal.ofReal ((absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-t)) =
        ENNReal.ofReal (classSum K c t) :=
  ennreal_tsum_ofReal_eq (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (classSum_ennreal_ne_top K ht c)

theorem classSum_nonneg (c : ClassGroup (𝓞 K)) (t : ℝ) : 0 ≤ classSum K c t :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- **The value of `Ξ_c` at real `t > 1`.** -/
theorem classXi_ofReal {t : ℝ} (ht : 1 < t) (c : ClassGroup (𝓞 K)) :
    classXi K c t = ((gammaReal K t * classSum K c t : ℝ) : ℂ) := by
  classical
  have hn0 := finrank_pos_real K
  set s' : ℝ := (finrank ℚ K : ℝ) * t / 2 with hs'
  have hσeq : 2 * s' / (finrank ℚ K : ℝ) = t := by rw [hs']; field_simp
  have hcard : (Fintype.card (classIdx K c) : ℝ) / 2 < s' := by
    rw [card_classIdx_eq_finrank, hs']
    nlinarith
  have hΛ := heckeFEPair_ofReal (classBasis K c) (classEmb K c)
    (by rw [latticeSet_classBasis]; exact idealInK_unit_mul _) hcard
  rw [latticeSet_classBasis, hσeq] at hΛ
  change (classFEPair K c).Λ (s' : ℂ) = _ at hΛ
  have harg : (finrank ℚ K : ℂ) * (t : ℂ) / 2 = ((s' : ℝ) : ℂ) := by rw [hs']; push_cast; ring
  unfold classXi
  rw [harg, hΛ, tsum_mul_left, cone_class_relation K ht c]
  have hN := absNorm_classRep_pos K c
  rw [← Complex.ofReal_cpow hN.le, ← Complex.ofReal_mul]
  congr 1
  unfold gammaReal classSum
  rw [← hs']
  have hNσ : (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ t *
      (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ (-t) = 1 := by
    rw [← Real.rpow_add hN, add_neg_cancel, Real.rpow_zero]
  linear_combination (π ^ (-s') * Real.Gamma s' * heckeConst K s' * (torsionOrder K : ℝ) *
    ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c},
      (absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-t)) * hNσ

/-- The cone sum of the dual lattice of `J_c` in terms of the class `c*`. -/
theorem dual_cone_relation {t : ℝ} (ht : 1 < t) (c : ClassGroup (𝓞 K)) :
    ∑' x : coneSet (latticeSet ((classBasis K c).traceDual : classIdx K c → K)),
        |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| ^ (-t) =
      torsionOrder K * (dualDen (classRep K c) : ℝ) ^ t * classSum K (classStar K c) t := by
  classical
  have hset : latticeSet ((classBasis K c).traceDual : classIdx K c → K) =
      (dualFrac (classRep K c) : Set K) := by
    rw [latticeSet_traceDual_eq, latticeSet_classBasis, traceDualSet_idealInK]
  rw [hset]
  have hd : (0 : ℝ) < dualDen (classRep K c) := by exact_mod_cast dualDen_pos (classRep K c)
  have hE := tsum_coneSet_dualFrac (classRep K c) (fun u => ENNReal.ofReal (u ^ (-t)))
  rw [mk0_jd_classRep] at hE
  have hsplit : ∀ I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = classStar K c},
      ENNReal.ofReal (((absNorm (I.1 : Ideal (𝓞 K)) : ℝ) / dualDen (classRep K c)) ^ (-t)) =
        ENNReal.ofReal ((dualDen (classRep K c) : ℝ) ^ t) *
          ENNReal.ofReal ((absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ (-t)) := fun I => by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _), Real.div_rpow (Nat.cast_nonneg _) hd.le,
      Real.rpow_neg hd.le, div_inv_eq_mul, mul_comm]
  simp_rw [hsplit] at hE
  rw [ENNReal.tsum_mul_left, classSum_ennreal_eq K ht] at hE
  have hfin : ∑' x : coneSet (dualFrac (classRep K c) : Set K),
      ENNReal.ofReal (|((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| ^ (-t)) ≠ ⊤ := by
    rw [hE]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  rw [ennreal_tsum_ofReal_eq (fun _ => Real.rpow_nonneg (abs_nonneg _) _) hfin,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hE
  rw [ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hd.le _)
      (classSum_nonneg K _ t)))] at hE
  rw [hE]
  ring

/-- **The class functional equation at real `t > 1`.** -/
theorem classXi_FE_ofReal {t : ℝ} (ht : 1 < t) (c : ClassGroup (𝓞 K)) :
    classXi K c (1 - (t : ℂ)) =
      ((|((discr K : ℤ) : ℝ)| : ℝ) : ℂ) ^ ((t : ℂ) - 1 / 2) * classXi K (classStar K c) t := by
  classical
  have hn0 := finrank_pos_real K
  set s' : ℝ := (finrank ℚ K : ℝ) * t / 2 with hs'
  have hs'k : (finrank ℚ K : ℝ) / 2 < s' := by rw [hs']; nlinarith
  have hσeq : 2 * s' / (finrank ℚ K : ℝ) = t := by rw [hs']; field_simp
  -- the functional equation of the class
  have hFE := classFEPair_functional_equation K c (s' : ℂ)
  have hdual := classFEPair_symm_ofReal K c hs'k
  rw [hσeq] at hdual
  rw [hdual] at hFE
  have harg : (finrank ℚ K : ℂ) * (1 - (t : ℂ)) / 2 =
      (((finrank ℚ K : ℝ) / 2 : ℝ) : ℂ) - (s' : ℂ) := by
    rw [hs']
    push_cast
    ring
  have harg' : ((((finrank ℚ K : ℝ) / 2 : ℝ) : ℂ) - (s' : ℂ)) =
      ((finrank ℚ K : ℝ) : ℂ) / 2 - (s' : ℂ) := by push_cast; ring
  rw [classXi_ofReal K ht (classStar K c)]
  unfold classXi
  rw [harg, harg', hFE, tsum_mul_left, dual_cone_relation K ht c]
  have hN := absNorm_classRep_pos K c
  have hD : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast discr_ne_zero K
  rw [dualDen_classRep]
  -- everything is real
  rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
    show (t : ℂ) - 1 / 2 = ((t - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hN.le, ← Complex.ofReal_cpow hD.le]
  simp only [← Complex.ofReal_mul]
  congr 1
  unfold gammaReal
  rw [← hs', Real.mul_rpow (Nat.cast_nonneg _) hD.le]
  have e1 : (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ (1 - t) *
      (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ t =
        (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) := by
    rw [← Real.rpow_add hN, sub_add_cancel, Real.rpow_one]
  have e2 : |((discr K : ℤ) : ℝ)| ^ t = |((discr K : ℤ) : ℝ)| ^ (t - 1 / 2) *
      Real.sqrt |((discr K : ℤ) : ℝ)| := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hD]
    congr 1
    ring
  rw [e2]
  have hsq : 0 < Real.sqrt |((discr K : ℤ) : ℝ)| := Real.sqrt_pos.mpr hD
  field_simp
  linear_combination (Real.Gamma s' * heckeConst K s' * (torsionOrder K : ℝ) *
    classSum K (classStar K c) t) * e1

theorem differentiableAt_classXi (c : ClassGroup (𝓞 K)) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (classXi K c) s := by
  classical
  have hn : (finrank ℚ K : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hN : ((absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (absNorm_classRep_pos K c).ne'
  unfold classXi
  refine (differentiableAt_id.const_cpow (Or.inl hN)).mul ?_
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

theorem isPreconnected_compl_zero_one : IsPreconnected (({0, 1} : Set ℂ)ᶜ) := by
  have h : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  exact (Set.Countable.isPathConnected_compl_of_one_lt_rank h
    (Set.toFinite ({0, 1} : Set ℂ)).countable).isConnected.isPreconnected

theorem frequently_ofReal_gt_one {f g : ℂ → ℂ} (h : ∀ t : ℝ, 1 < t → f t = g t) :
    ∃ᶠ z in 𝓝[≠] (2 : ℂ), f z = g z := by
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (Complex.continuous_ofReal.tendsto (2 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := {(2 : ℝ)}ᶜ))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      intro hx'
      apply hx
      simp only [Set.mem_singleton_iff] at hx' ⊢
      exact_mod_cast hx'
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] (2 : ℝ), f x = g x := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))] with x hx
    exact h x hx
  exact ht.frequently hev.frequently

/-- **The functional equation of `Ξ_c` on `ℂ \ {0, 1}`.** -/
theorem classXi_FE (c : ClassGroup (𝓞 K)) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    classXi K c (1 - s) =
      ((|((discr K : ℤ) : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * classXi K (classStar K c) s := by
  set U : Set ℂ := ({0, 1} : Set ℂ)ᶜ with hU
  have hUopen : IsOpen U := (Set.toFinite ({0, 1} : Set ℂ)).isClosed.isOpen_compl
  have hmem : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 := fun z hz => by
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    exact hz
  have hD : ((|((discr K : ℤ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := by
      rw [abs_pos]
      exact_mod_cast discr_ne_zero K
    exact_mod_cast this.ne'
  have hL : AnalyticOnNhd ℂ (fun z => classXi K c (1 - z)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    obtain ⟨hz0, hz1⟩ := hmem z hz
    have h0 : 1 - z ≠ 0 := fun h => hz1 (by linear_combination -h)
    have h1 : 1 - z ≠ 1 := fun h => hz0 (by linear_combination -h)
    exact ((differentiableAt_classXi K c h0 h1).comp z (by fun_prop)).differentiableWithinAt
  have hR : AnalyticOnNhd ℂ (fun z => ((|((discr K : ℤ) : ℝ)| : ℝ) : ℂ) ^ (z - 1 / 2) *
      classXi K (classStar K c) z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    obtain ⟨hz0, hz1⟩ := hmem z hz
    exact (((differentiableAt_id.sub_const _).const_cpow (Or.inl hD)).mul
      (differentiableAt_classXi K _ hz0 hz1)).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := by
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    norm_num
  have hfreq := frequently_ofReal_gt_one (f := fun z => classXi K c (1 - z))
    (g := fun z => ((|((discr K : ℤ) : ℝ)| : ℝ) : ℂ) ^ (z - 1 / 2) *
      classXi K (classStar K c) z) (fun t ht => classXi_FE_ofReal K ht c)
  have hs : s ∈ U := by
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hs0, hs1⟩
  exact hL.eqOn_of_preconnected_of_frequently_eq hR isPreconnected_compl_zero_one h2 hfreq hs

/-- The bijection `c ↦ c* = c⁻¹ [𝔡]` of the class group. -/
def classStarEquiv : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (Equiv.inv _).trans (Equiv.mulRight (ClassGroup.mk0 (diff0 K)))

theorem classStarEquiv_apply (c : ClassGroup (𝓞 K)) : classStarEquiv K c = classStar K c := rfl

/-- `Ξ_K = ∑_c Ξ_c`. -/
def dedekindXi (s : ℂ) : ℂ := ∑ c : ClassGroup (𝓞 K), classXi K c s

theorem differentiableAt_dedekindXi {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (dedekindXi K) s := by
  unfold dedekindXi
  exact DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => differentiableAt_classXi K c hs0 hs1

/-- **The functional equation of `Ξ_K`.** -/
theorem dedekindXi_FE {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    dedekindXi K (1 - s) = ((|((discr K : ℤ) : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * dedekindXi K s := by
  unfold dedekindXi
  simp_rw [classXi_FE K _ hs0 hs1]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (classStarEquiv K) (fun c => classXi K c s)

/-- The entire factor `|det| π^{ns/2} ∏_w m_w^{s m_w/2} Γ(s m_w/2)⁻¹ / w`. -/
def zetaCoefCommon (s : ℂ) : ℂ :=
  ((|LinearMap.det (heckeLin (R := Fin (rank K)) (placeLog (K := K)))| : ℝ) : ℂ) *
    (π : ℂ) ^ ((finrank ℚ K : ℂ) * s / 2) *
    (∏ o, ((placeMult (K := K) o : ℝ) : ℂ) ^ (s * placeMult (K := K) o / 2) *
      (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹) / (torsionOrder K : ℂ)

theorem zetaCoef_eq_mul (c : ClassGroup (𝓞 K)) (s : ℂ) :
    zetaCoef K c s =
      ((absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) : ℂ) ^ s * zetaCoefCommon K s := by
  unfold zetaCoef zetaCoefCommon
  ring

theorem differentiable_zetaCoefCommon : Differentiable ℂ (zetaCoefCommon K) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have h2 : Differentiable ℂ fun s : ℂ => (π : ℂ) ^ ((finrank ℚ K : ℂ) * s / 2) :=
    (by fun_prop : Differentiable ℂ fun s : ℂ => (finrank ℚ K : ℂ) * s / 2).const_cpow (Or.inl hπ)
  have h3 : ∀ o : Option (Fin (rank K)), Differentiable ℂ fun s : ℂ =>
      ((placeMult (K := K) o : ℝ) : ℂ) ^ (s * placeMult (K := K) o / 2) *
        (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹ := fun o => by
    have hm : ((placeMult (K := K) o : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (placeMult_pos o).ne'
    have ha : Differentiable ℂ fun s : ℂ => s * (placeMult (K := K) o : ℂ) / 2 := by fun_prop
    exact (ha.const_cpow (Or.inl hm)).mul (Complex.differentiable_one_div_Gamma.comp ha)
  have h4 : Differentiable ℂ fun s : ℂ => ∏ o, ((placeMult (K := K) o : ℝ) : ℂ) ^
      (s * placeMult (K := K) o / 2) * (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹ :=
    fun s => DifferentiableAt.fun_finsetProd (u := Finset.univ) (fun o _ => (h3 o) s)
  unfold zetaCoefCommon
  exact (((differentiable_const _).mul h2).mul h4).div_const _

theorem dedekindZetaHecke_eq_mul_xi (s : ℂ) :
    dedekindZetaHecke K s = zetaCoefCommon K s * dedekindXi K s := by
  unfold dedekindZetaHecke dedekindXi classXi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [zetaCoef_eq_mul]
  ring

/-- **Hecke's functional equation for the Dedekind zeta function.**
There is a function `Ξ_K`, holomorphic on `ℂ \ {0, 1}`, with
`Ξ_K(1 - s) = |d_K|^{s - 1/2} Ξ_K(s)` and `ζ_K(s) = G_K(s)⁻¹ Ξ_K(s)` for `re s > 1`, where
`G_K(s)⁻¹ = zetaCoefCommon K s` is entire (a constant times
`π^{ns/2} ∏_w m_w^{s m_w/2} / Γ(s m_w/2)`). Equivalently `|d_K|^{s/2} Ξ_K(s)` is invariant under
`s ↦ 1 - s`. -/
theorem dedekindZeta_functional_equation :
    (∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ (dedekindXi K) s) ∧
      (∀ s, s ≠ 0 → s ≠ 1 → dedekindXi K (1 - s) =
        ((|((discr K : ℤ) : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * dedekindXi K s) ∧
      Differentiable ℂ (zetaCoefCommon K) ∧
      ∀ s, 1 < s.re → dedekindZeta K s = zetaCoefCommon K s * dedekindXi K s :=
  ⟨fun _ hs0 hs1 => differentiableAt_dedekindXi K hs0 hs1,
    fun _ hs0 hs1 => dedekindXi_FE K hs0 hs1, differentiable_zetaCoefCommon K,
    fun s hs => by rw [← dedekindZetaHecke_eq K hs, dedekindZetaHecke_eq_mul_xi]⟩

/-- The completed form: `|d_K|^{s/2} Ξ_K(s)` is invariant under `s ↦ 1 - s`. -/
theorem completedDedekindXi_FE {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    ((|((discr K : ℤ) : ℝ)| : ℝ) : ℂ) ^ ((1 - s) / 2) * dedekindXi K (1 - s) =
      ((|((discr K : ℤ) : ℝ)| : ℝ) : ℂ) ^ (s / 2) * dedekindXi K s := by
  have hD : ((|((discr K : ℤ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := by
      rw [abs_pos]
      exact_mod_cast discr_ne_zero K
    exact_mod_cast this.ne'
  rw [dedekindXi_FE K hs0 hs1, ← mul_assoc, ← Complex.cpow_add _ _ hD]
  congr 2
  ring

end SimultaneousPrimitiveRoots.Hecke

end
