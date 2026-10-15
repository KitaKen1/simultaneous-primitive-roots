module

public import SimultaneousPrimitiveRoots.Hecke.LeftBound

/-!
# An a priori exponential bound for `(s - 1) ζ_K(s)` in the strip `-1 ≤ Re s ≤ 2`

Phragmén–Lindelöf needs some a priori growth bound in the strip; its constants do not enter the
conclusion, so here they may depend on `K` (and on the choice of class representatives).

* `norm_mellin_le`: a Mellin transform convergent at `a` and `b` is bounded on `a ≤ Re s ≤ b`.
* `WeakFEPair.exists_norm_Λ₀_le`: hence `Λ₀` of an FE pair is bounded on vertical strips.
* `norm_inv_Gamma_le_of_im`: `‖Γ(z)⁻¹‖ ≤ 4 Γ(3 - Re z) e^{π |Im z|}/π` for `Re z ≤ 2`,
  `|Im z| ≥ 1/2` (reflection after two shifts `Γ(z) = (z - 1)(z - 2) Γ(z - 2)`).
* `exists_norm_dedekindZetaEntire_le_strip`: `‖(s - 1) ζ_K(s)‖ ≤ A e^{B |Im s|}` for
  `-1 ≤ Re s ≤ 2`, `|Im s| ≥ 1`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.Units Module Complex MeasureTheory Set Filter Ideal
open scoped Real

/-- `t ^ σ ≤ t ^ a + t ^ b` for `t > 0` and `a ≤ σ ≤ b`. -/
theorem rpow_le_rpow_add_rpow {t a σ b : ℝ} (ht : 0 < t) (h1 : a ≤ σ) (h2 : σ ≤ b) :
    t ^ σ ≤ t ^ a + t ^ b := by
  rcases le_total t 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge ht h h1
    have := Real.rpow_nonneg ht.le b
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h h2
    have := Real.rpow_nonneg ht.le a
    linarith

/-- **A Mellin transform is bounded on vertical strips** where it converges at both edges. -/
theorem norm_mellin_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E}
    {a b : ℝ} (ha : MellinConvergent f a) (hb : MellinConvergent f b) {s : ℂ} (h1 : a ≤ s.re)
    (h2 : s.re ≤ b) :
    ‖mellin f s‖ ≤ (∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖) +
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖ := by
  rw [mellin]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add ha.norm hb.norm]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
    (ha.norm.add hb.norm) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re,
    Complex.ofReal_re, Complex.one_re]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (rpow_le_rpow_add_rpow ht0 (by linarith) (by linarith))
    (norm_nonneg _)

/-- `Λ₀` of an FE pair is bounded on every vertical strip. -/
theorem exists_norm_fePair_Λ₀_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (P : WeakFEPair E) (a b : ℝ) :
    ∃ M, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖P.Λ₀ s‖ ≤ M := by
  have hS := P.isStrongFEPair_toStrongFEPair
  exact ⟨_, fun s h1 h2 => norm_mellin_le (hS.hasMellin a).1 (hS.hasMellin b).1 h1 h2⟩

/-- `‖Γ(z)⁻¹‖ ≤ 4 Γ(3 - Re z) e^{π |Im z|}/π` for `Re z ≤ 2` and `|Im z| ≥ 1/2`. -/
theorem norm_inv_Gamma_le_of_im {z : ℂ} (hre : z.re ≤ 2) (him : 1 / 2 ≤ |z.im|) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ 4 * (Real.Gamma (3 - z.re) * Real.exp (π * |z.im|) / π) := by
  have him0 : z.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at him
    norm_num at him
  have h1 : z - 1 ≠ 0 := by
    intro h
    apply him0
    have := congrArg Complex.im h
    simpa using this
  have h2 : z - 2 ≠ 0 := by
    intro h
    apply him0
    have := congrArg Complex.im h
    simpa using this
  have hG : Complex.Gamma z = (z - 1) * ((z - 2) * Complex.Gamma (z - 2)) := by
    have e1 := Complex.Gamma_add_one (z - 1) h1
    have e2 := Complex.Gamma_add_one (z - 2) h2
    rw [sub_add_cancel] at e1
    rw [show z - 2 + 1 = z - 1 by ring] at e2
    rw [e1, e2]
  have hinv : ∀ w : ℂ, w.im = z.im → ‖w⁻¹‖ ≤ 2 := by
    intro w hw
    rw [norm_inv]
    have : 1 / 2 ≤ ‖w‖ := le_trans (by rw [hw]; exact him) (Complex.abs_im_le_norm w)
    calc ‖w‖⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) this
      _ = 2 := by norm_num
  have hA := norm_inv_Gamma_le (s := z - 2) (by simp; linarith)
  have hre2 : (z - 2).re = z.re - 2 := by simp
  have him2 : (z - 2).im = z.im := by simp
  rw [hre2, him2, show 1 - (z.re - 2) = 3 - z.re by ring] at hA
  rw [hG, mul_inv, mul_inv, norm_mul, norm_mul]
  have hz1 := hinv (z - 1) (by simp)
  have hz2 := hinv (z - 2) (by simp)
  have hnn : 0 ≤ ‖(Complex.Gamma (z - 2))⁻¹‖ := norm_nonneg _
  calc ‖(z - 1)⁻¹‖ * (‖(z - 2)⁻¹‖ * ‖(Complex.Gamma (z - 2))⁻¹‖)
      ≤ 2 * (2 * (Real.Gamma (3 - z.re) * Real.exp (π * |z.im|) / π)) := by
        gcongr
    _ = 4 * (Real.Gamma (3 - z.re) * Real.exp (π * |z.im|) / π) := by ring

/-- At one place, for `-1 ≤ Re s ≤ 2`, `|Im s| ≥ 1` and `1 ≤ m ≤ 2`:
`‖m^{sm/2} Γ(sm/2)⁻¹‖ ≤ 4096 e^{π |Im s|}`. -/
theorem norm_placeFactor_le_strip {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) (ht : 1 ≤ |s.im|)
    {m : ℝ} (hm1 : 1 ≤ m) (hm2 : m ≤ 2) :
    ‖((m : ℝ) : ℂ) ^ (s * m / 2) * (Complex.Gamma (s * m / 2))⁻¹‖ ≤
      4096 * Real.exp (π * |s.im|) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hre : (s * m / 2).re = s.re * m / 2 := by simp
  have him : (s * m / 2).im = s.im * m / 2 := by simp
  have habs : |s.im * m / 2| = |s.im| * m / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hm0, abs_two]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hm0, hre]
  have hG := norm_inv_Gamma_le_of_im (z := s * m / 2) (by rw [hre]; nlinarith)
    (by rw [him, habs]; nlinarith)
  rw [hre, him, habs] at hG
  -- `m ^ (σ m / 2) ≤ 4`
  have hmp : m ^ (s.re * m / 2) ≤ 4 := by
    calc m ^ (s.re * m / 2) ≤ m ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by nlinarith)
      _ = m ^ 2 := Real.rpow_two m
      _ ≤ 4 := by nlinarith
  -- `Γ(3 - σ m / 2) ≤ 256`
  have hy1 : 1 ≤ 3 - s.re * m / 2 := by nlinarith
  have hy4 : 3 - s.re * m / 2 ≤ 4 := by nlinarith
  have hΓ : Real.Gamma (3 - s.re * m / 2) ≤ 256 := by
    have := (Gamma_le_rpow_self hy1).trans (rpow_self_le_rpow_self hy1 hy4)
    have h44 : (4 : ℝ) ^ (4 : ℝ) = 256 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    linarith
  have hexp : Real.exp (π * (|s.im| * m / 2)) ≤ Real.exp (π * |s.im|) := by
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ π * |s.im| := by have := Real.pi_pos; positivity
    nlinarith
  have hπ : 1 ≤ π := by linarith [Real.pi_gt_three]
  have hG' : ‖(Complex.Gamma (s * m / 2))⁻¹‖ ≤ 1024 * Real.exp (π * |s.im|) := by
    refine hG.trans ?_
    have hΓ0 : 0 ≤ Real.Gamma (3 - s.re * m / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
    have he0 : 0 ≤ Real.exp (π * (|s.im| * m / 2)) := (Real.exp_pos _).le
    rw [mul_div_assoc']
    rw [div_le_iff₀ Real.pi_pos]
    have : Real.Gamma (3 - s.re * m / 2) * Real.exp (π * (|s.im| * m / 2)) ≤
        256 * Real.exp (π * |s.im|) := by gcongr
    have he1 : 0 ≤ Real.exp (π * |s.im|) := (Real.exp_pos _).le
    nlinarith
  have hmp0 : 0 ≤ m ^ (s.re * m / 2) := Real.rpow_nonneg hm0.le _
  calc m ^ (s.re * m / 2) * ‖(Complex.Gamma (s * m / 2))⁻¹‖
      ≤ 4 * (1024 * Real.exp (π * |s.im|)) := by gcongr
    _ = 4096 * Real.exp (π * |s.im|) := by ring

variable (K : Type*) [Field K] [NumberField K]

/-- The Gamma factor `C(s)` grows at most exponentially in `|Im s|` on the strip. -/
theorem exists_norm_zetaCoefCommon_le_strip :
    ∃ A B : ℝ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖zetaCoefCommon K s‖ ≤ A * Real.exp (B * |s.im|) := by
  set N₀ := Fintype.card (Option (Fin (rank K)))
  set A₀ := ‖((|LinearMap.det (heckeLin (R := Fin (rank K)) (placeLog (K := K)))| : ℝ) : ℂ)‖
  refine ⟨A₀ * π ^ (finrank ℚ K : ℝ) * 4096 ^ N₀ / ‖(torsionOrder K : ℂ)‖, π * N₀,
    fun s h1 h2 ht => ?_⟩
  have hπ : (0 : ℝ) < π := Real.pi_pos
  unfold zetaCoefCommon
  rw [norm_div, norm_mul, norm_mul, norm_prod, Complex.norm_cpow_eq_rpow_re_of_pos hπ]
  have hre1 : ((finrank ℚ K : ℂ) * s / 2).re = (finrank ℚ K : ℝ) * s.re / 2 := by simp
  rw [hre1]
  have hπpow : π ^ ((finrank ℚ K : ℝ) * s.re / 2) ≤ π ^ (finrank ℚ K : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
      (by have := finrank_pos_real K; nlinarith)
  have hprod : ∏ o, ‖((placeMult (K := K) o : ℝ) : ℂ) ^ (s * placeMult (K := K) o / 2) *
      (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹‖ ≤
      ∏ _o : Option (Fin (rank K)), 4096 * Real.exp (π * |s.im|) :=
    Finset.prod_le_prod (fun o _ => norm_nonneg _)
      (fun o _ => norm_placeFactor_le_strip h1 h2 ht (one_le_placeMult K o)
        (placeMult_le_two K o))
  rw [Finset.prod_const, Finset.card_univ, mul_pow, ← Real.exp_nat_mul] at hprod
  have hw : 0 < ‖(torsionOrder K : ℂ)‖ := by
    have : (torsionOrder K : ℂ) ≠ 0 := by exact_mod_cast torsionOrder_ne_zero K
    exact norm_pos_iff.mpr this
  rw [div_le_iff₀ hw]
  have hA0 : 0 ≤ A₀ := norm_nonneg _
  have hP0 : 0 ≤ ∏ o, ‖((placeMult (K := K) o : ℝ) : ℂ) ^ (s * placeMult (K := K) o / 2) *
      (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹‖ := Finset.prod_nonneg fun o _ => norm_nonneg _
  calc A₀ * π ^ ((finrank ℚ K : ℝ) * s.re / 2) *
        ∏ o, ‖((placeMult (K := K) o : ℝ) : ℂ) ^ (s * placeMult (K := K) o / 2) *
          (Complex.Gamma (s * placeMult (K := K) o / 2))⁻¹‖
      ≤ A₀ * π ^ (finrank ℚ K : ℝ) * (4096 ^ N₀ * Real.exp (N₀ * (π * |s.im|))) := by
        gcongr
    _ = A₀ * π ^ (finrank ℚ K : ℝ) * 4096 ^ N₀ / ‖(torsionOrder K : ℂ)‖ *
          Real.exp (π * N₀ * |s.im|) * ‖(torsionOrder K : ℂ)‖ := by
        rw [show (N₀ : ℝ) * (π * |s.im|) = π * N₀ * |s.im| by ring]
        field_simp

/-- `‖Λ_c(ns/2)‖` is bounded on the strip away from the real axis. -/
theorem exists_norm_classΛ_le_strip (c : ClassGroup (𝓞 K)) :
    ∃ L : ℝ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖(classFEPair K c).Λ ((finrank ℚ K : ℂ) * s / 2)‖ ≤ L := by
  set P := classFEPair K c
  have hn := finrank_pos_real K
  obtain ⟨M, hM⟩ := exists_norm_fePair_Λ₀_le P (-(finrank ℚ K : ℝ)) (finrank ℚ K : ℝ)
  refine ⟨M + 2 * ‖P.f₀‖ + 2 * ‖P.ε‖ * ‖P.g₀‖, fun s h1 h2 ht => ?_⟩
  set w : ℂ := (finrank ℚ K : ℂ) * s / 2 with hw
  have hwre : w.re = (finrank ℚ K : ℝ) * s.re / 2 := by rw [hw]; simp
  have hwim : w.im = (finrank ℚ K : ℝ) * s.im / 2 := by rw [hw]; simp
  have hwim' : 1 / 2 ≤ |w.im| := by
    rw [hwim, abs_div, abs_mul, abs_of_pos hn, abs_two]
    have : 1 ≤ (finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    nlinarith
  have hΛ₀ : ‖P.Λ₀ w‖ ≤ M := hM w (by rw [hwre]; nlinarith) (by rw [hwre]; nlinarith)
  have hinv1 : ‖1 / w‖ ≤ 2 := by
    rw [norm_div, norm_one]
    have : 1 / 2 ≤ ‖w‖ := hwim'.trans (Complex.abs_im_le_norm w)
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hinv2 : ‖P.ε / (P.k - w)‖ ≤ 2 * ‖P.ε‖ := by
    rw [norm_div]
    have hkw : (((P.k : ℂ) - w)).im = -w.im := by simp
    have : 1 / 2 ≤ ‖(P.k : ℂ) - w‖ := by
      refine hwim'.trans (le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _))
      rw [hkw, abs_neg]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg P.ε]
  unfold WeakFEPair.Λ
  calc ‖P.Λ₀ w - (1 / w) • P.f₀ - (P.ε / (P.k - w)) • P.g₀‖
      ≤ ‖P.Λ₀ w - (1 / w) • P.f₀‖ + ‖(P.ε / (P.k - w)) • P.g₀‖ := norm_sub_le _ _
    _ ≤ ‖P.Λ₀ w‖ + ‖(1 / w) • P.f₀‖ + ‖(P.ε / (P.k - w)) • P.g₀‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ M + 2 * ‖P.f₀‖ + 2 * ‖P.ε‖ * ‖P.g₀‖ := by
        rw [norm_smul, norm_smul]
        gcongr

/-- **A priori bound:** `‖(s - 1) ζ_K(s)‖ ≤ A e^{B |Im s|}` on `-1 ≤ Re s ≤ 2`, `|Im s| ≥ 1`. -/
theorem exists_norm_dedekindZetaEntire_le_strip :
    ∃ A B : ℝ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖dedekindZetaEntire K s‖ ≤ A * Real.exp (B * |s.im|) := by
  obtain ⟨A₁, B₁, hC⟩ := exists_norm_zetaCoefCommon_le_strip K
  choose L hL using exists_norm_classΛ_le_strip K
  set L₀ := ∑ c : ClassGroup (𝓞 K),
    (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ (2 : ℝ) * L c
  refine ⟨3 * A₁ * L₀, B₁ + 1, fun s h1 h2 ht => ?_⟩
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_im, abs_zero] at ht
    norm_num at ht
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_im, abs_zero] at ht
    norm_num at ht
  rw [dedekindZetaEntire_eq_xi K hs0 hs1, norm_mul, norm_mul]
  -- `‖Ξ(s)‖ ≤ L₀`
  have hXi : ‖dedekindXi K s‖ ≤ L₀ := by
    unfold dedekindXi classXi
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    have hN := absNorm_classRep_pos K c
    have hN1 : (1 : ℝ) ≤ (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) := by
      exact_mod_cast hN
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hN)]
    have hL0 : 0 ≤ L c := (norm_nonneg _).trans (hL c s h1 h2 ht)
    have hNpow : (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ s.re ≤
        (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 h2
    have hNpow0 : 0 ≤ (absNorm (classRep K c : Ideal (𝓞 K)) : ℝ) ^ (2 : ℝ) :=
      Real.rpow_nonneg (by linarith) _
    exact mul_le_mul hNpow (hL c s h1 h2 ht) (norm_nonneg _) hNpow0
  have hs1n : ‖s - 1‖ ≤ 3 * Real.exp |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : |(s - 1).re| ≤ 2 := by
      rw [Complex.sub_re, Complex.one_re, abs_le]
      constructor <;> linarith
    have him : (s - 1).im = s.im := by simp
    rw [him]
    have hexp := Real.add_one_le_exp (|s.im|)
    have habs := abs_nonneg s.im
    linarith
  have hCb := hC s h1 h2 ht
  have hL₀ : 0 ≤ L₀ := (norm_nonneg _).trans hXi
  have hA₁ : 0 ≤ A₁ * Real.exp (B₁ * |s.im|) := (norm_nonneg _).trans hCb
  calc ‖s - 1‖ * (‖zetaCoefCommon K s‖ * ‖dedekindXi K s‖)
      ≤ (3 * Real.exp |s.im|) * ((A₁ * Real.exp (B₁ * |s.im|)) * L₀) := by gcongr
    _ = 3 * A₁ * L₀ * (Real.exp (B₁ * |s.im|) * Real.exp |s.im|) := by ring
    _ = 3 * A₁ * L₀ * Real.exp ((B₁ + 1) * |s.im|) := by
        rw [← Real.exp_add]
        ring_nf

end SimultaneousPrimitiveRoots.Hecke

end
