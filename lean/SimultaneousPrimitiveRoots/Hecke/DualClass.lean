module

public import SimultaneousPrimitiveRoots.Hecke.DualIdeal

/-!
# Cone sums of the dual ideal

Let `A = J 𝔡` and `d = N(A)`. Since `d ∈ A`, there is an integral ideal `J'` with `(d) = A J'`.
Then `J' = d · A⁻¹ = d · J^∨` as subsets of `K`, `[J'] = [A]⁻¹` and `N(J') = d^{n-1}`. Scaling by
the positive integer `d` preserves the fundamental cone, so the cone sum of `J^∨` is the cone sum
of the integral ideal `J'` with norms divided by `d^n`, and by `tsum_coneSet_eq_class`

`∑_{x ∈ J^∨ ∩ cone} g(|N x|) = w · ∑_{I ∈ [J 𝔡]} g(N(I) / d)`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Ideal Module NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units
open scoped nonZeroDivisors ENNReal

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The different ideal as a nonzero ideal. -/
def diff0 : (Ideal (𝓞 K))⁰ :=
  ⟨differentIdeal ℤ (𝓞 K), mem_nonZeroDivisors_of_ne_zero differentIdeal_ne_bot⟩

/-- `A = J 𝔡`. -/
def jd (J : (Ideal (𝓞 K))⁰) : (Ideal (𝓞 K))⁰ := J * diff0 K

/-- `d = N(J 𝔡)`. -/
def dualDen (J : (Ideal (𝓞 K))⁰) : ℕ := absNorm (jd J : Ideal (𝓞 K))

theorem dualDen_pos (J : (Ideal (𝓞 K))⁰) : 0 < dualDen J :=
  absNorm_pos_of_nonZeroDivisors (jd J)

theorem exists_dualComplement (J : (Ideal (𝓞 K))⁰) :
    ∃ J' : Ideal (𝓞 K), Ideal.span {(dualDen J : 𝓞 K)} = (jd J : Ideal (𝓞 K)) * J' := by
  apply Ideal.dvd_iff_le.mpr
  rw [Ideal.span_singleton_le_iff_mem]
  exact Ideal.absNorm_mem _

/-- The integral ideal `J'` with `(d) = J 𝔡 J'`. -/
def dualComplement (J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K) := (exists_dualComplement J).choose

theorem dualComplement_spec (J : (Ideal (𝓞 K))⁰) :
    Ideal.span {(dualDen J : 𝓞 K)} = (jd J : Ideal (𝓞 K)) * dualComplement J :=
  (exists_dualComplement J).choose_spec

theorem dualDen_ne_zero_ringOfIntegers (J : (Ideal (𝓞 K))⁰) : (dualDen J : 𝓞 K) ≠ 0 := by
  exact_mod_cast (dualDen_pos J).ne'

theorem dualComplement_ne_bot (J : (Ideal (𝓞 K))⁰) : dualComplement J ≠ ⊥ := by
  intro h
  have := dualComplement_spec J
  rw [h, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at this
  exact dualDen_ne_zero_ringOfIntegers J this

/-- `J'` as a nonzero ideal. -/
def dualComp0 (J : (Ideal (𝓞 K))⁰) : (Ideal (𝓞 K))⁰ :=
  ⟨dualComplement J, mem_nonZeroDivisors_of_ne_zero (dualComplement_ne_bot J)⟩

theorem mk0_dualComp0 (J : (Ideal (𝓞 K))⁰) :
    ClassGroup.mk0 (dualComp0 J) = (ClassGroup.mk0 (jd J))⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← map_mul]
  have hmem : ((dualComp0 J * jd J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ :=
    SetLike.coe_mem _
  show ClassGroup.mk0 ⟨_, hmem⟩ = 1
  rw [ClassGroup.mk0_eq_one_iff]
  have h : ((dualComp0 J * jd J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
      Ideal.span {(dualDen J : 𝓞 K)} := by
    rw [Submonoid.coe_mul, mul_comm, dualComplement_spec]
    rfl
  rw [h]
  exact ⟨⟨_, rfl⟩⟩

theorem absNorm_dualComplement (J : (Ideal (𝓞 K))⁰) :
    (absNorm (dualComplement J) : ℝ) = (dualDen J : ℝ) ^ (finrank ℚ K) / dualDen J := by
  have h := congrArg (fun I => (absNorm I : ℝ)) (dualComplement_spec J)
  rw [_root_.map_mul, absNorm_span_singleton] at h
  have hn : (Algebra.norm ℤ (dualDen J : 𝓞 K)).natAbs = dualDen J ^ (finrank ℚ K) := by
    rw [← map_natCast (algebraMap ℤ (𝓞 K)) (dualDen J), Algebra.norm_algebraMap, Int.natAbs_pow,
      Int.natAbs_natCast, RingOfIntegers.rank]
  rw [hn] at h
  have hd : (0 : ℝ) < dualDen J := by exact_mod_cast dualDen_pos J
  push_cast at h
  rw [eq_div_iff hd.ne', mul_comm, h]
  rfl

/-- The dual fractional ideal `J^∨ = (J 𝔡)⁻¹`. -/
abbrev dualFrac (J : (Ideal (𝓞 K))⁰) : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.dual ℤ ℚ ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

omit [NumberField K] in
theorem idealInK_eq_coe (I : Ideal (𝓞 K)) :
    idealInK I = ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
  ext x
  rw [SetLike.mem_coe, FractionalIdeal.mem_coeIdeal]
  rfl

theorem coe_jd (J : (Ideal (𝓞 K))⁰) :
    ((jd J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [jd, Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul]
  rfl

theorem coe_dualComplement (J : (Ideal (𝓞 K))⁰) :
    ((dualComplement J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (dualDen J : K) * dualFrac J := by
  have h := congrArg (fun I : Ideal (𝓞 K) => (I : FractionalIdeal (𝓞 K)⁰ K))
    (dualComplement_spec J)
  simp only [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_mul,
    map_natCast] at h
  have hA : ((jd J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact nonZeroDivisors.coe_ne_zero (jd J)
  rw [dualFrac, dual_eq_inv_mul_different, ← coe_jd]
  calc ((dualComplement J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = (((jd J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ *
          (((jd J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
            ((dualComplement J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) := by
        rw [inv_mul_cancel_left₀ hA]
    _ = _ := by rw [← h, mul_comm]

/-- `J' = d · J^∨` as subsets of `K`. -/
theorem idealInK_dualComplement (J : (Ideal (𝓞 K))⁰) :
    idealInK (dualComplement J) = (fun x => (dualDen J : K) * x) '' (dualFrac J : Set K) := by
  ext y
  rw [idealInK_eq_coe, SetLike.mem_coe, coe_dualComplement, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

omit [NumberField K] in
theorem mixedEmbedding_natCast_mul (d : ℕ) (x : K) :
    mixedEmbedding K ((d : K) * x) = (d : ℝ) • mixedEmbedding K x := by
  rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ]

theorem norm_natCast_mul (d : ℕ) (x : K) :
    Algebra.norm ℚ ((d : K) * x) = (d : ℚ) ^ (finrank ℚ K) * Algebra.norm ℚ x := by
  rw [map_mul, ← map_natCast (algebraMap ℚ K) d, Algebra.norm_algebraMap]

/-- Scaling a set by a positive integer, on the cone. -/
def coneScale (S : Set K) {d : ℕ} (hd : 0 < d) :
    coneSet S → coneSet ((fun x => (d : K) * x) '' S) := fun x =>
  ⟨(d : K) * x, ⟨x, x.2.1, rfl⟩,
    mul_ne_zero (by exact_mod_cast hd.ne') x.2.2.1, by
      rw [mixedEmbedding_natCast_mul]
      exact smul_mem_of_mem x.2.2.2 (by exact_mod_cast hd.ne')⟩

theorem coneScale_bijective (S : Set K) {d : ℕ} (hd : 0 < d) :
    Function.Bijective (coneScale S hd) := by
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · have h' : (d : K) * x = (d : K) * y := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel₀ hdK h')
  · obtain ⟨⟨z, hzS, hz⟩, hy0, hyC⟩ := y.2
    simp only at hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hy0 (by rw [← hz, mul_zero])
    have hzC : mixedEmbedding K z ∈ fundamentalCone K := by
      have : mixedEmbedding K (y : K) = (d : ℝ) • mixedEmbedding K z := by
        rw [← hz, mixedEmbedding_natCast_mul]
      rw [this] at hyC
      exact (smul_mem_iff_mem (by exact_mod_cast hd.ne')).mp hyC
    exact ⟨⟨z, hzS, hz0, hzC⟩, Subtype.ext hz⟩

theorem tsum_coneSet_natCast_mul (S : Set K) {d : ℕ} (hd : 0 < d) (g : ℝ → ℝ≥0∞) :
    ∑' y : coneSet ((fun x => (d : K) * x) '' S), g |((Algebra.norm ℚ (y : K) : ℚ) : ℝ)| =
      ∑' x : coneSet S, g ((d : ℝ) ^ (finrank ℚ K) * |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)|) := by
  rw [← (Equiv.ofBijective _ (coneScale_bijective S hd)).tsum_eq]
  apply tsum_congr
  intro x
  simp only [Equiv.ofBijective_apply, coneScale]
  rw [norm_natCast_mul]
  push_cast
  rw [abs_mul, abs_pow, Nat.abs_cast]

/-- **The cone sum of the dual ideal `J^∨` in terms of the class `[J 𝔡]`.** -/
theorem tsum_coneSet_dualFrac (J : (Ideal (𝓞 K))⁰) (g : ℝ → ℝ≥0∞) :
    ∑' x : coneSet (dualFrac J : Set K), g |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| =
      (torsionOrder K : ℝ≥0∞) *
        ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = ClassGroup.mk0 (jd J)},
          g ((absNorm (I.1 : Ideal (𝓞 K)) : ℝ) / dualDen J) := by
  have hd := dualDen_pos J
  have hd' : (0 : ℝ) < dualDen J := by exact_mod_cast hd
  have hdn : (0 : ℝ) < (dualDen J : ℝ) ^ (finrank ℚ K) := by positivity
  set g' : ℝ → ℝ≥0∞ := fun t => g (t / (dualDen J : ℝ) ^ (finrank ℚ K)) with hg'
  have h1 : ∑' x : coneSet (dualFrac J : Set K), g |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| =
      ∑' x : coneSet (dualFrac J : Set K),
        g' ((dualDen J : ℝ) ^ (finrank ℚ K) * |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)|) := by
    apply tsum_congr
    intro x
    simp only [hg']
    rw [mul_div_cancel_left₀ _ hdn.ne']
  rw [h1, ← tsum_coneSet_natCast_mul _ hd g', ← idealInK_dualComplement]
  have h2 := tsum_coneSet_eq_class (dualComp0 J) (mk0_dualComp0 J) g'
  rw [show ((dualComp0 J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = dualComplement J from rfl] at h2
  rw [h2]
  congr 1
  apply tsum_congr
  intro I
  simp only [hg']
  congr 1
  rw [absNorm_dualComplement J]
  field_simp

end SimultaneousPrimitiveRoots.Hecke

end
