module

public import SimultaneousPrimitiveRoots.GaussianPrimeCounting
public import SimultaneousPrimitiveRoots.GaussianZeroBounds
public import SimultaneousPrimitiveRoots.SparseGoodCounting

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter

noncomputable section

/-- The signed explicit-formula argument, with its actual analytic inputs
displayed. No Hecke zero enumeration or explicit formula is proved here. -/
theorem gaussianHeckeTrace_upper_bound {ι : Type*} (ρ : ι → ℂ) {x δ M R L : ℝ}
    {q : ℕ} (hx : 1 ≤ x) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hq : 1 ≤ q) (hR : 0 ≤ R)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hmass : (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤ M * (q : ℝ) * Real.log (2 * (q : ℝ)))
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ Real.sqrt (8 * δ * Real.log x) →
      (ρ i).re ≤ 1 - δ)
    (hformula : L ≤ artinGaussianZeroRemainder ρ x + R * (q : ℝ) * Real.log (2 * (q : ℝ))) :
    L ≤ (artinGaussianConstant * M + R) * x ^ (1 - δ) * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  have hpow : 1 ≤ x ^ (1 - δ) := Real.one_le_rpow hx (by linarith)
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * q))
  have herr : R * (q : ℝ) * Real.log (2 * (q : ℝ)) ≤
      (R * (q : ℝ) * Real.log (2 * (q : ℝ))) * x ^ (1 - δ) :=
    le_mul_of_one_le_right (mul_nonneg (mul_nonneg hR (Nat.cast_nonneg _)) hlog) hpow
  calc
    L ≤ artinGaussianZeroRemainder ρ x + R * (q : ℝ) * Real.log (2 * (q : ℝ)) := hformula
    _ ≤ (artinGaussianConstant * x ^ (1 - δ)) *
          (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) + R * (q : ℝ) * Real.log (2 * (q : ℝ)) :=
      add_le_add (artinGaussianZeroRemainder_le ρ hx hδ0 hstrip hw hlow) le_rfl
    _ ≤ (artinGaussianConstant * x ^ (1 - δ)) * (M * (q : ℝ) * Real.log (2 * (q : ℝ))) +
        (R * (q : ℝ) * Real.log (2 * (q : ℝ))) * x ^ (1 - δ) :=
      add_le_add (mul_le_mul_of_nonneg_left hmass
        (mul_nonneg artinGaussianConstant_pos.le (Real.rpow_nonneg (by linarith) _))) herr
    _ = _ := by ring

/-- Corollary 5 of the note, conditional on the Hecke explicit formula,
zero-weight mass, cyclotomic upper bound, and trace factorization. The
left side is the actual finite set of power-residue exceptions. -/
theorem powerResidueException_count_bound_of_hecke_traces {ι : Type*} (ρ : ι → ℂ)
    {a q : ℕ} [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    {x δ CE M R E L : ℝ} (hx : 1 < x) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hCE : 0 ≤ CE) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hmass : (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤ M * (q : ℝ) * Real.log (2 * (q : ℝ)))
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ Real.sqrt (8 * δ * Real.log x) →
      (ρ i).re ≤ 1 - δ)
    (hformula : L ≤ artinGaussianZeroRemainder ρ x + R * (q : ℝ) * Real.log (2 * (q : ℝ)))
    (hE : E ≤ CE * x)
    (hfactor : gaussianDegreeOnePrimeTrace (PrimeKummerField a q) x ≤ E + ((q : ℝ) - 1) * L) :
    let C := CE + (artinGaussianConstant * M + R)
    ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x := by
  let CL := artinGaussianConstant * M + R
  have hCL : 0 ≤ CL := add_nonneg (mul_nonneg artinGaussianConstant_pos.le hM) hR
  have hq1 : 0 ≤ (q : ℝ) - 1 := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
    linarith
  have hL := gaussianHeckeTrace_upper_bound ρ hx.le hδ0 hδ1 hq.out.one_le hR
    hstrip hw hmass hlow hformula
  have htrace : gaussianDegreeOnePrimeTrace (PrimeKummerField a q) x ≤
      CE * x + CL * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) := by
    calc
      _ ≤ E + ((q : ℝ) - 1) * L := hfactor
      _ ≤ CE * x + ((q : ℝ) - 1) *
          (CL * x ^ (1 - δ) * (q : ℝ) * Real.log (2 * (q : ℝ))) :=
        add_le_add hE (mul_le_mul_of_nonneg_left hL hq1)
      _ = _ := by ring
  apply powerResidueException_count_bound_of_gaussianTrace hx
  apply htrace.trans
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by have := hq.out.two_le; omega : 1 ≤ 2 * q))
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCL) (by linarith)
  · apply mul_le_mul_of_nonneg_right _ hlog
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hq1)
    exact le_add_of_nonneg_left hCE

/-- Unproved analytic input about a precisely defined, convergent series of
actual degree-one prime ideals. Only large good q are required. -/
def GaussianLargeGoodTraceBound (A : Finset ℕ) (δ η C : ℝ)
    (B : Set ℕ) (Q : ℝ → ℕ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime,
    ∀ haq : a < q, Q x < q → q ∉ B → q ≤ Nat.floor (2 * x ^ η) →
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    gaussianDegreeOnePrimeTrace (PrimeKummerField a q) x ≤
      C * x + C * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ))

theorem largeGoodPowerResidueBound_of_gaussianTrace {A : Finset ℕ} {δ η C : ℝ}
    {B : Set ℕ} {Q : ℝ → ℕ} (hA : ∀ a ∈ A, 2 ≤ a)
    (htrace : GaussianLargeGoodTraceBound A δ η C B Q) :
    LargeGoodPowerResidueBound A δ η C B Q := by
  filter_upwards [htrace, eventually_gt_atTop (1 : ℝ)] with x ht hx
  intro a ha q hq haq hlarge hgood hcut
  let : Fact (2 ≤ a) := ⟨hA a ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  exact powerResidueException_count_bound_of_gaussianTrace hx
    (ht a ha q (hA a ha) hq haq hlarge hgood hcut)

theorem mainClaim_of_gaussian_sparse_bounds {δ η : ℝ} (hη : 0 ≤ η)
    (hηδ : η < δ) (hηhalf : η < 1 / 2)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hsparse : ∀ A : Finset ℕ, Admissible A →
      ∃ K C Cbad : ℝ, ∃ B : Set ℕ, ∃ Q : ℝ → ℕ,
        0 ≤ K ∧ 0 ≤ C ∧ 0 ≤ Cbad ∧ Summable (badReciprocalWeight B) ∧ Tendsto Q atTop atTop ∧
        SmallExponentPowerResidueBound A η K Q ∧ GaussianLargeGoodTraceBound A δ η C B Q ∧
        SparseBadPowerResidueBound A η Cbad B Q) : MainClaim := by
  apply mainClaim_of_small_large_sparse_bounds hη hηδ hηhalf hsupply
  intro A hA
  obtain ⟨K, C, Cbad, B, Q, hK, hC, hCb, hB, hQ, hs, hg, hb⟩ := hsparse A hA
  exact ⟨K, C, Cbad, B, Q, hK, hC, hCb, hB, hQ, hs,
    largeGoodPowerResidueBound_of_gaussianTrace hA.2.1 hg, hb⟩

end

end SimultaneousPrimitiveRoots
