module

public import SimultaneousPrimitiveRoots.GaussianPrimePowers
public import SimultaneousPrimitiveRoots.GaussianHeckeCounting

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter

noncomputable section

theorem powerResidueException_count_mul_log_le_primePowerTrace {a q : ℕ}
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] {x : ℝ} (hx : 1 < x) :
    ((powerResidueExceptionPrimes a q x).card : ℝ) *
      ((q : ℝ) * ((q : ℝ) - 1)) * Real.log x ≤
        gaussianPrimePowerTrace (PrimeKummerField a q) x := by
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  exact (powerResidueException_count_mul_log_le_gaussianTrace hx).trans
    (gaussianDegreeOnePrimeTrace_le_primePowerTrace (PrimeKummerField a q) (by linarith))

theorem powerResidueException_count_bound_of_primePowerTrace {a q : ℕ}
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] {x δ C : ℝ}
    (hx : 1 < x)
    (htrace : gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      C * x + C * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ))) :
    ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x := by
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  exact powerResidueException_count_bound_of_gaussianTrace hx
    ((gaussianDegreeOnePrimeTrace_le_primePowerTrace (PrimeKummerField a q) (by linarith)).trans htrace)

/-- The full positive prime-power trace can now be the input to the signed
Hecke argument. The factorization, explicit formula and zero mass remain
explicit hypotheses, rather than conclusions of the comparison lemma. -/
theorem powerResidueException_count_bound_of_full_hecke_traces {ι : Type*} (ρ : ι → ℂ)
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
    (hfactor : gaussianPrimePowerTrace (PrimeKummerField a q) x ≤ E + ((q : ℝ) - 1) * L) :
    let C := CE + (artinGaussianConstant * M + R)
    ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x := by
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  exact powerResidueException_count_bound_of_hecke_traces ρ hx hδ0 hδ1 hCE hM hR
    hstrip hw hmass hlow hformula hE
    ((gaussianDegreeOnePrimeTrace_le_primePowerTrace (PrimeKummerField a q) (by linarith)).trans hfactor)

/-- Still-unproved uniform upper bound on the actual, convergent full
prime-power trace. Small, large-good and bad q share one B and one Q. -/
def GaussianFullLargeGoodTraceBound (A : Finset ℕ) (δ η C : ℝ)
    (B : Set ℕ) (Q : ℝ → ℕ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime,
    ∀ haq : a < q, Q x < q → q ∉ B → q ≤ Nat.floor (2 * x ^ η) →
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      C * x + C * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ))

theorem gaussianLargeGoodTraceBound_of_fullTrace {A : Finset ℕ} {δ η C : ℝ}
    {B : Set ℕ} {Q : ℝ → ℕ} (htrace : GaussianFullLargeGoodTraceBound A δ η C B Q) :
    GaussianLargeGoodTraceBound A δ η C B Q := by
  filter_upwards [htrace, eventually_gt_atTop (0 : ℝ)] with x ht hx
  intro a ha q ha2 hq haq hlarge hgood hcut
  let : Fact (2 ≤ a) := ⟨ha2⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  exact (gaussianDegreeOnePrimeTrace_le_primePowerTrace (PrimeKummerField a q) hx).trans
    (ht a ha q ha2 hq haq hlarge hgood hcut)

theorem mainClaim_of_gaussian_full_sparse_bounds {δ η : ℝ} (hη : 0 ≤ η)
    (hηδ : η < δ) (hηhalf : η < 1 / 2)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hsparse : ∀ A : Finset ℕ, Admissible A →
      ∃ K C Cbad : ℝ, ∃ B : Set ℕ, ∃ Q : ℝ → ℕ,
        0 ≤ K ∧ 0 ≤ C ∧ 0 ≤ Cbad ∧ Summable (badReciprocalWeight B) ∧ Tendsto Q atTop atTop ∧
        SmallExponentPowerResidueBound A η K Q ∧ GaussianFullLargeGoodTraceBound A δ η C B Q ∧
        SparseBadPowerResidueBound A η Cbad B Q) : MainClaim := by
  apply mainClaim_of_gaussian_sparse_bounds hη hηδ hηhalf hsupply
  intro A hA
  obtain ⟨K, C, Cbad, B, Q, hK, hC, hCb, hB, hQ, hs, hg, hb⟩ := hsparse A hA
  exact ⟨K, C, Cbad, B, Q, hK, hC, hCb, hB, hQ, hs,
    gaussianLargeGoodTraceBound_of_fullTrace hg, hb⟩

end

end SimultaneousPrimitiveRoots
