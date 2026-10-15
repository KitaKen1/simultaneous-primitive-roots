module

public import SimultaneousPrimitiveRoots.KummerFiniteDeletion
public import SimultaneousPrimitiveRoots.GaussianFixedHeightCounting
public import SimultaneousPrimitiveRoots.FixedChebotarevCounting

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Filter
noncomputable section

/-- Divide the entire zero sum once; there is no fractional-multiplicity index.
The list may repeat entries to encode ordinary nonnegative multiplicities. -/
theorem artinGaussianZeroRemainder_div_le_fixed_height {ι : Type*} (ρ : ι → ℂ)
    {x δ T d M : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T) (hd : 0 < d)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hmass : (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤ d * M)
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ T → (ρ i).re ≤ 1 - δ) :
    artinGaussianZeroRemainder ρ x / d ≤
      artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8)) * M := by
  apply (div_le_iff₀ hd).mpr
  have h := artinGaussianZeroRemainder_le_fixed_height ρ hx hT hstrip hw hlow
  have hc : 0 ≤ artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8)) := by
    have := artinGaussianConstant_pos
    positivity
  calc
    _ ≤ _ := h
    _ ≤ artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8)) * (d * M) :=
      mul_le_mul_of_nonneg_left hmass hc
    _ = _ := by ring

/-- Raw quotient zero mass is allowed to carry the full degree q(q-1).
The actual signed trace is normalized by q-1 before applying the bound. -/
theorem primeKummerGaussianSignedTrace_le_of_quotient_zeros {ι : Type*} (ρ : ι → ℂ)
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {x δ M R : ℝ} (hx : 1 ≤ x) (hδ1 : δ ≤ 1) (_hM : 0 ≤ M) (hR : 0 ≤ R)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hmass : (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤
      M * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)))
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ 2 * (q : ℝ) ^ 2 → (ρ i).re ≤ 1 - δ)
    (hformula : primeKummerGaussianSignedTrace a q x ≤
      artinGaussianZeroRemainder ρ x / ((q : ℝ) - 1) +
        R * (q : ℝ) * Real.log (2 * (q : ℝ))) :
    primeKummerGaussianSignedTrace a q x ≤
      (artinGaussianConstant * M + R) * x ^ (1 - δ) *
        (q : ℝ) * Real.log (2 * (q : ℝ)) +
      artinGaussianConstant * M * x * (q : ℝ) * Real.log (2 * (q : ℝ)) *
        Real.exp (-(q : ℝ) ^ 4 / 2) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hd : 0 < (q : ℝ) - 1 := by linarith
  have hm : (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤
      ((q : ℝ) - 1) * (M * (q : ℝ) * Real.log (2 * (q : ℝ))) := by
    convert hmass using 1
    ring
  have hrem := artinGaussianZeroRemainder_div_le_fixed_height ρ hx
    (T := 2 * (q : ℝ) ^ 2) (by positivity) hd hstrip hw hm hlow
  have heq : -(2 * (q : ℝ) ^ 2) ^ 2 / 8 = -(q : ℝ) ^ 4 / 2 := by ring
  rw [heq] at hrem
  have hp : 1 ≤ x ^ (1 - δ) := Real.one_le_rpow hx (by linarith)
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  calc
    _ ≤ _ := hformula
    _ ≤ artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-(q : ℝ) ^ 4 / 2)) *
          (M * (q : ℝ) * Real.log (2 * (q : ℝ))) +
        (R * (q : ℝ) * Real.log (2 * (q : ℝ))) * x ^ (1 - δ) :=
      add_le_add hrem (le_mul_of_one_le_right (by positivity) hp)
    _ = _ := by ring

/-- The deterministic decomposition is supplied by the unconditional theorem
exists_uniformKummerGaussianTraceDecomposition; only the zero-side data remain. -/
theorem primeKummerGaussianTrace_bound_of_quotient_zeros {ι : Type*} (ρ : ι → ℂ)
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {x δ CE M R : ℝ} (hx : 1 ≤ x) (hδ1 : δ ≤ 1)
    (hCE : 0 ≤ CE) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hmass : (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤
      M * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)))
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ 2 * (q : ℝ) ^ 2 → (ρ i).re ≤ 1 - δ)
    (hformula : primeKummerGaussianSignedTrace a q x ≤
      artinGaussianZeroRemainder ρ x / ((q : ℝ) - 1) +
        R * (q : ℝ) * Real.log (2 * (q : ℝ)))
    (hdecomp : gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      CE * x + ((q : ℝ) - 1) * primeKummerGaussianSignedTrace a q x) :
    let C := gaussianFixedHeightCountingConstant CE M R
    gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      C * x + C * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) := by
  have hL := primeKummerGaussianSignedTrace_le_of_quotient_zeros ρ hx hδ1 hM hR
    hstrip hw hmass hlow hformula
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hq1 : 0 ≤ (q : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hC := artinGaussianConstant_pos
  have htail := gaussian_q_height_tail_le (q := (q : ℝ)) (by linarith : (1 : ℝ) ≤ q)
  have hhigh : ((q : ℝ) - 1) *
      (artinGaussianConstant * M * x * (q : ℝ) * Real.log (2 * (q : ℝ)) *
        Real.exp (-(q : ℝ) ^ 4 / 2)) ≤ 4 * artinGaussianConstant * M * x := by
    calc
      _ = (artinGaussianConstant * M * x) *
          (((q : ℝ) - 1) * (q : ℝ) * Real.log (2 * (q : ℝ)) *
            Real.exp (-(q : ℝ) ^ 4 / 2)) := by ring
      _ ≤ (artinGaussianConstant * M * x) *
          ((q : ℝ) ^ 2 * Real.log (2 * (q : ℝ)) * Real.exp (-(q : ℝ) ^ 4 / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        gcongr
        nlinarith
      _ ≤ (artinGaussianConstant * M * x) * 4 :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  let CL := artinGaussianConstant * M + R
  have hCL : 0 ≤ CL := by dsimp [CL]; positivity
  have hfirst : 0 ≤ CE + 4 * artinGaussianConstant * M := by positivity
  have htrace : gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      (CE + 4 * artinGaussianConstant * M) * x +
        CL * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) := by
    calc
      _ ≤ CE * x + ((q : ℝ) - 1) *
          ((artinGaussianConstant * M + R) * x ^ (1 - δ) * (q : ℝ) * Real.log (2 * (q : ℝ)) +
            artinGaussianConstant * M * x * (q : ℝ) * Real.log (2 * (q : ℝ)) *
              Real.exp (-(q : ℝ) ^ 4 / 2)) :=
        hdecomp.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hL hq1))
      _ = CE * x + CL * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) +
          ((q : ℝ) - 1) * (artinGaussianConstant * M * x * (q : ℝ) * Real.log (2 * (q : ℝ)) *
            Real.exp (-(q : ℝ) ^ 4 / 2)) := by dsimp [CL]; ring
      _ ≤ _ := by nlinarith [hhigh]
  apply htrace.trans
  change _ ≤ gaussianFixedHeightCountingConstant CE M R * x + _
  unfold gaussianFixedHeightCountingConstant
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCL) (by linarith)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hfirst)
          (mul_nonneg (Nat.cast_nonneg q) hq1)) (Real.rpow_nonneg (by linarith) _)) hlog

/-- Witnesses for the upper-bound argument, with the formula stated for the
actual signed Kummer trace. Their existence is not asserted here. In an
analytic construction rho must list the actual quotient zeros correctly. -/
def KummerQuotientGaussianUpperInputs (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (x δ M R : ℝ) : Prop :=
  ∃ (ι : Type) (ρ : ι → ℂ),
    (∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1) ∧
    Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)) ∧
    (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤
      M * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) ∧
    (∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ 2 * (q : ℝ) ^ 2 → (ρ i).re ≤ 1 - δ) ∧
    primeKummerGaussianSignedTrace a q x ≤
      artinGaussianZeroRemainder ρ x / ((q : ℝ) - 1) + R * (q : ℝ) * Real.log (2 * (q : ℝ))

def UniformKummerQuotientGaussianUpperInputs (A : Finset ℕ) (δ η M R : ℝ)
    (B : Set ℕ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime,
    ∀ haq : a < q, q ∉ B → q ≤ Nat.floor (2 * x ^ η) →
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    KummerQuotientGaussianUpperInputs a q x δ M R

/-- Finite deletion and the cyclotomic base bound are discharged, not assumed. -/
theorem exists_gaussianFullLargeGoodTraceBound_of_quotient_inputs
    (A : Finset ℕ) {δ η M R : ℝ} {B : Set ℕ}
    (hη : η < 1 / 5) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hinput : UniformKummerQuotientGaussianUpperInputs A δ η M R B) :
    ∃ C : ℝ, 0 ≤ C ∧ GaussianFullLargeGoodTraceBound A δ η C B (fun _ => 0) := by
  obtain ⟨CE, hCE, hd⟩ := exists_uniformKummerGaussianTraceDecomposition A hη
  refine ⟨gaussianFixedHeightCountingConstant CE M R,
    gaussianFixedHeightCountingConstant_nonneg hCE hM hR, ?_⟩
  filter_upwards [hd, hinput, eventually_ge_atTop (1 : ℝ)] with x hdx hix hx
  intro a ha q ha2 hq haq _hlarge hgood hcut
  let : Fact (2 ≤ a) := ⟨ha2⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  obtain ⟨ι, ρ, hstrip, hw, hmass, hlow, hformula⟩ := hix a ha q ha2 hq haq hgood hcut
  exact primeKummerGaussianTrace_bound_of_quotient_zeros ρ hx hδ1 hCE hM hR
    hstrip hw hmass hlow hformula (hdx a ha ha2 q hq haq hcut)

/-- The fixed-q count, the common slow cutoff and finite deletion have been
proved. Candidate supply and uniform quotient-zero inputs with KR remain
genuine hypotheses; this is not an unconditional proof of MainClaim. -/
theorem mainClaim_of_quotient_gaussian_inputs {δ η : ℝ}
    (hη : 0 ≤ η) (hηδ : η < δ) (hηfifth : η < 1 / 5) (hδ1 : δ ≤ 1)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hinput : ∀ A : Finset ℕ, Admissible A → ∃ M R : ℝ, ∃ B : Set ℕ,
      0 ≤ M ∧ 0 ≤ R ∧ Summable (badReciprocalWeight B) ∧
        UniformKummerQuotientGaussianUpperInputs A δ η M R B) : MainClaim := by
  apply mainClaim_of_all_good_gaussian_bounds hη hηδ hηfifth hsupply
  intro A hA
  obtain ⟨M, R, B, hM, hR, hB, hi⟩ := hinput A hA
  obtain ⟨C, hC, hb⟩ := exists_gaussianFullLargeGoodTraceBound_of_quotient_inputs
    A hηfifth hδ1 hM hR hi
  exact ⟨C, B, hC, hB, hb⟩

end
end SimultaneousPrimitiveRoots
