module

public import SimultaneousPrimitiveRoots.GaussianUniformDeletion
public import SimultaneousPrimitiveRoots.KummerQuotientGaussianBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Filter
noncomputable section

/-- The signed full trace corresponds to the full zeta quotient, with no
finite Euler poles on the boundary line Re(s)=0 introduced by deletion. -/
def primeKummerGaussianFullSignedTrace (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (x : ℝ) : ℝ :=
  (gaussianPrimePowerTrace (PrimeKummerField a q) x -
    gaussianPrimePowerTrace (CyclotomicField q ℚ) x) / ((q : ℝ) - 1)

theorem primeKummerBaseRemovedTrace_div_le (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {x : ℝ} (hx : 0 < x) :
    gaussianRemovedPrimeIdealTrace (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) x /
        ((q : ℝ) - 1) ≤ gaussianUniformRowConstant * Real.log (a * q : ℕ) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hd : 0 < (q : ℝ) - 1 := by linarith
  have h := gaussianRemovedBadPrimesTrace_le_uniform (CyclotomicField q ℚ) (a * q)
    (mul_ne_zero (by have := ha.out; omega) hq.out.ne_zero) hx
  change gaussianRemovedPrimeIdealTrace (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) x ≤ _ at h
  rw [prime_cyclotomic_degree hq.out, Nat.cast_sub hq.out.one_le, Nat.cast_one] at h
  apply (div_le_iff₀ hd).mpr
  convert h using 1 <;> first | rfl | ring

theorem primeKummerGaussianSignedTrace_eq_full_removed (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {x : ℝ} (hx : 0 < x) :
    primeKummerGaussianSignedTrace a q x = primeKummerGaussianFullSignedTrace a q x -
      gaussianRemovedPrimeIdealTrace (PrimeKummerField a q) (primeKummerTopBadPrimes a q) x /
        ((q : ℝ) - 1) +
      gaussianRemovedPrimeIdealTrace (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) x /
        ((q : ℝ) - 1) := by
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  let : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ _
  rw [primeKummerGaussianSignedTrace, primeKummerGaussianFullSignedTrace,
    gaussianPrimePowerTrace_eq_deleted_add_removed (PrimeKummerField a q) (primeKummerTopBadPrimes a q) hx,
    gaussianPrimePowerTrace_eq_deleted_add_removed (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) hx,
    Nat.cast_sub hq.out.one_le, Nat.cast_one]
  ring

/-- The top deletion is discarded with its favorable negative sign. -/
theorem primeKummerGaussianSignedTrace_le_full (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {x : ℝ} (hx : 0 < x) :
    primeKummerGaussianSignedTrace a q x ≤ primeKummerGaussianFullSignedTrace a q x +
      gaussianUniformRowConstant * Real.log (a * q : ℕ) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have ht : 0 ≤ gaussianRemovedPrimeIdealTrace (PrimeKummerField a q)
      (primeKummerTopBadPrimes a q) x / ((q : ℝ) - 1) :=
    div_nonneg (gaussianRemovedPrimeIdealTrace_nonneg _ _ _) (by linarith)
  rw [primeKummerGaussianSignedTrace_eq_full_removed a q hx]
  linarith [primeKummerBaseRemovedTrace_div_le a q hx]

theorem primeKummerGaussianSignedTrace_le_full_logq (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    {x : ℝ} (hx : 0 < x) :
    primeKummerGaussianSignedTrace a q x ≤ primeKummerGaussianFullSignedTrace a q x +
      2 * gaussianUniformRowConstant * Real.log q := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by have := ha.out; omega : 0 < a)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.out.pos
  have haq0 : (a : ℝ) ≤ q := by exact_mod_cast haq.out.le
  have hlog : Real.log (a * q : ℕ) ≤ 2 * Real.log q := by
    rw [Nat.cast_mul, Real.log_mul ha0.ne' hq0.ne']
    linarith [Real.log_le_log ha0 haq0]
  apply (primeKummerGaussianSignedTrace_le_full a q hx).trans
  apply add_le_add le_rfl
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hlog gaussianUniformRowConstant_pos.le

def kummerFullToDeletedErrorConstant (R : ℝ) : ℝ := R + 2 * gaussianUniformRowConstant

theorem kummerFullToDeletedErrorConstant_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ kummerFullToDeletedErrorConstant R := by
  unfold kummerFullToDeletedErrorConstant
  have := gaussianUniformRowConstant_pos
  positivity

/-- A full quotient zero formula implies the required actual deleted formula.
The error constant is enlarged uniformly in a,q,x. -/
theorem primeKummerGaussianSignedTrace_formula_of_full {ι : Type*} (ρ : ι → ℂ)
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {x R : ℝ} (hx : 0 < x)
    (hformula : primeKummerGaussianFullSignedTrace a q x ≤
      artinGaussianZeroRemainder ρ x / ((q : ℝ) - 1) + R * (q : ℝ) * Real.log (2 * (q : ℝ))) :
    primeKummerGaussianSignedTrace a q x ≤
      artinGaussianZeroRemainder ρ x / ((q : ℝ) - 1) +
        kummerFullToDeletedErrorConstant R * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hlog0 : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hlog : Real.log q ≤ (q : ℝ) * Real.log (2 * (q : ℝ)) := by
    calc
      _ ≤ Real.log (2 * (q : ℝ)) := Real.log_le_log (by linarith) (by linarith)
      _ ≤ _ := le_mul_of_one_le_left hlog0 (by linarith)
  have hc := mul_le_mul_of_nonneg_left hlog
    (by have := gaussianUniformRowConstant_pos; positivity : 0 ≤ 2 * gaussianUniformRowConstant)
  have h := primeKummerGaussianSignedTrace_le_full_logq a q hx
  unfold kummerFullToDeletedErrorConstant
  nlinarith

/-- The remaining formula now concerns the full zeta quotient, whose
entireness is the classical Aramata--Brauer route. Its actual analytic
construction, zero mass and fixed gap are still unproved inputs here. -/
def KummerFullQuotientGaussianUpperInputs (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (x δ M R : ℝ) : Prop :=
  ∃ (ι : Type) (ρ : ι → ℂ),
    (∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1) ∧
    Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)) ∧
    (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤
      M * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) ∧
    (∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ 2 * (q : ℝ) ^ 2 → (ρ i).re ≤ 1 - δ) ∧
    primeKummerGaussianFullSignedTrace a q x ≤
      artinGaussianZeroRemainder ρ x / ((q : ℝ) - 1) + R * (q : ℝ) * Real.log (2 * (q : ℝ))

theorem kummerQuotientGaussianUpperInputs_of_full {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {x δ M R : ℝ}
    (hx : 0 < x) (h : KummerFullQuotientGaussianUpperInputs a q x δ M R) :
    KummerQuotientGaussianUpperInputs a q x δ M (kummerFullToDeletedErrorConstant R) := by
  obtain ⟨ι, ρ, hstrip, hw, hm, hl, hf⟩ := h
  exact ⟨ι, ρ, hstrip, hw, hm, hl, primeKummerGaussianSignedTrace_formula_of_full ρ hx hf⟩

def UniformKummerFullQuotientGaussianUpperInputs (A : Finset ℕ) (δ η M R : ℝ)
    (B : Set ℕ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime,
    ∀ haq : a < q, q ∉ B → q ≤ Nat.floor (2 * x ^ η) →
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    KummerFullQuotientGaussianUpperInputs a q x δ M R

theorem uniformKummerQuotientGaussianUpperInputs_of_full {A : Finset ℕ}
    {δ η M R : ℝ} {B : Set ℕ}
    (h : UniformKummerFullQuotientGaussianUpperInputs A δ η M R B) :
    UniformKummerQuotientGaussianUpperInputs A δ η M (kummerFullToDeletedErrorConstant R) B := by
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hi hx
  intro a ha q ha2 hq haq hgood hcut
  let : Fact (2 ≤ a) := ⟨ha2⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  exact kummerQuotientGaussianUpperInputs_of_full hx (hi a ha q ha2 hq haq hgood hcut)

theorem exists_gaussianFullLargeGoodTraceBound_of_full_quotient_inputs
    (A : Finset ℕ) {δ η M R : ℝ} {B : Set ℕ}
    (hη : η < 1 / 5) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hinput : UniformKummerFullQuotientGaussianUpperInputs A δ η M R B) :
    ∃ C : ℝ, 0 ≤ C ∧ GaussianFullLargeGoodTraceBound A δ η C B (fun _ => 0) :=
  exists_gaussianFullLargeGoodTraceBound_of_quotient_inputs A hη hδ1 hM
    (kummerFullToDeletedErrorConstant_nonneg hR) (uniformKummerQuotientGaussianUpperInputs_of_full hinput)

/-- Only actual full-quotient analytic inputs with KR and candidate supply
remain: finite Euler correction is proved internally, with favorable sign. -/
theorem mainClaim_of_full_quotient_gaussian_inputs {δ η : ℝ}
    (hη : 0 ≤ η) (hηδ : η < δ) (hηfifth : η < 1 / 5) (hδ1 : δ ≤ 1)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hinput : ∀ A : Finset ℕ, Admissible A → ∃ M R : ℝ, ∃ B : Set ℕ,
      0 ≤ M ∧ 0 ≤ R ∧ Summable (badReciprocalWeight B) ∧
        UniformKummerFullQuotientGaussianUpperInputs A δ η M R B) : MainClaim := by
  apply mainClaim_of_quotient_gaussian_inputs hη hηδ hηfifth hδ1 hsupply
  intro A hA
  obtain ⟨M, R, B, hM, hR, hB, hi⟩ := hinput A hA
  exact ⟨M, kummerFullToDeletedErrorConstant R, B, hM,
    kummerFullToDeletedErrorConstant_nonneg hR, hB, uniformKummerQuotientGaussianUpperInputs_of_full hi⟩

end
end SimultaneousPrimitiveRoots
