module

public import SimultaneousPrimitiveRoots.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData

/-! Generalization of `SimultaneousPrimitiveRoots.KummerUniformDeletionBridge` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField IsDedekindDomain Filter
noncomputable section

/-- The signed trace attached to `F_K = (s - 1) ζ_K(s)`: `(Θ_K(x) - M(x))/(q - 1)`, where
`M(x) = ∫_{t > 1} w(t/x) dt` is the main term coming from the pole of `ζ_K` at `1`
(it replaces `Θ_{ℚ(ζ_q)}` of the quotient version). -/
def primeKummerGaussianFullSignedTrace (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (x : ℝ) : ℝ :=
  (gaussianPrimePowerTrace (PrimeKummerField a q) x -
    ∫ t in Set.Ioi (1 : ℝ), artinGaussianWeight (t / x)) / ((q : ℝ) - 1)

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

end
end SimultaneousPrimitiveRoots.Explicit
