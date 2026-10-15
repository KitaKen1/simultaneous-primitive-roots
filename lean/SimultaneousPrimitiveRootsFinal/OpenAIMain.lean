import Solution
import Mathlib

/-!
# OpenAI's conditional main from the unconditional prime-base corollary

The five definitions below are copied from the independent FC statement.
The proof uses the already proved unconditional corollary and does not assume a proof
of any of the four analytic hypotheses.
-/

namespace SimultaneousPrimitiveRootsChallenge

open scoped NumberField nonZeroDivisors Classical

/-- The zero-free hypothesis of [OAI26, Input 3.1]. -/
def HeckeZeroFreeHypothesis : Prop :=
  ∀ (m : ℕ) [NeZero m], 12 ∣ m →
    ∀ (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F],
      ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ →
        ∀ χ : (Ideal (𝓞 F))⁰ →* ℂ, (Set.Finite (Set.range χ) ∧
              (∀ I, χ I = 0 ↔ (I : Ideal (𝓞 F)) ⊔ 𝔪 ≠ ⊤) ∧
              ∀ a : 𝓞 F, a - 1 ∈ 𝔪 →
                (∀ σ : F →+* ℝ, 0 < σ (algebraMap (𝓞 F) F a)) →
                  ∀ I : (Ideal (𝓞 F))⁰, (I : Ideal (𝓞 F)) = Ideal.span {a} → χ I = 1) →
          let principal : Prop := ∀ I : (Ideal (𝓞 F))⁰,
            (I : Ideal (𝓞 F)) ⊔ 𝔪 = ⊤ → χ I = 1
          ∃ L : ℂ → ℂ, Meromorphic L ∧
            DifferentiableOn ℂ L {s : ℂ | s ≠ 1 ∨ ¬ principal} ∧
            (∀ s : ℂ, 1 < s.re → L s = LSeries (fun n =>
              ∑ᶠ I ∈ {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm (I : Ideal (𝓞 F)) = n}, χ I) s) ∧
            ∀ s : ℂ, 1 - (10 : ℝ) ^ (-6 : ℤ) < s.re →
              (s ≠ 1 ∨ ¬ principal) → L s ≠ 0

/-- The rough-factor density of [OAI26, (4.7)]. -/
noncomputable def roughDensity (γ w : ℝ) : ℝ :=
  ∑' j : ℕ, if j = 0 then 0 else if j = 1 then 1 / w else
    (1 / (j.factorial : ℝ)) * ∫ t : Fin (j - 1) → ℝ,
      if (∀ i, γ ≤ t i) ∧ (∑ i, t i) ≤ w - γ then
        (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹ else 0

/-- The marked Type II hypothesis of [OAI26, Input 4.1(i)(ii)]. -/
def MarkedTypeIIHypothesis : Prop :=
  let V (y : ℝ) : ℝ :=
    ∏ p ∈ Nat.primesBelow (⌊y⌋₊ + 1), (1 - 1 / (p : ℝ))
  let W (x : ℝ) : ℝ := Real.exp (Real.log x ^ (0.24 : ℝ))
  let rough (y : ℝ) (n : ℕ) : Prop :=
    0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → y < (p : ℝ)
  let P (x a : ℝ) : Finset ℕ :=
    (Nat.primesBelow (⌊Real.exp (2 * Real.log x ^ a)⌋₊ + 1)).filter
      (fun p => Real.exp (Real.log x ^ a) ≤ (p : ℝ))
  let weight {K : ℕ} (a : Fin K → ℝ) (x : ℝ) (h : ℕ) : ℝ :=
    let ω := fun i : Fin K => ((P x (a i)).filter (· ∣ h)).card
    (2 : ℝ) ^ ((K : ℤ) - ((∑ i, ω i : ℕ) : ℤ)) *
      ∏ i, (ω i : ℝ) / (∑ p ∈ P x (a i), 1 / (p : ℝ))
  let scales (δ κ x Hm Hn : ℝ) : Prop :=
    x ^ δ ≤ Hm ∧ x ^ δ ≤ Hn ∧ x / κ ≤ Hm * Hn ∧ Hm * Hn ≤ κ * x
  let coefficient (x C H : ℝ) (α : ℕ → ℂ) : Prop :=
    (∀ m, α m ≠ 0 → H ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H ∧ rough (W x) m) ∧
      ∀ m, ‖α m‖ ≤ Real.log x ^ C
  let cancellation (x Hm Hn A₀ B A M : ℝ) (α : ℕ → ℂ) : Prop :=
    ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ A₀ →
      ∀ χ : DirichletCharacter ℂ k, ∀ t : ℝ, |t| ≤ 2 * (Hm * Hn) * Real.log x ^ B →
        ‖∑ m ∈ Finset.Icc ⌈Hm⌉₊ ⌊2 * Hm⌋₊,
          α m * χ (m : ZMod k) * (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ M * Hm * Real.log x ^ (-A)
  (∀ δ C Dstar κ : ℝ, 0 < δ → 0 < C → 0 < Dstar → 1 ≤ κ →
    ∀ 𝒜 : ℝ → ℝ → ℝ → Set (ℕ → ℂ),
      (∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
        ∃ M x₀ : ℝ, 0 < M ∧ 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
          ∀ Hm Hn : ℝ, scales δ κ x Hm Hn →
            ∀ α ∈ 𝒜 x Hm Hn, cancellation x Hm Hn A₀ B A M α) →
      ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ a : Fin K → ℝ,
        (0 < K ∧ StrictMono a ∧ ∀ i, (0.1 : ℝ) < a i ∧ a i < (0.2 : ℝ)) →
        ∃ M x₀ : ℝ, 0 < M ∧ 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
          ∀ Hm Hn : ℝ, scales δ κ x Hm Hn →
            ∀ F : ℕ → ℂ, (∀ h : ℕ, 0 < h → ‖F h‖ ≤ 1) →
              (∀ i, ∀ p ∈ P x (a i), ∀ h : ℕ, 0 < h → F (p * h) = F h) →
              ∀ α ∈ 𝒜 x Hm Hn, coefficient x C Hm α →
                ∀ β : ℕ → ℂ, coefficient x C Hn β →
                  ‖∑ m ∈ Finset.Icc ⌈Hm⌉₊ ⌊2 * Hm⌋₊,
                    ∑ n ∈ Finset.Icc ⌈Hn⌉₊ ⌊2 * Hn⌋₊,
                      α m * β n * F (m * n - 1) *
                        (weight a x (m * n - 1) : ℂ)‖ ≤
                    M * (Hm * Hn) * Real.log x ^ (-Dstar)) ∧
  (∀ δ C κ γ wminus wplus : ℝ,
    0 < δ → 0 < C → 1 ≤ κ → 0 < γ → γ < wminus → wminus < wplus → wplus < 1 →
      ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
        ∃ M x₀ : ℝ, 0 < M ∧ 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
          ∀ Hm Hn : ℝ, scales δ κ x Hm Hn →
            wminus ≤ Real.log Hm / Real.log x → Real.log (2 * Hm) / Real.log x ≤ wplus →
              ∀ I : Set ℕ, Set.OrdConnected I →
                I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
                  ∀ v : ℝ, |v| ≤ Real.log x ^ C →
                    cancellation x Hm Hn A₀ B A M (fun m =>
                      if m ∈ I then (m : ℂ) ^ ((v : ℂ) * Complex.I) *
                        ((if rough (x ^ γ) m then 1 else 0) -
                          ((roughDensity γ (Real.log m / Real.log x) /
                            (Real.log x * V (W x)) : ℝ) : ℂ) *
                              (if rough (W x) m then 1 else 0)) else 0))

/-- The block sieve hypothesis of [OAI26, Input 5.1]. -/
def BlockSieveHypothesis : Prop :=
  ∀ η₀ C₀ : ℝ, 0 < η₀ → ∃ M : ℝ, 0 < M ∧ ∃ H₀ : ℕ,
    ∀ (Ω : Finset ℕ) (wt : ℕ → ℝ), (∀ ν ∈ Ω, 0 ≤ wt ν) →
      ∀ (z : ℝ) (D : Finset ℕ), 1 < z →
        (∀ p ∈ D, p.Prime ∧ (p : ℝ) ≤ z) →
        ∀ (bad : ℕ → ℕ → Prop) (Y : ℝ), 0 ≤ Y →
          ∀ g : ℕ → ℝ, (∀ p ∈ D, 0 ≤ g p ∧ g p ≤ 1 - η₀) →
            (∀ u : ℝ, 1 < u →
              ∑ p ∈ D.filter (fun p : ℕ => u < (p : ℝ) ∧ (p : ℝ) ≤ u ^ 2), g p ≤ C₀) →
            let S := ∑ ν ∈ Ω.filter (fun ν => ∀ p ∈ D, ¬ bad p ν), wt ν
            let V := ∏ p ∈ D, (1 - g p)
            let R := fun level : ℝ =>
              ∑ E ∈ D.powerset.filter (fun E => ((∏ p ∈ E, p : ℕ) : ℝ) ≤ level),
                |(∑ ν ∈ Ω.filter (fun ν => ∀ p ∈ E, bad p ν), wt ν) - Y * ∏ p ∈ E, g p|
            (∀ H : ℕ, H₀ ≤ H → Even H →
              |S - Y * V| ≤ M * Real.exp (-(H : ℝ)) * (Y * V) + M * R (z ^ (4 * H + 2))) ∧
            S ≤ M * (Y * V) + M * R (z ^ 10)

/-- The rough density hypothesis of [OAI26, Input 5.2]. -/
def RoughDensityHypothesis : Prop :=
  ∃ bd cd Cd : ℝ, 0 < bd ∧ 0 < cd ∧ 0 < Cd ∧
    ∀ b : ℝ, 0 < b → b < min bd (1 / 2) →
      (∫ t in b..(1 / 2), roughDensity t (1 - t) / t) = roughDensity b 1 - 1 ∧
      roughDensity b 1 ≤ Real.exp (-Real.eulerMascheroniConstant) / b *
        (1 + Cd * Real.exp (-cd / b))

/-- OpenAI [OAI26, Theorem 1.1], as a corollary of [Ki26]. -/
theorem simultaneous_primitive_roots :
    ∀ A : Finset ℕ, A.Nonempty →
      (∀ a ∈ A, a.Prime) →
      (HeckeZeroFreeHypothesis ∧ MarkedTypeIIHypothesis ∧
        BlockSieveHypothesis ∧ RoughDensityHypothesis) →
      ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        c * (x / (Real.log x) ^ 2) ≤
          (Nat.card {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ p.Prime ∧
            ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} : ℝ) := by
  intro A hA hprime _
  exact simultaneous_primitive_roots_unconditional A hA hprime

end SimultaneousPrimitiveRootsChallenge

#print axioms SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots
