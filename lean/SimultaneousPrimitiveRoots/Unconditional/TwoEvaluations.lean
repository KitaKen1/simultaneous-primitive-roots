module

public import SimultaneousPrimitiveRoots.Unconditional.GaussianSignal

/-!
# [A]'s two evaluations of the common signal (level 3 of step Z6)

[A] (`A-02a:0123–0164`) evaluates one scalar `I_Z` in two ways:

* Cauchy–Schwarz and the reflected second moment (`prop:reflection`) give
  `I_Z ≪_ε Z^{933/2000 + ε}` for every `ε > 0`;
* Poisson summation, the Euler product and the zero-density estimate give
  `I_Z = c₀ f_η(Z) + O(Z^{7/15 - .0004})` with `c₀ ≠ 0`.

Since `933/2000 = 7/15 - 1/6000`, the two give `f_η(Z) ≪ Z^{7/15 - 1/20000}`
(`isBigO_of_hasTwoEvaluations`), which is the growth required of a Mellin signal of width
`κ = 1/20000` (`HasMellinSignal`, with `1 - κ - 8/15 = 7/15 - 1/20000`).

`HasTwoEvaluations f` states the two evaluations for a signal `f`; the content of [A] §§3–6 is to
construct `I_Z` and prove them for [A]'s signal `f_η`. With the inverse-Mellin construction of
`GaussianSignal.lean` this gives a Mellin signal of width `1/20000`
(`hasMellinSignal_of_hasTwoEvaluations`), and so the Hecke zero-free strip of every width
`0 < δ ≤ 1/20000` (`heckeZeroFreeStrip_of_heckeTwoEvaluations`) from `HeckeTwoEvaluations`: for
every ray class character `χ` of every cyclotomic field `F ⊇ μ₁₂`, a multiplier `H` with [A]'s two
evaluations.

[A]'s signal is built from the `S`-incomplete `L^S(s, η)` with `S ⊇` the primes of `𝔪`; it is
`gaussianSignal χ (H / E)` for the finite Euler product `E` at the extra primes of `S`, and `H / E`
is again holomorphic and nowhere zero on the required half-plane
`Re s > 1 - 1/20000`, and bounded on `Re s ≥ 2`. The finite Euler factor `E` itself is
holomorphic and nowhere zero on `Re s > 0`; [A] only asserts that property for `H` on
a neighborhood of `Re s ≥ .998`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional

open Filter Asymptotics TauCeti TauCeti.GlobalNumberFields NumberField

noncomputable section

/-- **[A]'s two evaluations of a common signal `I` against `f`**: `I(Z) ≪_ε Z^{933/2000 + ε}` for
every `ε > 0`, and `I(Z) - c₀ f(Z) ≪ Z^{7/15 - 4/10000}` with `c₀ ≠ 0`. -/
def HasTwoEvaluations (f : ℝ → ℂ) : Prop :=
  ∃ (I : ℝ → ℂ) (c₀ : ℂ), c₀ ≠ 0 ∧
    (∀ ε : ℝ, 0 < ε → I =O[atTop] fun Z : ℝ => Z ^ ((933 / 2000 : ℝ) + ε)) ∧
    (fun Z => I Z - c₀ * f Z) =O[atTop] fun Z : ℝ => Z ^ ((7 / 15 : ℝ) - 4 / 10000)

/-- Powers of `Z` are ordered at `∞` by their exponents. -/
theorem rpow_isBigO_rpow_atTop {a b : ℝ} (h : a ≤ b) :
    (fun x : ℝ => x ^ a) =O[atTop] fun x : ℝ => x ^ b := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact Real.rpow_le_rpow_of_exponent_le hx h

/-- **The two evaluations bound the signal**: `f(Z) ≪ Z^{7/15 - 1/20000}`. -/
theorem isBigO_of_hasTwoEvaluations {f : ℝ → ℂ} (h : HasTwoEvaluations f) :
    f =O[atTop] fun Z : ℝ => Z ^ ((7 / 15 : ℝ) - 1 / 20000) := by
  obtain ⟨I, c₀, hc₀, hI, hdiff⟩ := h
  -- take `ε = 1/10⁵`: `933/2000 + 1/10⁵ ≤ 7/15 - 1/20000`
  have hI' : I =O[atTop] fun Z : ℝ => Z ^ ((7 / 15 : ℝ) - 1 / 20000) :=
    (hI (1 / 100000) (by norm_num)).trans (rpow_isBigO_rpow_atTop (by norm_num))
  have hdiff' : (fun Z => I Z - c₀ * f Z) =O[atTop]
      fun Z : ℝ => Z ^ ((7 / 15 : ℝ) - 1 / 20000) :=
    hdiff.trans (rpow_isBigO_rpow_atTop (by norm_num))
  have hcf : (fun Z => c₀ * f Z) =O[atTop] fun Z : ℝ => Z ^ ((7 / 15 : ℝ) - 1 / 20000) := by
    have := hI'.sub hdiff'
    simpa only [sub_sub_cancel] using this
  have hf : f = fun Z => c₀⁻¹ * (c₀ * f Z) := by
    funext Z
    rw [← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
  rw [hf]
  exact hcf.const_mul_left c₀⁻¹

/-- The growth exponent of a Mellin signal of width `1/20000`. -/
theorem signal_exponent_eq :
    (1 - 1 / 20000 + (-8 / 15 : ℝ)) = (7 / 15 : ℝ) - 1 / 20000 := by
  norm_num

/-! ### From the two evaluations to the zero-free strip -/

/-- A Mellin signal of width `κ` is one of every smaller width. -/
theorem HasMellinSignal.mono {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}
    {χ : RayClassCharacter 𝔪} {κ κ' : ℝ} (h : HasMellinSignal χ κ) (hκ : κ' ≤ κ) :
    HasMellinSignal χ κ' := by
  obtain ⟨H, f, hH, hH0, hloc, hzero, htop, hid⟩ := h
  refine ⟨H, f, hH.mono fun s hs => ?_, fun s hs => hH0 s ?_, hloc, hzero,
    htop.trans (rpow_isBigO_rpow_atTop (by linarith)), hid⟩
  · have hs' : 1 - κ' < s.re := hs
    show 1 - κ < s.re
    linarith
  · linarith

variable {K : Type*} [Field K] [NumberField K]

/-- **The two evaluations give a Mellin signal of width `1/20000`.** -/
theorem hasMellinSignal_of_hasTwoEvaluations {𝔪 : Modulus K} {χ : RayClassCharacter 𝔪}
    {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H {s : ℂ | 1 - 1 / 20000 < s.re})
    (hH0 : ∀ s : ℂ, 1 - 1 / 20000 < s.re → H s ≠ 0)
    (hHb : ∃ C, ∀ s : ℂ, 2 ≤ s.re → ‖H s‖ ≤ C)
    (h : HasTwoEvaluations (gaussianSignal χ H)) : HasMellinSignal χ (1 / 20000) := by
  refine hasMellinSignal_of_isBigO (by norm_num) (by norm_num) hH hH0 hHb ?_
  rw [signal_exponent_eq]
  exact isBigO_of_hasTwoEvaluations h

/-- **[A] §§3–6 for one ray class character**: a multiplier `H`, holomorphic and nowhere zero on
`Re s > 1 - 1/20000` and bounded on `Re s ≥ 2`, for whose signal
`f(Z) = (1/2πi) ∫_{(2)} Z^{s-8/15} e^{(s-5/6)²} H(s)/L(s,χ) ds` [A]'s two evaluations hold. -/
def HasHeckeTwoEvaluations {𝔪 : Modulus K} (χ : RayClassCharacter 𝔪) : Prop :=
  ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | 1 - 1 / 20000 < s.re} ∧
    (∀ s : ℂ, 1 - 1 / 20000 < s.re → H s ≠ 0) ∧ (∃ C, ∀ s : ℂ, 2 ≤ s.re → ‖H s‖ ≤ C) ∧
    HasTwoEvaluations (gaussianSignal χ H)

/-- **[A] §§3–6**: the two evaluations for every ray class character of every cyclotomic field
`F ⊇ μ₁₂`. -/
def HeckeTwoEvaluations : Prop :=
  ∀ (m : ℕ) [NeZero m], 12 ∣ m →
    ∀ (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F],
      ∀ (𝔪 : Modulus F) (χ : RayClassCharacter 𝔪), HasHeckeTwoEvaluations χ

/-- **[A]'s two evaluations give the Hecke zero-free strip** of every width
`0 < δ ≤ 1/20000`, in particular `δ = 10⁻⁶`. -/
theorem heckeZeroFreeStrip_of_heckeTwoEvaluations {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 20000)
    (h : HeckeTwoEvaluations) : HeckeZeroFreeStrip δ :=
  heckeZeroFreeStrip_of_heckeMellinSignal hδ fun m _ h12 F _ _ _ 𝔪 χ => by
    obtain ⟨H, hH, hH0, hHb, h2⟩ := h m h12 F 𝔪 χ
    exact (hasMellinSignal_of_hasTwoEvaluations hH hH0 hHb h2).mono hδ1

end

end SimultaneousPrimitiveRoots.Unconditional
