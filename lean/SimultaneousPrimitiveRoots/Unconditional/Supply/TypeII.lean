module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Basic

/-!
# The one-sided marked Type II estimate ([P] Theorem 3.1) in coefficient form

[P] Theorem 3.1 (`[P-03:0037–0058]`) bounds `∑_{m,n} α_m β_n F(mn-1) 𝒲(mn-1)` for the
prime-minus-rough coefficient `α_m = m^{iv}(1_{m prime} - 1_{m rough} / (V(W) log m))`. For a fixed
residue class the invariance `F(ph) = F(h)` cannot carry the class, and the public paper moves
the class to the coefficients by characters (`[PUB-tex:0503–0516]`); this needs the estimate for
general scalar coefficients. That form is [A]'s coefficient criterion
`lem:marked-coefficient-transfer`
(`[A-08:0099–0123]`): the conclusion of Theorem 3.1 holds for every rough-supported coefficient
`α` that has cancellation against every character of logarithmic modulus, on the frequency range
`|t| ≤ 2 X L^B`. The only input about the prime-minus-rough coefficient is [P] Lemma 5.2
(`[P-05:0044–0055]`), which is that cancellation.

* `MarkedTypeIICoefficientForm`: `[A-08:0099–0123]`, the form used by the reduction.
* `MarkedTypeIICoefficientFormPointwise`: the stronger "one test" form proposed in
  `docs/s-side-map.md` §4.2, which the proof also gives; it implies the form of [A]
  (`markedTypeIICoefficientForm_of_pointwise`).
* `PrimeMinusRoughLongCoefficient`: [P] Lemma 5.2.
* `MarkedTypeII`: [P] Theorem 3.1 as stated.

All four are propositions (`def … : Prop`); none is proved here.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply

open Filter Asymptotics
open scoped Topology ContDiff

noncomputable section

/-! ### Objects -/

/-- The integers of the dyad `[H, 2H]` (`[P-03:0041–0042, 0048]`). -/
def dyad (H : ℝ) : Finset ℕ := Finset.Icc ⌈H⌉₊ ⌊2 * H⌋₊

theorem mem_dyad {H : ℝ} (hH : 0 ≤ H) {m : ℕ} :
    m ∈ dyad H ↔ H ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H := by
  unfold dyad
  rw [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (mul_nonneg zero_le_two hH)]

/-- The scales of Theorem 3.1: `H_m, H_n ≥ x^δ` and `X = H_m H_n ≍ x` with comparison constant
`κ` (`[P-03:0038–0039]`; the comparison constants are fixed, `[A-08:0102–0103]`). -/
structure TypeIIScales (δ κ x Hm Hn : ℝ) : Prop where
  /-- `H_m ≥ x^δ` -/
  le_left : x ^ δ ≤ Hm
  /-- `H_n ≥ x^δ` -/
  le_right : x ^ δ ≤ Hn
  /-- `x / κ ≤ H_m H_n` -/
  lower : x / κ ≤ Hm * Hn
  /-- `H_m H_n ≤ κ x` -/
  upper : Hm * Hn ≤ κ * x

/-- A scalar coefficient supported on `W`-rough integers of the dyad `[H, 2H]`, of modulus at
most `L^C` (`[A-08:0104–0108]`, `[P-03:0048–0049]`). A coefficient supported on a subinterval
`I ⊆ [H, 2H]` is a special case. -/
structure RoughDyadCoefficient (x C H : ℝ) (α : ℕ → ℂ) : Prop where
  /-- supported on rough integers in `[H, 2H]` -/
  support : ∀ m, α m ≠ 0 → H ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H ∧ IsRough (roughCutoff x) m
  /-- `|α_m| ≤ L^C` -/
  bound : ∀ m, ‖α m‖ ≤ Real.log x ^ C

/-- `F(ph) = F(h)` for every prime `p` of the bands and every positive `h`, including `p ∣ h`
(`[P-03:0040–0041]`, `[A-08:0036–0041, 0087–0088]`). -/
def BandInvariant {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (F : ℕ → ℂ) : Prop :=
  ∀ i, ∀ p ∈ bandPrimes (𝔞.exponent i) x, ∀ h : ℕ, 0 < h → F (p * h) = F h

/-- The marked bilinear sum `∑_{m,n} α_m β_n F(mn-1) 𝒲(mn-1)` over the dyads `m ∈ [H_m, 2H_m]`,
`n ∈ [H_n, 2H_n]` (`[P-03:0051–0054]` (eq:type-II), `[A-08:0078–0081]`). The coefficients of the
statements vanish outside the dyads. -/
def markedBilinearSum (q : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x Hm Hn : ℝ) (α β : ℕ → ℂ)
    (F : ℕ → ℂ) : ℂ :=
  ∑ m ∈ dyad Hm, ∑ n ∈ dyad Hn,
    α m * β n * F (m * n - 1) * ((markedWeight q 𝔞 x (m * n - 1) : ℝ) : ℂ)

/-- `∑_m α_m χ(m) m^{it}` over the dyad `[H_m, 2H_m]`; characters are zero on nonunits
(`[A-08:0021–0022]`, `[P-05:0042]`), as in Mathlib. -/
def twistedSum (Hm : ℝ) (α : ℕ → ℂ) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  ∑ m ∈ dyad Hm, α m * χ (m : ZMod k) * (m : ℂ) ^ ((t : ℂ) * Complex.I)

/-- The coefficient test (eq:type-ii-long-coefficient-interface) (`[A-08:0109–0113]`) =
(maj:M-uniform) (`[P-05:0045–0053]`) for one coefficient `α` at one `x`, with the constant `M`
explicit: for every character `χ` modulo `k ≤ L^{A₀}` and every `|t| ≤ 2 X L^B`,
`|H_m^{-1} ∑_m α_m χ(m) m^{it}| ≤ M L^{-A}`, where `X = H_m H_n`. -/
def LongCoefficientBound (x Hm Hn A₀ B A M : ℝ) (α : ℕ → ℂ) : Prop :=
  ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k, ∀ t : ℝ,
    |t| ≤ 2 * (Hm * Hn) * Real.log x ^ B →
      ‖twistedSum Hm α χ t‖ ≤ M * Hm * Real.log x ^ (-A)

/-- **The hypothesis of [A]'s coefficient criterion** (`[A-08:0108–0117]`) for a family of
coefficients: `𝒜 x Hm Hn` is the set of permitted coefficients at `x` and at the scales
`(H_m, H_n)` (the interval of support and any further fixed parameters that define the
coefficients are absorbed into the family). For every fixed `A₀, B, A > 0` the coefficient test
holds for all large `x`, uniformly in the family, the character and the frequency; the constant
`M` and the threshold `x₀` may depend on `A₀, B, A` and on the family. -/
def PassesCoefficientTest (δ κ : ℝ) (𝒜 : ℝ → ℝ → ℝ → Set (ℕ → ℂ)) : Prop :=
  ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A → ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ,
    TypeIIScales δ κ x Hm Hn → ∀ α ∈ 𝒜 x Hm Hn, LongCoefficientBound x Hm Hn A₀ B A M α

/-! ### The statements -/

/-- **[P] Theorem 3.1 in coefficient form** = [A] `lem:marked-coefficient-transfer`
(`[A-08:0099–0123]`).

Fix `δ, C, D_* > 0`, `q ∈ (0,1)` and the comparison constant `κ` of `X = H_m H_n ≍ x`. If `K` is
sufficiently large in terms of these, then for every marking array with `K` bands and every family
of coefficients that passes the coefficient test,
`|∑_{m,n} α_m β_n F(mn-1) 𝒲(mn-1)| ≪ X L^{-D_*}`, uniformly in `|F| ≤ 1` invariant under the
band primes, in `α` of the family and in `β`, both supported on rough integers of their dyads and
bounded by `L^C`.

Dependence of constants (`[A-08:0119–0122, 0236–0250]`, `[P-03:0055–0057]`, `[P-05:0446–0456]`):
* `K₀` depends only on `δ, C, D_*, q, κ`: it is chosen (through `D_1 → E_0 → A_0 → K`) before the
  band exponents and independently of the coefficient family, so it is quantified before `𝔞` and
  `𝒜`. The text asks for `K` large in terms of the fixed data; the proof supports the stronger
  reading used here, in which the family may even depend on `K` and `𝔞`.
* the implied constant `M` and the threshold `x₀` may depend on everything fixed, including the
  band exponents and the family.

`κ` is part of the fixed data (the papers write `X ≍ x`), so `K₀` is allowed to depend on it. -/
def MarkedTypeIICoefficientForm : Prop :=
  ∀ δ C Dstar q κ : ℝ, 0 < δ → 0 < C → 0 < Dstar → 0 < q → q < 1 → 1 ≤ κ →
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ 𝔞 : MarkingArray K,
      ∀ 𝒜 : ℝ → ℝ → ℝ → Set (ℕ → ℂ), PassesCoefficientTest δ κ 𝒜 →
        ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ, TypeIIScales δ κ x Hm Hn →
          ∀ F : ℕ → ℂ, (∀ h, ‖F h‖ ≤ 1) → BandInvariant 𝔞 x F →
            ∀ α ∈ 𝒜 x Hm Hn, RoughDyadCoefficient x C Hm α →
              ∀ β : ℕ → ℂ, RoughDyadCoefficient x C Hn β →
                ‖markedBilinearSum q 𝔞 x Hm Hn α β F‖ ≤
                  M * (Hm * Hn) * Real.log x ^ (-Dstar)

/-- **The "one test" form of the coefficient criterion** (the proposal `markedTypeII_coeff` of
`docs/s-side-map.md` §4.2). There are exponents `A₀, B, A`, depending only on `δ, C, D_*, q, κ`,
such that the bound of Theorem 3.1 holds at `x` for every coefficient `α` that satisfies the
coefficient test with these three exponents and constant `1` at this `x`.

This is what the proof uses: `A_0` is fixed before `K` and the major-term accuracies `B, A` are
chosen after `A_0`, independently of `K` (`[P-05:0350, 0417–0432, 0446–0456]`,
`[A-08:0210–0244]`); it is not stated in this form in the papers. It implies
`MarkedTypeIICoefficientForm` (`markedTypeIICoefficientForm_of_pointwise`). -/
def MarkedTypeIICoefficientFormPointwise : Prop :=
  ∀ δ C Dstar q κ : ℝ, 0 < δ → 0 < C → 0 < Dstar → 0 < q → q < 1 → 1 ≤ κ →
    ∃ A₀ B A : ℝ, 0 < A₀ ∧ 0 < B ∧ 0 < A ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ 𝔞 : MarkingArray K,
      ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ, TypeIIScales δ κ x Hm Hn →
        ∀ F : ℕ → ℂ, (∀ h, ‖F h‖ ≤ 1) → BandInvariant 𝔞 x F →
          ∀ α : ℕ → ℂ, RoughDyadCoefficient x C Hm α → LongCoefficientBound x Hm Hn A₀ B A 1 α →
            ∀ β : ℕ → ℂ, RoughDyadCoefficient x C Hn β →
              ‖markedBilinearSum q 𝔞 x Hm Hn α β F‖ ≤ M * (Hm * Hn) * Real.log x ^ (-Dstar)

/-- The prime-minus-rough coefficient of [P] Theorem 3.1 (`[P-03:0041–0047]`):
`α_m = m^{iv} (1_{m prime} - 1_{m rough} / (V(W) log m))` on the interval `[lo, hi]`, and `0`
outside it. Intervals with open ends give the same coefficients (`m` is an integer). -/
def primeMinusRough (x v lo hi : ℝ) (m : ℕ) : ℂ :=
  open _root_.Classical in
  if lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi then
    (m : ℂ) ^ ((v : ℂ) * Complex.I) *
      ((if m.Prime then 1 else 0) -
        (if IsRough (roughCutoff x) m then 1 else 0) /
          ((mertensProduct (roughCutoff x) * Real.log m : ℝ) : ℂ))
  else 0

/-- **[P] Lemma 5.2** `maj:long-coefficient` (`[P-05:0044–0055]`): fix `A_0, B, A > 0`; for the
coefficient of Theorem 3.1 (fixed `δ, C`, comparison constant `κ`), every character `χ` of modulus
at most `L^{A_0}` and every `|t| ≤ 2 X L^B`, `|H_m^{-1} ∑_m α_m χ(m) m^{it}| ≪_A L^{-A}`, uniformly
in the coefficient interval and in `|v| ≤ L^C` (`[P-05:0028–0029]`). Principal and imprimitive
characters are included. (The conjugated form of `[P-05:0054]` follows by conjugation.)

In the fixed-class argument the lemma is used for `λ χ` with `λ` a character modulo the fixed
`H`: its modulus is `lcm(H, k) ≤ L^{A_0 + 1}`, so the lemma is applied with `A_0 + 1`
(`[PUB-tex:0509–0514]`). -/
def PrimeMinusRoughLongCoefficient : Prop :=
  ∀ δ C κ : ℝ, 0 < δ → 0 < C → 1 ≤ κ → ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
    ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ, TypeIIScales δ κ x Hm Hn →
      ∀ v : ℝ, |v| ≤ Real.log x ^ C → ∀ lo hi : ℝ, Hm ≤ lo → hi ≤ 2 * Hm →
        LongCoefficientBound x Hm Hn A₀ B A M (primeMinusRough x v lo hi)

/-- **[P] Theorem 3.1** `thm:type-II` (`[P-03:0037–0058]`), as stated: the bound for the
prime-minus-rough coefficient on an arbitrary interval of `[H_m, 2H_m]`. `K₀` depends on
`δ, C, D_*, q` (and `κ`), not on the band exponents; `M` and `x₀` may depend on all fixed
parameters, including the band exponents. -/
def MarkedTypeII : Prop :=
  ∀ δ C Dstar q κ : ℝ, 0 < δ → 0 < C → 0 < Dstar → 0 < q → q < 1 → 1 ≤ κ →
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ 𝔞 : MarkingArray K,
      ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ, TypeIIScales δ κ x Hm Hn →
        ∀ F : ℕ → ℂ, (∀ h, ‖F h‖ ≤ 1) → BandInvariant 𝔞 x F →
          ∀ v : ℝ, |v| ≤ Real.log x ^ C → ∀ lo hi : ℝ, Hm ≤ lo → hi ≤ 2 * Hm →
            ∀ β : ℕ → ℂ, RoughDyadCoefficient x C Hn β →
              ‖markedBilinearSum q 𝔞 x Hm Hn (primeMinusRough x v lo hi) β F‖ ≤
                M * (Hm * Hn) * Real.log x ^ (-Dstar)

/-! ### Sanity checks -/

/-- The family of prime-minus-rough coefficients of Theorem 3.1 with `|v| ≤ L^C`. -/
def primeMinusRoughFamily (C : ℝ) : ℝ → ℝ → ℝ → Set (ℕ → ℂ) := fun x Hm _ =>
  {α | ∃ v lo hi : ℝ, |v| ≤ Real.log x ^ C ∧ Hm ≤ lo ∧ hi ≤ 2 * Hm ∧
    α = primeMinusRough x v lo hi}

/-- [P] Lemma 5.2 says exactly that the prime-minus-rough family passes the coefficient test of
[A]'s coefficient criterion. -/
theorem primeMinusRoughLongCoefficient_iff :
    PrimeMinusRoughLongCoefficient ↔
      ∀ δ C κ : ℝ, 0 < δ → 0 < C → 1 ≤ κ → PassesCoefficientTest δ κ (primeMinusRoughFamily C) := by
  constructor
  · intro h δ C κ hδ hC hκ A₀ B A hA₀ hB hA
    obtain ⟨M, x₀, hM⟩ := h δ C κ hδ hC hκ A₀ B A hA₀ hB hA
    refine ⟨M, x₀, fun x hx Hm Hn hs α hα => ?_⟩
    obtain ⟨v, lo, hi, hv, hlo, hhi, rfl⟩ := hα
    exact hM x hx Hm Hn hs v hv lo hi hlo hhi
  · intro h δ C κ hδ hC hκ A₀ B A hA₀ hB hA
    obtain ⟨M, x₀, hM⟩ := h δ C κ hδ hC hκ A₀ B A hA₀ hB hA
    refine ⟨M, x₀, fun x hx Hm Hn hs v hv lo hi hlo hhi => ?_⟩
    have hmem : primeMinusRough x v lo hi ∈ primeMinusRoughFamily C x Hm Hn :=
      ⟨v, lo, hi, hv, hlo, hhi, rfl⟩
    exact hM x hx Hm Hn hs _ hmem

/-- **The "one test" form implies the form of [A]'s criterion.** A family that passes the
coefficient test for all `(A₀, B, A)` passes, for large `x`, the single test with constant `1`
(take the family's bound at `A + 1` and absorb its constant into one power of `L`). -/
theorem markedTypeIICoefficientForm_of_pointwise (h : MarkedTypeIICoefficientFormPointwise) :
    MarkedTypeIICoefficientForm := by
  intro δ C Dstar q κ hδ hC hD hq hq1 hκ
  obtain ⟨A₀, B, A, hA₀, hB, hA, K₀, hK₀⟩ := h δ C Dstar q κ hδ hC hD hq hq1 hκ
  refine ⟨K₀, fun K hK 𝔞 𝒜 h𝒜 => ?_⟩
  obtain ⟨M, x₁, hM⟩ := hK₀ K hK 𝔞
  obtain ⟨M₂, x₂, hM₂⟩ := h𝒜 A₀ B (A + 1) hA₀ hB (by linarith)
  refine ⟨M, max x₁ (max x₂ (Real.exp (max M₂ 1))),
    fun x hx Hm Hn hs F hF hFinv α hα hαr β hβ => ?_⟩
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans hx
  have hx₂ : x₂ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxe : Real.exp (max M₂ 1) ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hxe
  have hlog : max M₂ 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hxe
    rwa [Real.log_exp] at this
  have hL1 : 1 ≤ Real.log x := (le_max_right _ _).trans hlog
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hM₂L : M₂ ≤ Real.log x := (le_max_left _ _).trans hlog
  have hHm : 0 ≤ Hm := (Real.rpow_nonneg hx0.le δ).trans hs.le_left
  refine hM x hx₁ Hm Hn hs F hF hFinv α hαr ?_ β hβ
  intro k hk hkL χ t ht
  have h1 := hM₂ x hx₂ Hm Hn hs α hα k hk hkL χ t ht
  have hpow : Real.log x ^ (-(A + 1)) = Real.log x ^ (-A) * (Real.log x)⁻¹ := by
    rw [show -(A + 1) = -A + (-1) by ring, Real.rpow_add hL0, Real.rpow_neg_one]
  have hLA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL0.le _
  have h2 : M₂ * (Real.log x)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hL0]
    exact hM₂L
  calc ‖twistedSum Hm α χ t‖ ≤ M₂ * Hm * Real.log x ^ (-(A + 1)) := h1
    _ = (M₂ * (Real.log x)⁻¹) * (Hm * Real.log x ^ (-A)) := by rw [hpow]; ring
    _ ≤ 1 * (Hm * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hHm hLA)
    _ = 1 * Hm * Real.log x ^ (-A) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply
