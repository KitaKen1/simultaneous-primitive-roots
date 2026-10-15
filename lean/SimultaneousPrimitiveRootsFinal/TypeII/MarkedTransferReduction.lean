import ArtinPrimitiveRoots.TypeII.Marked
import SimultaneousPrimitiveRoots.Unconditional.Supply.TypeII

/-!
# The marked Type II estimate in coefficient form, from the vendored formalization of [A]

`Supply.MarkedTypeIICoefficientForm` (`Supply/TypeII.lean`) is [A] `lem:marked-coefficient-transfer`
(`[A-08:0099–0251]`). The vendored formalization of [A] proves it as
`ArtinPrimitiveRoots.TypeII.marked_coefficient_transfer`
(`vendor/ArtinPrimitiveRoots/TypeII/MarkedTransfer.lean`). That file is at the end of a long import
chain, so this file does not import it: it imports only the *interface* of the vendored theorem
(`vendor/ArtinPrimitiveRoots/TypeII/Marked.lean`), states the vendored theorem as the proposition
`VendoredMarkedCoefficientTransfer`, and proves

`markedTypeIICoefficientForm_of_vendored :
  VendoredMarkedCoefficientTransfer → Supply.MarkedTypeIICoefficientForm`.

`TypeII/MarkedTransferBridge.lean` discharges the hypothesis.

## The two statements

The vendored theorem is about one `CoefficientFamily`: for every `x` one choice of the scales
`Hm x`, `Hn x`, of an interval and of a coefficient `alpha x`, and its constants `C', x₀` depend on
the family. The statement of the project asks for constants that are uniform in all scales with
`TypeIIScales δ κ x Hm Hn` and all coefficients of a set-valued family `𝒜 x Hm Hn` that passes the
coefficient test. The passage is a selection argument (`exists_selection`): at each `x` choose
scales and a coefficient that violate the bound with the largest possible constant `n ≤ x` (the
zero coefficient at the scales `(√x, √x)` if there is no violation at all). The selected family is
a `CoefficientFamily` with the long coefficient cancellation, because the coefficient test is
uniform in the scales and in the family; the vendored bound for it, with constant `C'`, then
holds for *every* admissible choice at every `x ≥ max x₀ ⌈C'⌉`, with the constant `⌈C'⌉`.

If `δ > 1/2` there are no scales for large `x` and the statement is empty (`not_typeIIScales`);
for `δ ≤ 1/2` the scales `(√x, √x)` exist (`typeIIScales_sqrt`).

## The dictionary (all exact)

* `roughCutoff`: `exp (L ^ (24/100))` and `exp (L ^ 0.24)` (`roughCutoff_eq`);
  `roughAbove n W` is `Supply.IsRough W n` by definition.
* bands: `primeBand x a = Supply.bandPrimes a x` (`primeBand_eq`), hence `bandMass`, `bandOmega`
  are `Supply.reciprocalMass`, `Supply.primeHits` of the band, and the two marked weights agree at
  every integer (`markedWeight_eq`).
* `ValidBands K 𝔞.exponent` for a `Supply.MarkingArray K` with `0 < K` (`validBands`); `K₀` is
  enlarged to `max K₀ 1`.
* `IsMarkedInvariant` follows from `|F| ≤ 1` and `Supply.BandInvariant` (`isMarkedInvariant`): the
  vendored invariance also asks for `F (p * 0) = F 0`, which is trivial.
* dyads: `dyadicIntegers H = Supply.dyad H` for `H ≥ 0` (`dyadicIntegers_eq_dyad`); the interval of
  the family is the whole dyad (`dyadSet`).
* the two `markedBilinearSum`s agree (`markedBilinearSum_eq`).
* `m ^ (t * I) = exp (I * t * log m)` for `m ≠ 0` (`natCast_cpow_mul_I`), so the vendored long
  coefficient sum is `Supply.twistedSum` (`familyOf_sum_eq`); the vendored test divides by `H_m`.
* scale constants: `c₁ = κ⁻¹ ≤ c₂ = κ`.
-/

namespace SimultaneousPrimitiveRoots.Unconditional

open ArtinPrimitiveRoots.TypeII in
/-- **The statement of the vendored theorem**
`ArtinPrimitiveRoots.TypeII.marked_coefficient_transfer`
(`vendor/ArtinPrimitiveRoots/TypeII/MarkedTransfer.lean`), copied with the same binders in the same
order (the eight hypotheses `hδ, hC, hD, hqd₀, hqd₁, hc₁, hc₂, hc₁₂` are written as arrows). It is
discharged in `TypeII/MarkedTransferBridge.lean`. -/
def VendoredMarkedCoefficientTransfer : Prop :=
  ∀ (δ C Dstar q_d c₁ c₂ : ℝ),
    0 < δ → 0 < C → 0 < Dstar →
    0 < q_d → q_d < 1 →
    0 < c₁ → 0 < c₂ → c₁ ≤ c₂ →
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ family : CoefficientFamily δ C c₁ c₂,
        HasLongCoefficientCancellation family →
        ∀ a : Fin K → ℝ, ValidBands K a →
      ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ β : ℕ → ℂ,
            (∀ n, β n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧
              roughAbove n (roughCutoff x)) →
            (∀ n ∈ dyadicIntegers (family.Hn x),
              ‖β n‖ ≤ Real.rpow (Real.log x) C) →
            ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
              ‖markedBilinearSum x K a q_d F (family.Hm x) (family.Hn x)
                (family.interval x) (family.alpha x) β‖ ≤
                  C' * (family.Hm x * family.Hn x) *
          Real.rpow (Real.log x) (-Dstar)

namespace Supply.MarkedBridge

/-! ### The dictionary between the vendored definitions and those of `Supply` -/

/-- The two rough cutoffs `W = exp (L ^ 0.24)`. -/
theorem roughCutoff_eq (x : ℝ) :
    ArtinPrimitiveRoots.TypeII.roughCutoff x = Supply.roughCutoff x := by
  have h : (24 / 100 : ℝ) = 0.24 := by norm_num
  unfold ArtinPrimitiveRoots.TypeII.roughCutoff Supply.roughCutoff
  rw [Real.rpow_eq_pow, h]

/-- The two notions of roughness are the same proposition. -/
theorem roughAbove_iff (n : ℕ) (W : ℝ) :
    ArtinPrimitiveRoots.TypeII.roughAbove n W ↔ Supply.IsRough W n := Iff.rfl

/-- The two bands of primes `exp (L^a) ≤ p ≤ exp (2 L^a)`. -/
theorem primeBand_eq (x a : ℝ) :
    ArtinPrimitiveRoots.TypeII.primeBand x a = Supply.bandPrimes a x := by
  ext p
  rw [Supply.mem_bandPrimes]
  unfold ArtinPrimitiveRoots.TypeII.primeBand
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  simp only [Real.rpow_eq_pow]
  exact ⟨fun h => h.2, fun h => ⟨Nat.le_floor h.2.2, h⟩⟩

/-- The reciprocal mass of a band, in the two notations. -/
theorem bandMass_eq (x a : ℝ) :
    ArtinPrimitiveRoots.TypeII.bandMass x a = Supply.reciprocalMass (Supply.bandPrimes a x) := by
  unfold ArtinPrimitiveRoots.TypeII.bandMass Supply.reciprocalMass
  rw [primeBand_eq]

/-- The number of prime divisors of `h` in a band, in the two notations. -/
theorem bandOmega_eq (x a : ℝ) (h : ℕ) :
    ArtinPrimitiveRoots.TypeII.bandOmega x a h = Supply.primeHits (Supply.bandPrimes a x) h := by
  unfold ArtinPrimitiveRoots.TypeII.bandOmega Supply.primeHits
  refine congrArg Finset.card ?_
  ext p
  simp only [Finset.mem_filter, primeBand_eq]

/-- **The two marked weights agree** at every integer: `q^{ω(h) - K} ∏_i ω_i(h) / V_i` if every
band has a divisor of `h` and `0` otherwise, against `∏_i q^{ω_i(h) - 1} ω_i(h) / V_i`. -/
theorem markedWeight_eq (q : ℝ) {K : ℕ} (𝔞 : Supply.MarkingArray K) (x : ℝ) (h : ℕ) :
    ArtinPrimitiveRoots.TypeII.markedWeight x K 𝔞.exponent q h = Supply.markedWeight q 𝔞 x h := by
  unfold ArtinPrimitiveRoots.TypeII.markedWeight
  split_ifs with hall
  · have hpos : ∀ i, 1 ≤ Supply.primeHits (Supply.bandPrimes (𝔞.exponent i) x) h := by
      intro i
      obtain ⟨p, hp, hdvd⟩ := hall i
      rw [primeBand_eq] at hp
      exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hdvd⟩⟩
    rw [Supply.markedWeight_eq_of_pos q 𝔞 x h hpos]
    unfold ArtinPrimitiveRoots.TypeII.markedOmega
    simp only [bandOmega_eq, bandMass_eq]
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    refine (Supply.markedWeight_eq_zero (i := i) ?_).symm
    unfold Supply.primeHits
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp
    rw [← primeBand_eq] at hp
    exact hi p hp

/-- A marking array with at least one band satisfies the vendored conditions on the exponents. -/
theorem validBands {K : ℕ} (hK : 0 < K) (𝔞 : Supply.MarkingArray K) :
    ArtinPrimitiveRoots.TypeII.ValidBands K 𝔞.exponent :=
  ⟨hK, fun i => ⟨𝔞.gt_tenth i, 𝔞.lt_fifth i⟩, fun _ _ hij => 𝔞.strictMono (Fin.lt_def.mpr hij)⟩

/-- `|F| ≤ 1` and the invariance of the project give the vendored invariance (which also asks for
`F (p * 0) = F 0`). -/
theorem isMarkedInvariant {K : ℕ} (𝔞 : Supply.MarkingArray K) (x : ℝ) {F : ℕ → ℂ}
    (hF : ∀ h, ‖F h‖ ≤ 1) (hinv : Supply.BandInvariant 𝔞 x F) :
    ArtinPrimitiveRoots.TypeII.IsMarkedInvariant x K 𝔞.exponent F := by
  refine ⟨hF, fun p h hp _ => ?_⟩
  unfold ArtinPrimitiveRoots.TypeII.markedPrimes at hp
  obtain ⟨i, -, hpi⟩ := Finset.mem_biUnion.mp hp
  rw [primeBand_eq] at hpi
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · rw [Nat.mul_zero]
  · exact hinv i p hpi h hh

/-- Membership in the vendored dyad (no condition on the sign of `H`). -/
theorem mem_dyadicIntegers {H : ℝ} {n : ℕ} :
    n ∈ ArtinPrimitiveRoots.TypeII.dyadicIntegers H ↔ H ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * H := by
  unfold ArtinPrimitiveRoots.TypeII.dyadicIntegers
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  exact ⟨fun h => h.2, fun h => ⟨Nat.le_floor h.2, h⟩⟩

/-- The two dyads agree for `H ≥ 0`. (For `H < 0` the vendored one is empty and `Supply.dyad H`
is `{0}`.) -/
theorem dyadicIntegers_eq_dyad {H : ℝ} (hH : 0 ≤ H) :
    ArtinPrimitiveRoots.TypeII.dyadicIntegers H = Supply.dyad H := by
  ext n
  rw [mem_dyadicIntegers, Supply.mem_dyad hH]

/-- The whole dyad `[H, 2H]` as a set of natural numbers: the interval of the selected family. -/
def dyadSet (H : ℝ) : Set ℕ := {m : ℕ | H ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H}

theorem mem_dyadSet {H : ℝ} {m : ℕ} : m ∈ dyadSet H ↔ H ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H := Iff.rfl

theorem isNatInterval_dyadSet (H : ℝ) : ArtinPrimitiveRoots.TypeII.IsNatInterval (dyadSet H) := by
  intro m n k hm hn hmin hmax
  rw [mem_dyadSet] at hm hn ⊢
  constructor
  · have h : H ≤ ((min m n : ℕ) : ℝ) := by
      rcases min_choice m n with h | h <;> rw [h]
      · exact hm.1
      · exact hn.1
    exact h.trans (by exact_mod_cast hmin)
  · have h : ((max m n : ℕ) : ℝ) ≤ 2 * H := by
      rcases max_choice m n with h | h <;> rw [h]
      · exact hm.2
      · exact hn.2
    exact (show (k : ℝ) ≤ ((max m n : ℕ) : ℝ) by exact_mod_cast hmax).trans h

open _root_.Classical in
/-- The index set of the vendored sums for the interval `dyadSet H` is the dyad of the project. -/
theorem filter_dyadSet_eq_dyad {H : ℝ} (hH : 0 ≤ H) :
    (ArtinPrimitiveRoots.TypeII.dyadicIntegers H).filter (fun m => m ∈ dyadSet H) =
      Supply.dyad H := by
  ext m
  rw [Finset.mem_filter, mem_dyadicIntegers, mem_dyadSet, Supply.mem_dyad hH]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- **The two marked bilinear sums agree**, for the interval `dyadSet Hm` and nonnegative
scales. -/
theorem markedBilinearSum_eq (q : ℝ) {K : ℕ} (𝔞 : Supply.MarkingArray K) (x : ℝ) {Hm Hn : ℝ}
    (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (α β F : ℕ → ℂ) :
    ArtinPrimitiveRoots.TypeII.markedBilinearSum x K 𝔞.exponent q F Hm Hn (dyadSet Hm) α β =
      Supply.markedBilinearSum q 𝔞 x Hm Hn α β F := by
  unfold ArtinPrimitiveRoots.TypeII.markedBilinearSum Supply.markedBilinearSum
  rw [filter_dyadSet_eq_dyad hHm, dyadicIntegers_eq_dyad hHn]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [markedWeight_eq]

/-- `m^{it} = exp (i t log m)` for a positive integer `m`. (At `m = 0` the left side is `0` for
`t ≠ 0` and the right side is `1`.) -/
theorem natCast_cpow_mul_I {m : ℕ} (hm : m ≠ 0) (t : ℝ) :
    (m : ℂ) ^ ((t : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hm), Complex.natCast_log]
  congr 1
  ring

/-! ### Scales -/

/-- For `δ ≤ 1/2` and `x ≥ 1` the scales `(√x, √x)` are admissible. -/
theorem typeIIScales_sqrt {δ κ x : ℝ} (hδ : δ ≤ 1 / 2) (hκ : 1 ≤ κ) (hx : 1 ≤ x) :
    Supply.TypeIIScales δ κ x (Real.sqrt x) (Real.sqrt x) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have h1 : x ^ δ ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx hδ
  refine ⟨h1, h1, ?_, ?_⟩
  · rw [Real.mul_self_sqrt hx0]
    exact div_le_self hx0 hκ
  · rw [Real.mul_self_sqrt hx0]
    exact le_mul_of_one_le_left hx0 hκ

/-- For `δ > 1/2` there are no scales at large `x`: `x^{2δ} ≤ H_m H_n ≤ κ x` fails. -/
theorem not_typeIIScales {δ κ : ℝ} (hδ : 1 / 2 < δ) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ, ¬ Supply.TypeIIScales δ κ x Hm Hn := by
  have hexp : 0 < 2 * δ - 1 := by linarith
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hexp).eventually_gt_atTop κ)
  refine ⟨max x₁ 1, fun x hx Hm Hn hs => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
  have hgt : κ < x ^ (2 * δ - 1) := hx₁ x ((le_max_left _ _).trans hx)
  have hpow : 0 ≤ x ^ δ := Real.rpow_nonneg hx0.le δ
  have hprod : x ^ δ * x ^ δ ≤ κ * x :=
    (mul_le_mul hs.le_left hs.le_right hpow (hpow.trans hs.le_left)).trans hs.upper
  have hsplit : x ^ δ * x ^ δ = x ^ (2 * δ - 1) * x := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']
    congr 1
    ring
  rw [hsplit] at hprod
  exact absurd (le_of_mul_le_mul_right hprod hx0) (not_le.mpr hgt)

/-! ### The selection -/

/-- A violation at `x` of the bound of `Supply.MarkedTypeIICoefficientForm` with the constant `M`,
at the scales `(Hm, Hn)` and for the first coefficient `α`: some admissible `F` and `β` give a
marked bilinear sum larger than `M X L^{-D_*}`. -/
def Violation (C Dstar q : ℝ) {K : ℕ} (𝔞 : Supply.MarkingArray K) (M x Hm Hn : ℝ)
    (α : ℕ → ℂ) : Prop :=
  ∃ F β : ℕ → ℂ, (∀ h, ‖F h‖ ≤ 1) ∧ Supply.BandInvariant 𝔞 x F ∧
    Supply.RoughDyadCoefficient x C Hn β ∧
      M * (Hm * Hn) * Real.log x ^ (-Dstar) < ‖Supply.markedBilinearSum q 𝔞 x Hm Hn α β F‖

/-- A violation with the constant `M` is a violation with every smaller constant. -/
theorem Violation.mono {C Dstar q : ℝ} {K : ℕ} {𝔞 : Supply.MarkingArray K} {M M' x Hm Hn : ℝ}
    {α : ℕ → ℂ} (h : Violation C Dstar q 𝔞 M x Hm Hn α) (hM : M' ≤ M) (hx : 1 ≤ x)
    (hH : 0 ≤ Hm * Hn) : Violation C Dstar q 𝔞 M' x Hm Hn α := by
  obtain ⟨F, β, hF, hinv, hβ, hlt⟩ := h
  refine ⟨F, β, hF, hinv, hβ, lt_of_le_of_lt ?_ hlt⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hH)
    (Real.rpow_nonneg (Real.log_nonneg hx) _)

/-- The zero coefficient is a rough dyadic coefficient, for `x ≥ 1`. -/
theorem roughDyadCoefficient_zero {x : ℝ} (hx : 1 ≤ x) (C H : ℝ) :
    Supply.RoughDyadCoefficient x C H (0 : ℕ → ℂ) where
  support := fun m hm => absurd rfl hm
  bound := fun m => by
    rw [Pi.zero_apply, norm_zero]
    exact Real.rpow_nonneg (Real.log_nonneg hx) C

/-- **The selection.** At a given `x ≥ 1` at which there are scales, there are scales `(Hm, Hn)`
and a coefficient `α`, which is `0` or a rough dyadic coefficient of the family, such that every
violation at `x` with a natural constant `n ≤ x`, at any scales and for any coefficient of the
family, is also a violation with the constant `n` at `(Hm, Hn)` for `α`. -/
theorem exists_selection (δ κ C Dstar q : ℝ) {K : ℕ} (𝔞 : Supply.MarkingArray K)
    (𝒜 : ℝ → ℝ → ℝ → Set (ℕ → ℂ)) {x : ℝ} (hx : 1 ≤ x)
    (hscales : ∃ Hm Hn : ℝ, Supply.TypeIIScales δ κ x Hm Hn) :
    ∃ Hm Hn : ℝ, ∃ α : ℕ → ℂ, Supply.TypeIIScales δ κ x Hm Hn ∧
      Supply.RoughDyadCoefficient x C Hm α ∧ (α = 0 ∨ α ∈ 𝒜 x Hm Hn) ∧
      ∀ n : ℕ, (n : ℝ) ≤ x → ∀ Hm' Hn' : ℝ, Supply.TypeIIScales δ κ x Hm' Hn' →
        ∀ α' ∈ 𝒜 x Hm' Hn', Supply.RoughDyadCoefficient x C Hm' α' →
          Violation C Dstar q 𝔞 n x Hm' Hn' α' → Violation C Dstar q 𝔞 n x Hm Hn α := by
  classical
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  -- the natural constants for which the bound is violated somewhere at `x`
  let P : ℕ → Prop := fun n => ∃ Hm Hn : ℝ, ∃ α : ℕ → ℂ, Supply.TypeIIScales δ κ x Hm Hn ∧
    α ∈ 𝒜 x Hm Hn ∧ Supply.RoughDyadCoefficient x C Hm α ∧ Violation C Dstar q 𝔞 n x Hm Hn α
  by_cases hP : ∃ n : ℕ, n ≤ ⌊x⌋₊ ∧ P n
  · obtain ⟨n₀, hn₀, hPn₀⟩ := hP
    obtain ⟨Hm, Hn, α, hs, hα, hαr, hviol⟩ := Nat.findGreatest_spec hn₀ hPn₀
    refine ⟨Hm, Hn, α, hs, hαr, Or.inr hα, fun n hn Hm' Hn' hs' α' hα' hαr' hviol' => ?_⟩
    have hnle : n ≤ Nat.findGreatest P ⌊x⌋₊ :=
      Nat.le_findGreatest (Nat.le_floor hn) ⟨Hm', Hn', α', hs', hα', hαr', hviol'⟩
    have hpow : 0 ≤ x ^ δ := Real.rpow_nonneg hx0 δ
    exact hviol.mono (by exact_mod_cast hnle) hx
      (mul_nonneg (hpow.trans hs.le_left) (hpow.trans hs.le_right))
  · obtain ⟨Hm, Hn, hs⟩ := hscales
    refine ⟨Hm, Hn, 0, hs, roughDyadCoefficient_zero hx C Hm, Or.inl rfl,
      fun n hn Hm' Hn' hs' α' hα' hαr' hviol' => ?_⟩
    exact absurd ⟨n, Nat.le_floor hn, Hm', Hn', α', hs', hα', hαr', hviol'⟩ hP

/-! ### The selected family in the vendored interface -/

/-- The coefficient family of the vendored interface with the scales `Hm x`, `Hn x`, the whole
dyad `[Hm x, 2 Hm x]` as interval and the coefficients `alpha x`, for `x ≥ 2`. -/
noncomputable def familyOf (δ C κ : ℝ) (Hm Hn : ℝ → ℝ) (alpha : ℝ → ℕ → ℂ)
    (hs : ∀ x, 2 ≤ x → Supply.TypeIIScales δ κ x (Hm x) (Hn x))
    (hr : ∀ x, 2 ≤ x → Supply.RoughDyadCoefficient x C (Hm x) (alpha x)) :
    ArtinPrimitiveRoots.TypeII.CoefficientFamily δ C κ⁻¹ κ where
  xMin := 2
  xMin_ge_two := le_rfl
  Hm := Hm
  Hn := Hn
  interval := fun x => dyadSet (Hm x)
  alpha := alpha
  interval_property := fun x => isNatInterval_dyadSet (Hm x)
  scales := fun x hx =>
    ⟨(hs x hx).le_left, (hs x hx).le_right, by
      rw [← div_eq_inv_mul]
      exact (hs x hx).lower, (hs x hx).upper⟩
  interval_bounds := fun _ _ _ hm => hm
  rough_support := fun x hx m hm =>
    ⟨⟨((hr x hx).support m hm).1, ((hr x hx).support m hm).2.1⟩, by
      rw [roughCutoff_eq]
      exact ((hr x hx).support m hm).2.2⟩
  coefficient_bound := fun x hx m _ => (hr x hx).bound m

/-- The terms of the selected family are the dyad of the project. -/
theorem familyTerms_familyOf {δ C κ : ℝ} {Hm Hn : ℝ → ℝ} {alpha : ℝ → ℕ → ℂ}
    (hs : ∀ x, 2 ≤ x → Supply.TypeIIScales δ κ x (Hm x) (Hn x))
    (hr : ∀ x, 2 ≤ x → Supply.RoughDyadCoefficient x C (Hm x) (alpha x)) {x : ℝ}
    (hHm : 0 ≤ Hm x) :
    ArtinPrimitiveRoots.TypeII.familyTerms (familyOf δ C κ Hm Hn alpha hs hr) x =
      Supply.dyad (Hm x) := by
  ext m
  unfold ArtinPrimitiveRoots.TypeII.familyTerms
  simp only [Finset.mem_filter]
  rw [mem_dyadicIntegers, Supply.mem_dyad hHm]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- The long coefficient sum of the selected family, in the vendored form, is
`Supply.twistedSum`, for `Hm x > 0`. -/
theorem familyOf_sum_eq {δ C κ : ℝ} {Hm Hn : ℝ → ℝ} {alpha : ℝ → ℕ → ℂ}
    (hs : ∀ x, 2 ≤ x → Supply.TypeIIScales δ κ x (Hm x) (Hn x))
    (hr : ∀ x, 2 ≤ x → Supply.RoughDyadCoefficient x C (Hm x) (alpha x)) {x : ℝ}
    (hHm : 0 < Hm x) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) :
    (∑ m ∈ ArtinPrimitiveRoots.TypeII.familyTerms (familyOf δ C κ Hm Hn alpha hs hr) x,
        (familyOf δ C κ Hm Hn alpha hs hr).alpha x m * χ (m : ZMod k) *
          Complex.exp (Complex.I * (t : ℂ) * (Real.log (m : ℝ) : ℂ))) =
      Supply.twistedSum (Hm x) (alpha x) χ t := by
  rw [familyTerms_familyOf hs hr hHm.le]
  unfold Supply.twistedSum
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h := ((Supply.mem_dyad hHm.le).mp hm).1
    rw [Nat.cast_zero] at h
    exact absurd hHm (not_lt.mpr h)
  rw [natCast_cpow_mul_I hm0]
  rfl

/-- **The selected family has the long coefficient cancellation**, if each of its coefficients is
`0` or belongs to a family that passes the coefficient test: the test is uniform in the scales and
in the coefficients of the family. -/
theorem hasLongCoefficientCancellation_familyOf {δ C κ : ℝ} {Hm Hn : ℝ → ℝ}
    {alpha : ℝ → ℕ → ℂ} (hs : ∀ x, 2 ≤ x → Supply.TypeIIScales δ κ x (Hm x) (Hn x))
    (hr : ∀ x, 2 ≤ x → Supply.RoughDyadCoefficient x C (Hm x) (alpha x))
    {𝒜 : ℝ → ℝ → ℝ → Set (ℕ → ℂ)} (h𝒜 : Supply.PassesCoefficientTest δ κ 𝒜)
    (hmem : ∀ x, 2 ≤ x → alpha x = 0 ∨ alpha x ∈ 𝒜 x (Hm x) (Hn x)) :
    ArtinPrimitiveRoots.TypeII.HasLongCoefficientCancellation
      (familyOf δ C κ Hm Hn alpha hs hr) := by
  intro A₀ B A hA₀ hB hA
  obtain ⟨M, x₁, hM⟩ := h𝒜 A₀ B A hA₀ hB hA
  refine ⟨max M 1, max x₁ 2, lt_of_lt_of_le one_pos (le_max_right _ _), le_max_right _ _,
    le_max_right _ _, fun x hx k hk hkL χ t ht => ?_⟩
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans hx
  have hx2 : (2 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hHm : 0 < Hm x := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 δ) (hs x hx2).le_left
  have hLA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  rw [familyOf_sum_eq hs hr hHm χ t]
  refine (div_le_iff₀ hHm).mpr ?_
  rcases hmem x hx2 with h0 | hin
  · have hzero : Supply.twistedSum (Hm x) (alpha x) χ t = 0 := by
      unfold Supply.twistedSum
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [h0, Pi.zero_apply, zero_mul, zero_mul]
    rw [hzero, norm_zero]
    exact mul_nonneg (mul_nonneg (zero_le_one.trans (le_max_right M 1)) hLA) hHm.le
  · calc ‖Supply.twistedSum (Hm x) (alpha x) χ t‖
        ≤ M * Hm x * Real.log x ^ (-A) :=
          hM x hx₁ (Hm x) (Hn x) (hs x hx2) (alpha x) hin k hk hkL χ t ht
      _ = M * (Real.log x ^ (-A) * Hm x) := by ring
      _ ≤ max M 1 * (Real.log x ^ (-A) * Hm x) :=
          mul_le_mul_of_nonneg_right (le_max_left M 1) (mul_nonneg hLA hHm.le)
      _ = max M 1 * Real.log x ^ (-A) * Hm x := by ring

end Supply.MarkedBridge

open Supply.MarkedBridge in
/-- **The marked Type II estimate in coefficient form** ([A] `lem:marked-coefficient-transfer`,
[P] Theorem 3.1 in coefficient form) follows from the vendored theorem
`ArtinPrimitiveRoots.TypeII.marked_coefficient_transfer`. -/
theorem markedTypeIICoefficientForm_of_vendored (hV : VendoredMarkedCoefficientTransfer) :
    Supply.MarkedTypeIICoefficientForm := by
  intro δ C Dstar q κ hδ hC hD hq hq1 hκ
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos hκ
  rcases le_or_gt δ (1 / 2) with hδ2 | hδ2
  swap
  · -- no scales at large `x`: the statement is empty
    obtain ⟨x₀, hx₀⟩ := not_typeIIScales (κ := κ) hδ2
    exact ⟨0, fun K _ 𝔞 𝒜 _ => ⟨0, x₀, fun x hx Hm Hn hs => absurd hs (hx₀ x hx Hm Hn)⟩⟩
  obtain ⟨K₀, hK₀⟩ := hV δ C Dstar q κ⁻¹ κ hδ hC hD hq hq1 (inv_pos.mpr hκ0) hκ0
    ((inv_le_one_of_one_le₀ hκ).trans hκ)
  refine ⟨max K₀ 1, fun K hK 𝔞 𝒜 h𝒜 => ?_⟩
  have hKK₀ : K₀ ≤ K := (le_max_left _ _).trans hK
  have hK1 : 0 < K := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hK)
  -- the selection at every `x ≥ 2`
  have hsel : ∀ x : ℝ, ∃ T : ℝ × ℝ × (ℕ → ℂ), 2 ≤ x →
      Supply.TypeIIScales δ κ x T.1 T.2.1 ∧ Supply.RoughDyadCoefficient x C T.1 T.2.2 ∧
      (T.2.2 = 0 ∨ T.2.2 ∈ 𝒜 x T.1 T.2.1) ∧
      ∀ n : ℕ, (n : ℝ) ≤ x → ∀ Hm' Hn' : ℝ, Supply.TypeIIScales δ κ x Hm' Hn' →
        ∀ α' ∈ 𝒜 x Hm' Hn', Supply.RoughDyadCoefficient x C Hm' α' →
          Violation C Dstar q 𝔞 n x Hm' Hn' α' → Violation C Dstar q 𝔞 n x T.1 T.2.1 T.2.2 := by
    intro x
    by_cases hx : 2 ≤ x
    · have hx1 : 1 ≤ x := by linarith
      obtain ⟨Hm, Hn, α, h⟩ := exists_selection δ κ C Dstar q 𝔞 𝒜 hx1
        ⟨_, _, typeIIScales_sqrt hδ2 hκ hx1⟩
      exact ⟨(Hm, Hn, α), fun _ => h⟩
    · exact ⟨(0, 0, 0), fun h => absurd h hx⟩
  choose T hT using hsel
  have hs : ∀ x, 2 ≤ x → Supply.TypeIIScales δ κ x (T x).1 (T x).2.1 := fun x hx => (hT x hx).1
  have hr : ∀ x, 2 ≤ x → Supply.RoughDyadCoefficient x C (T x).1 (T x).2.2 :=
    fun x hx => (hT x hx).2.1
  -- the vendored bound for the selected family
  obtain ⟨C', x₀, -, hx₀, hbound⟩ := hK₀ K hKK₀
    (familyOf δ C κ (fun x => (T x).1) (fun x => (T x).2.1) (fun x => (T x).2.2) hs hr)
    (hasLongCoefficientCancellation_familyOf hs hr h𝒜 fun x hx => (hT x hx).2.2.1)
    𝔞.exponent (validBands hK1 𝔞)
  refine ⟨(⌈C'⌉₊ : ℝ), max x₀ (⌈C'⌉₊ : ℝ), fun x hx Hm Hn hsc F hF hFinv α hα hαr β hβ => ?_⟩
  have hxx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hxN : ((⌈C'⌉₊ : ℕ) : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hx2 : (2 : ℝ) ≤ x := hx₀.trans hxx₀
  have hx0 : 0 < x := by linarith
  have hpow : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
  have hLD : 0 ≤ Real.log x ^ (-Dstar) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  by_contra hlt
  rw [not_le] at hlt
  -- the violation moves to the selected scales and coefficient
  obtain ⟨F', β', hF', hFinv', hβ', hlt'⟩ :=
    (hT x hx2).2.2.2 ⌈C'⌉₊ hxN Hm Hn hsc α hα hαr ⟨F, β, hF, hFinv, hβ, hlt⟩
  have hTm : 0 < (T x).1 := lt_of_lt_of_le hpow (hs x hx2).le_left
  have hTn : 0 < (T x).2.1 := lt_of_lt_of_le hpow (hs x hx2).le_right
  have hb := hbound x hxx₀ β'
    (fun n hn => ⟨mem_dyadicIntegers.mpr ⟨(hβ'.support n hn).1, (hβ'.support n hn).2.1⟩, by
      rw [roughCutoff_eq]
      exact (hβ'.support n hn).2.2⟩)
    (fun n _ => hβ'.bound n) F' (isMarkedInvariant 𝔞 x hF' hFinv')
  change ‖ArtinPrimitiveRoots.TypeII.markedBilinearSum x K 𝔞.exponent q F' (T x).1 (T x).2.1
      (dyadSet (T x).1) (T x).2.2 β'‖ ≤ C' * ((T x).1 * (T x).2.1) * Real.log x ^ (-Dstar) at hb
  rw [markedBilinearSum_eq q 𝔞 x hTm.le hTn.le] at hb
  have hle : C' * ((T x).1 * (T x).2.1) * Real.log x ^ (-Dstar) ≤
      ((⌈C'⌉₊ : ℕ) : ℝ) * ((T x).1 * (T x).2.1) * Real.log x ^ (-Dstar) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.le_ceil C') (mul_nonneg hTm.le hTn.le)) hLD
  exact absurd (hlt'.trans_le (hb.trans hle)) (lt_irrefl _)

end SimultaneousPrimitiveRoots.Unconditional
