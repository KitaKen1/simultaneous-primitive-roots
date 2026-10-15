module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Basic

/-!
# The interior prime statistic in a fixed residue class ("Theorem 7.1^{H,b}")

[P] Theorem 7.1 (`[P-07:0022–0030]`, with the setup of `[P-07:0004–0020]`): fix `d ≥ 1` and
`ε > 0`; for slot intervals `𝓘_1, …, 𝓘_d` of primes with lower endpoints `≥ x^ε` and product of
the upper endpoints `≤ x^{1-ε}`, and every nonnegative `Φ ∈ C_c^∞((0, ∞))`,

`∑_p Φ((p-1)/x) (f_x(p-1) - C_x) = o(x / log x)`,

the limit being over all real `x → ∞`, for slot intervals subject to these bounds
(`[P-07:0028–0029]`).

The public paper's `prop:ap` (`[PUB-tex:0454–0461]`, proof `[PUB-tex:0462–0535]`; `(6.7)` in
`[PUB-ja:0479–0483]`) is the same statement with the factor `1_{p ≡ b (mod H)}`, for fixed `H ≥ 1`
and `(b, H) = 1`, written for `d = 1` and the slot `(x^α, x^β]`, `1/2 < α < β < 1`.

* `PrimeStatisticFixedClassAt d H b`: the fixed-class statement for `d` slots, one modulus `H` and
  one class `b`, in the generality of [P] Theorem 7.1 (all `ε > 0`, all admissible slot systems,
  all admissible `Φ`).
* `PrimeStatisticFixedClass d`: the same for every `H ≥ 1` and every reduced `b`.
* `InteriorPrimeStatistic d`: [P] Theorem 7.1 itself; it is the case `H = 1`
  (`primeStatisticFixedClassAt_one_iff`).
* `LongSlotStatisticAt α β H b`: the public paper's `prop:ap` for one class, with the paper's
  `f_x` and `C_x`; `fixedClassLongPrimeStatistic_iff` identifies `FixedClassLongPrimeStatistic α β`
  of `SupplyBridge.lean` with it.
* `fixedClassLongPrimeStatistic_of_primeStatisticFixedClass`: **the bridge**,
  `PrimeStatisticFixedClass 1 → FixedClassLongPrimeStatistic α β` for all `0 < α` and `β < 1`.

## Choices

* **Uniformity in the slots.** The slot intervals depend on `x` (their endpoints are constrained by
  powers of `x`), so the last sentence of the theorem (`[P-07:0028–0029]`) is read as: the bound
  `|∑| ≤ η x / log x` holds for all large `x` simultaneously for all admissible slot systems at
  `x`. This is the reading the proof supports ([P] Theorem 6.1 states its uniformity in the active
  groups and in the slot intervals, `[P-06:0073–0076]`), and for `d ≥ 1` it is equivalent to the
  `o(x / log x)` statement along every choice `x ↦ S x` of admissible slots
  (`primeStatisticFixedClassAt_iff_forall_selection`).
* **Generality.** [P] proves the case `H = 1` for all `d ≥ 1`. The public paper writes the changes
  for a class only for `d = 1` and the single slot `(x^α, x^β]`; `PrimeStatisticFixedClassAt d H b`
  with `d ≥ 2` and `H ≥ 2` is not written in either paper (the changes do not involve the slots).
  Only `d = 1` is used by the bridge.
* **The range of `(α, β)`.** The public paper fixes `1/2 < α < β < 1` (`[PUB-tex:0075]`) and
  `0 < c₀ < (1 - β)/2` (`[PUB-tex:0224]`); [P] needs `ε = min(α, 1 - β) > 0` and `0 < c₀ < ε/2`
  (`[P-07:0004–0007, 0078]`), which is the same condition when `α > 1/2`. The bridge holds for all
  `0 < α` and `β < 1` (for `α ≥ β` the slot is empty and the statement is trivial).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply

open Filter Asymptotics
open scoped Topology ContDiff

noncomputable section

/-- `∑_p Φ((p-1)/x) 1_{p ≡ b (mod H)} (f_x(p-1) - C_x)` for the slot system `S`
(`[P-07:0024–0027]` (eq:interior) with the class factor of `[PUB-tex:0457–0460]` (eq:fdap)). -/
def classPrimeSum {d : ℕ} (H b : ℕ) (Φ : ℝ → ℝ) (S : Fin d → Finset ℕ) (x : ℝ) : ℝ :=
  ∑ᶠ p : ℕ, if p.Prime ∧ p ≡ b [MOD H] then
    Φ (((p : ℝ) - 1) / x) * ((slotCount S (p - 1) : ℝ) - slotMass S) else 0

/-- `∑_p Φ((p-1)/x) (f_x(p-1) - C_x)` (`[P-07:0024–0027]`, (eq:interior)). -/
def primeSum {d : ℕ} (Φ : ℝ → ℝ) (S : Fin d → Finset ℕ) (x : ℝ) : ℝ :=
  ∑ᶠ p : ℕ, if p.Prime then
    Φ (((p : ℝ) - 1) / x) * ((slotCount S (p - 1) : ℝ) - slotMass S) else 0

/-- **Theorem 7.1^{H,b}: the interior prime statistic in the class `b (mod H)`**, for `d` slots.

For every fixed `ε > 0` and every nonnegative `Φ ∈ C_c^∞((0, ∞))`,
`∑_p Φ((p-1)/x) 1_{p ≡ b (H)} (f_x(p-1) - C_x) = o(x / log x)`, uniformly in the slot intervals
with lower endpoints `≥ x^ε` and product of upper endpoints `≤ x^{1-ε}`.

Sources: `[P-07:0004–0030]` (`H = 1`), `[PUB-tex:0454–0461]` (`d = 1`, slot `(x^α, x^β]`).
Order of quantifiers: `ε`, `Φ`, then the precision `η`, then `x` large (the threshold depends on
`d, H, b, ε, Φ, η`), then the slot system. `H` and `b` are fixed first (`[PUB-tex:0455]`). The
statement is used with `0 < H` and `b.Coprime H`, which are hypotheses of
`PrimeStatisticFixedClass`. -/
def PrimeStatisticFixedClassAt (d H b : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
    tsupport Φ ⊆ Set.Ioi 0 → (∀ t, 0 ≤ Φ t) →
      ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop, ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
        |classPrimeSum H b Φ S x| ≤ η * (x / Real.log x)

/-- **Theorem 7.1^{H,b} for every modulus and every reduced class** (`[PUB-tex:0454–0461]`, where
`H ≥ 1` and the class `b` with `(b, H) = 1` are fixed). `PrimeStatisticFixedClass 1` is the
statement behind the public paper's `prop:ap`. -/
def PrimeStatisticFixedClass (d : ℕ) : Prop :=
  ∀ H b : ℕ, 0 < H → b.Coprime H → PrimeStatisticFixedClassAt d H b

/-- **[P] Theorem 7.1** (`[P-07:0022–0030]`), for `d` slots; the theorem is for `d ≥ 1`. -/
def InteriorPrimeStatistic (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
    tsupport Φ ⊆ Set.Ioi 0 → (∀ t, 0 ≤ Φ t) →
      ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop, ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
        |primeSum Φ S x| ≤ η * (x / Real.log x)

/-! ### Sanity checks -/

/-- For `H = 1` the class condition is empty. -/
theorem classPrimeSum_one {d : ℕ} (b : ℕ) (Φ : ℝ → ℝ) (S : Fin d → Finset ℕ) (x : ℝ) :
    classPrimeSum 1 b Φ S x = primeSum Φ S x := by
  unfold classPrimeSum primeSum
  refine finsum_congr fun p => ?_
  by_cases hp : p.Prime
  · have h1 : p.Prime ∧ p ≡ b [MOD 1] := ⟨hp, Nat.modEq_one⟩
    rw [if_pos h1, if_pos hp]
  · have h2 : ¬ (p.Prime ∧ p ≡ b [MOD 1]) := fun h => hp h.1
    rw [if_neg h2, if_neg hp]

/-- **`H = 1` is [P] Theorem 7.1.** -/
theorem primeStatisticFixedClassAt_one_iff (d b : ℕ) :
    PrimeStatisticFixedClassAt d 1 b ↔ InteriorPrimeStatistic d := by
  unfold PrimeStatisticFixedClassAt InteriorPrimeStatistic
  simp only [classPrimeSum_one]

/-- The fixed-class statement for all classes contains [P] Theorem 7.1. -/
theorem interiorPrimeStatistic_of_primeStatisticFixedClass {d : ℕ}
    (h : PrimeStatisticFixedClass d) : InteriorPrimeStatistic d :=
  (primeStatisticFixedClassAt_one_iff d 1).mp (h 1 1 Nat.one_pos (Nat.coprime_one_right 1))

/-- **The uniform statement is the statement along every choice of slots.** For `d ≥ 1`,
`PrimeStatisticFixedClassAt d H b` holds if and only if for every `ε`, `Φ` and every choice
`x ↦ S x` of slot systems that are admissible for all large `x`,
`∑_p Φ((p-1)/x) 1_{p ≡ b (H)} (f_x(p-1) - C_x) = o(x / log x)`: this is the literal form of
`[P-07:0028–0029]`. -/
theorem primeStatisticFixedClassAt_iff_forall_selection {d : ℕ} (hd : 0 < d) (H b : ℕ) :
    PrimeStatisticFixedClassAt d H b ↔
      ∀ ε : ℝ, 0 < ε → ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ Set.Ioi 0 → (∀ t, 0 ≤ Φ t) →
          ∀ S : ℝ → Fin d → Finset ℕ, (∀ᶠ x : ℝ in atTop, SlotsAdmissible ε x (S x)) →
            (fun x : ℝ => classPrimeSum H b Φ (S x) x) =o[atTop] fun x : ℝ => x / Real.log x := by
  constructor
  · intro h ε hε Φ h1 h2 h3 h4 S hS
    rw [isLittleO_iff]
    intro c hc
    filter_upwards [h ε hε Φ h1 h2 h3 h4 c hc, hS, eventually_gt_atTop (1 : ℝ)]
      with x hx hadm hx1
    have hpos : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
    exact hx _ hadm
  · intro h ε hε Φ h1 h2 h3 h4 η hη
    by_contra hcon
    rw [not_eventually] at hcon
    classical
    -- at each `x`, pick a violating admissible slot system if there is one
    let S : ℝ → Fin d → Finset ℕ := fun x =>
      if hx : ∃ T : Fin d → Finset ℕ, SlotsAdmissible ε x T ∧
          ¬ |classPrimeSum H b Φ T x| ≤ η * (x / Real.log x)
      then hx.choose else fun _ => ∅
    have hS : ∀ᶠ x : ℝ in atTop, SlotsAdmissible ε x (S x) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx0
      by_cases hx : ∃ T : Fin d → Finset ℕ, SlotsAdmissible ε x T ∧
          ¬ |classPrimeSum H b Φ T x| ≤ η * (x / Real.log x)
      · have hSx : S x = hx.choose := dif_pos hx
        rw [hSx]
        exact hx.choose_spec.1
      · have hSx : S x = fun _ => ∅ := dif_neg hx
        rw [hSx]
        exact slotsAdmissible_empty hd ε hx0
    have hlo := isLittleO_iff.mp (h ε hε Φ h1 h2 h3 h4 S hS) hη
    obtain ⟨x, hxbad, hxlo, hx1⟩ :=
      (hcon.and_eventually (hlo.and (eventually_gt_atTop (1 : ℝ)))).exists
    have hex : ∃ T : Fin d → Finset ℕ, SlotsAdmissible ε x T ∧
        ¬ |classPrimeSum H b Φ T x| ≤ η * (x / Real.log x) := by
      by_contra hne
      exact hxbad fun T hT => by
        by_contra hbad
        exact hne ⟨T, hT, hbad⟩
    have hSx : S x = hex.choose := dif_pos hex
    have hpos : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx1)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos, hSx] at hxlo
    exact hex.choose_spec.2 hxlo

/-! ### The bridge to `FixedClassLongPrimeStatistic` -/

/-- For the single slot `(x^α, x^β]`, the sum of this file is the sum of `SupplyBridge.lean`. -/
theorem classPrimeSum_longSlot {α β x : ℝ} (hx : 0 ≤ x) (H b : ℕ) (Φ : ℝ → ℝ) :
    classPrimeSum H b Φ (fun _ : Fin 1 => longSlot α β x) x =
      fixedClassLongPrimeSum α β H b Φ x := by
  unfold classPrimeSum fixedClassLongPrimeSum
  refine finsum_congr fun p => ?_
  by_cases hp : p.Prime ∧ p ≡ b [MOD H]
  · rw [if_pos hp, if_pos hp, slotCount_one, slotMass_one,
      primeHits_longSlot hx (Nat.sub_ne_zero_of_lt hp.1.one_lt), reciprocalMass_longSlot]
  · rw [if_neg hp, if_neg hp]

/-- **The public paper's `prop:ap` for one pair of exponents and one class**
(`[PUB-tex:0454–0461]`), in the notation of this directory: for the single slot `(x^α, x^β]`,
`∑_p Φ((p-1)/x) 1_{p ≡ b (H)} (f_x(p-1) - C_x) = o(x / log x)` for every admissible `Φ`, with
`f_x(n) = ∑_{x^α < Q ≤ x^β} 1_{Q ∣ n}` and `C_x = ∑_{x^α < Q ≤ x^β} 1/Q` as in (eq:fx)
`[PUB-tex:0075–0079]`. -/
def LongSlotStatisticAt (α β : ℝ) (H b : ℕ) : Prop :=
  ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ → tsupport Φ ⊆ Set.Ioi 0 → (∀ t, 0 ≤ Φ t) →
    (fun x : ℝ => classPrimeSum H b Φ (fun _ : Fin 1 => longSlot α β x) x) =o[atTop]
      fun x : ℝ => x / Real.log x

/-- **`FixedClassLongPrimeStatistic α β` is the public paper's `prop:ap`**: the target of
`SupplyBridge.lean` (written with `Nat.primeFactors` and a `Finset.range`) is the statement with
the paper's `f_x` and `C_x`, for every modulus and every reduced class. -/
theorem fixedClassLongPrimeStatistic_iff (α β : ℝ) :
    FixedClassLongPrimeStatistic α β ↔
      ∀ H b : ℕ, 0 < H → b.Coprime H → LongSlotStatisticAt α β H b := by
  have hev : ∀ (H b : ℕ) (Φ : ℝ → ℝ),
      (fun x : ℝ => classPrimeSum H b Φ (fun _ : Fin 1 => longSlot α β x) x) =ᶠ[atTop]
        fixedClassLongPrimeSum α β H b Φ := by
    intro H b Φ
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact classPrimeSum_longSlot hx H b Φ
  constructor
  · intro h H b hH hb Φ h1 h2 h3 h4
    exact (h H b hH hb Φ h1 h2 h3 h4).congr' (hev H b Φ).symm EventuallyEq.rfl
  · intro h H b hH hb Φ h1 h2 h3 h4
    exact (h H b hH hb Φ h1 h2 h3 h4).congr' (hev H b Φ) EventuallyEq.rfl

/-- Theorem 7.1^{H,b} for one slot gives `prop:ap` for the class `b (mod H)` and every `0 < α`,
`β < 1`: apply it with margin `ε = min α (1 - β)` to the slot `(x^α, x^β]`, which is admissible
for `x ≥ 1`. -/
theorem longSlotStatisticAt_of_primeStatisticFixedClassAt {α β : ℝ} (hα : 0 < α) (hβ : β < 1)
    {H b : ℕ} (h : PrimeStatisticFixedClassAt 1 H b) : LongSlotStatisticAt α β H b := by
  intro Φ hΦ hΦc hΦs hΦ0
  rw [isLittleO_iff]
  intro c hc
  have hε : 0 < min α (1 - β) := lt_min hα (by linarith)
  filter_upwards [h (min α (1 - β)) hε Φ hΦ hΦc hΦs hΦ0 c hc, eventually_gt_atTop (1 : ℝ)]
    with x hx hx1
  have hpos : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
  exact hx _ (slotsAdmissible_longSlot α β hx1.le)

/-- **The bridge.** Theorem 7.1^{H,b} for one slot (`PrimeStatisticFixedClass 1`) gives the
fixed-class long-prime statistic of `SupplyBridge.lean` for every `0 < α` and `β < 1`.

The public paper's `prop:ap` is the case `1/2 < α < β < 1`; the Lean reduction uses
`α = 1 - δ/2`, `β = 1 - δ/4`, `δ = 10⁻⁶`. -/
theorem fixedClassLongPrimeStatistic_of_primeStatisticFixedClass {α β : ℝ} (hα : 0 < α)
    (hβ : β < 1) (h : PrimeStatisticFixedClass 1) : FixedClassLongPrimeStatistic α β :=
  (fixedClassLongPrimeStatistic_iff α β).mpr fun H b hH hb =>
    longSlotStatisticAt_of_primeStatisticFixedClassAt hα hβ (h H b hH hb)

/-- The bridge at the exponents of the Lean reduction: `α = 1 - δ/2`, `β = 1 - δ/4` with
`δ = 10⁻⁶`. -/
theorem fixedClassLongPrimeStatistic_paper (h : PrimeStatisticFixedClass 1) :
    FixedClassLongPrimeStatistic (1 - (10 : ℝ)⁻¹ ^ 6 / 2) (1 - (10 : ℝ)⁻¹ ^ 6 / 4) :=
  fixedClassLongPrimeStatistic_of_primeStatisticFixedClass (by norm_num) (by norm_num) h

end

end SimultaneousPrimitiveRoots.Unconditional.Supply
