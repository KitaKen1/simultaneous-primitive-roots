module

public import SimultaneousPrimitiveRoots.Unconditional.SupplyBridge

/-!
# Objects of the "S side": bands, marked weights and long-prime slots

This file defines the objects that occur in the statements of [P] Theorems 3.1, 6.1 and 7.1
(`verification/stage7-sources/P-03.tex`, `P-06.tex`, `P-07.tex`; a reference `[P-07:0022–0030]`
means lines 22–30 of `P-07.tex`, and `[A-08:…]`, `[PUB-tex:…]`, `[PUB-ja:…]` refer in the same way
to `A-08.tex`, to `publication_work_2026-10-09/TeX/simultaneous-primitive-roots.tex` and to
`proof_ja.md`).

Throughout, `x` is the real parameter, `L = log x` is written `Real.log x`, and all sets of primes
are `Finset ℕ`.

* `roughCutoff x = W = exp(L^{0.24})`, `IsRough W n`, `mertensProduct W = V(W)`.
* `MarkingArray K`: `K` band exponents `0.1 < a_1 < ⋯ < a_K < 0.2`; `bandPrimes a x` is the band
  `{p : exp(L^a) ≤ p ≤ exp(2 L^a)}`.
* `primeHits S n = ω_S(n)`, `reciprocalMass S = V_S`, `markFactor q S n = q^{ω-1} ω / V`,
  `markedWeight q 𝔞 x n = 𝒲(n)`.
* `SlotsAdmissible ε x S`: `d` slot intervals of primes with lower endpoints `≥ x^ε` and product of
  the upper endpoints `≤ x^{1-ε}`; `slotCount S u = f_x(u)` and `slotMass S = C_x`.
* `longSlot α β x`: the single slot `(x^α, x^β]` of the public paper, and the identification of
  `slotCount`, `slotMass` at `d = 1` with `longPrimeCount`, `longPrimeMass` of `SupplyBridge.lean`.

Nothing deep is proved here; the theorems are sanity checks of the definitions.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply

open Filter Asymptotics
open scoped Topology ContDiff

noncomputable section

/-! ### The rough cutoff -/

/-- `W = exp(L^{0.24})` with `L = log x` (`[P-03:0008–0011]`, `[P-02:0003–0008]`,
`[A-08:0015–0018]`). For `x < 1` the value is not meaningful (`L < 0`); every statement below is
about large `x`. -/
def roughCutoff (x : ℝ) : ℝ := Real.exp (Real.log x ^ (0.24 : ℝ))

/-- `n` is `W`-rough: no prime factor is `≤ W`, i.e. `P⁻(n) > W` (`[P-03:0012]`,
`[P-02:0009–0010]`, `[A-08:0019–0021]`). `1` is rough (`P⁻(1) = ∞`), and `0` is not rough once
`W ≥ 2`. -/
def IsRough (W : ℝ) (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → W < (p : ℝ)

/-- `V(y) = ∏_{p ≤ y} (1 - 1/p)` (`[P-03:0010]`, `[A-08:0017]`). -/
def mertensProduct (y : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

theorem isRough_one (W : ℝ) : IsRough W 1 := by
  intro p hp hdvd
  exact absurd (Nat.dvd_one.mp hdvd) hp.ne_one

theorem not_isRough_zero {W : ℝ} (hW : 2 ≤ W) : ¬ IsRough W 0 := by
  intro h
  have h2 : W < 2 := by exact_mod_cast h 2 Nat.prime_two (dvd_zero 2)
  linarith

/-! ### Bands and the marked weight -/

/-- A marking array: `K` band exponents `0.1 < a_1 < ⋯ < a_K < 0.2`, fixed before `x` grows
(`[P-03:0013–0018]`, `[P-07:0034–0043]`, `[A-08:0024–0031]`). -/
structure MarkingArray (K : ℕ) where
  /-- the exponents `a_1, …, a_K` -/
  exponent : Fin K → ℝ
  /-- `a_1 < ⋯ < a_K` -/
  strictMono : StrictMono exponent
  /-- `0.1 < a_i` -/
  gt_tenth : ∀ i, 1 / 10 < exponent i
  /-- `a_i < 0.2` -/
  lt_fifth : ∀ i, exponent i < 1 / 5

/-- The band `𝒫 = {p prime : exp(L^a) ≤ p ≤ exp(2 L^a)}` (`[P-03:0014–0016]`,
`[P-07:0041–0042]`). -/
def bandPrimes (a x : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.exp (2 * Real.log x ^ a)⌋₊ + 1)).filter fun p : ℕ =>
    p.Prime ∧ Real.exp (Real.log x ^ a) ≤ (p : ℝ)

theorem mem_bandPrimes {a x : ℝ} {p : ℕ} :
    p ∈ bandPrimes a x ↔
      p.Prime ∧ Real.exp (Real.log x ^ a) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (2 * Real.log x ^ a) := by
  unfold bandPrimes
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (Real.exp_pos _).le]
  tauto

/-- `ω_S(n) = #{p ∈ S : p ∣ n}` (`[P-03:0023]`, `[P-06:0028]`). Every prime divides `0`
(`[P-06:0105–0106]`). -/
def primeHits (S : Finset ℕ) (n : ℕ) : ℕ := (S.filter fun p => p ∣ n).card

/-- `V_S = ∑_{p ∈ S} 1/p` (`[P-03:0021]`, `[P-06:0016]`). -/
def reciprocalMass (S : Finset ℕ) : ℝ := ∑ p ∈ S, 1 / (p : ℝ)

/-- One group factor `q^{ω_S(n) - 1} ω_S(n) / V_S` of a marked weight (`[P-07:0036–0039]`). The
subtraction is truncated, so the factor is `0` when `ω_S(n) = 0`. -/
def markFactor (q : ℝ) (S : Finset ℕ) (n : ℕ) : ℝ :=
  q ^ (primeHits S n - 1) * (primeHits S n : ℝ) / reciprocalMass S

/-- The marked weight `𝒲(n) = ∏_i q^{ω_i(n) - 1} ω_i(n) / V_i = q^{ω(n) - K} ∏_i ω_i(n) / V_i`
(`[P-03:0029–0035]`, `[P-07:0036–0040]`, `[A-08:0044–0053]`); it is `0` if some band has no
divisor of `n` (`markedWeight_eq_zero`), and it has the second form otherwise
(`markedWeight_eq_of_pos`). -/
def markedWeight (q : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (n : ℕ) : ℝ :=
  ∏ i, markFactor q (bandPrimes (𝔞.exponent i) x) n

theorem markFactor_eq_zero {q : ℝ} {S : Finset ℕ} {n : ℕ} (h : primeHits S n = 0) :
    markFactor q S n = 0 := by
  unfold markFactor
  rw [h, Nat.cast_zero, mul_zero, zero_div]

/-- The weight vanishes when some band contains no prime divisor of `n` (`[P-03:0033]`). -/
theorem markedWeight_eq_zero {q : ℝ} {K : ℕ} {𝔞 : MarkingArray K} {x : ℝ} {n : ℕ} {i : Fin K}
    (h : primeHits (bandPrimes (𝔞.exponent i) x) n = 0) : markedWeight q 𝔞 x n = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (markFactor_eq_zero h)

/-- The form `𝒲(n) = q^{ω(n) - K} ∏_i ω_i(n) / V_i` of `[P-03:0029–0032]`, valid when every band
has a divisor of `n`. -/
theorem markedWeight_eq_of_pos (q : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (n : ℕ)
    (h : ∀ i, 1 ≤ primeHits (bandPrimes (𝔞.exponent i) x) n) :
    markedWeight q 𝔞 x n =
      q ^ ((∑ i, primeHits (bandPrimes (𝔞.exponent i) x) n) - K) *
        ∏ i, ((primeHits (bandPrimes (𝔞.exponent i) x) n : ℝ) /
          reciprocalMass (bandPrimes (𝔞.exponent i) x)) := by
  have hsum : ∑ i : Fin K, (primeHits (bandPrimes (𝔞.exponent i) x) n - 1) + K =
      ∑ i : Fin K, primeHits (bandPrimes (𝔞.exponent i) x) n := by
    calc ∑ i : Fin K, (primeHits (bandPrimes (𝔞.exponent i) x) n - 1) + K
        = ∑ i : Fin K, (primeHits (bandPrimes (𝔞.exponent i) x) n - 1) + ∑ _i : Fin K, 1 := by
          simp
      _ = ∑ i : Fin K, ((primeHits (bandPrimes (𝔞.exponent i) x) n - 1) + 1) :=
          Finset.sum_add_distrib.symm
      _ = ∑ i : Fin K, primeHits (bandPrimes (𝔞.exponent i) x) n :=
          Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (h i)
  have hexp : (∑ i : Fin K, primeHits (bandPrimes (𝔞.exponent i) x) n) - K =
      ∑ i : Fin K, (primeHits (bandPrimes (𝔞.exponent i) x) n - 1) := by
    omega
  unfold markedWeight markFactor
  rw [hexp, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-! ### Long-prime slots -/

/-- **Slot intervals** (`[P-07:0004–0007]`, `[P-06:0056–0058]`): for each `i < d`, `S i` is an
interval of primes with lower endpoint at least `x^ε`, and the product of the upper endpoints is at
most `x^{1-ε}`.

Choice made here: a slot is given by its finite set of primes, "interval" means that every prime
between two members is a member, the lower endpoint is read as the least member and the upper
endpoint as the largest member (`Finset.sup id`, which is `0` for an empty slot). A set of primes
`{ℓ : ℓ ∈ I}` for a real interval `I` (open, closed or half-open) with the paper's endpoint bounds
satisfies this, and conversely an admissible `S` with all slots nonempty is the set of primes of
the closed real intervals `[min S i, max S i]`, which satisfy the paper's bounds. If some slot is
empty there is no tuple, `slotCount = 0` and `slotMass = 0`. -/
structure SlotsAdmissible (ε x : ℝ) {d : ℕ} (S : Fin d → Finset ℕ) : Prop where
  /-- the slots consist of primes -/
  prime : ∀ i, ∀ ℓ ∈ S i, ℓ.Prime
  /-- each slot is an interval of primes -/
  interval : ∀ i, ∀ ℓ₁ ∈ S i, ∀ ℓ₂ ∈ S i, ∀ ℓ : ℕ, ℓ.Prime → ℓ₁ ≤ ℓ → ℓ ≤ ℓ₂ → ℓ ∈ S i
  /-- lower endpoints are at least `x^ε` -/
  lower : ∀ i, ∀ ℓ ∈ S i, x ^ ε ≤ (ℓ : ℝ)
  /-- the product of the upper endpoints is at most `x^{1-ε}` -/
  upper : ∏ i, (((S i).sup id : ℕ) : ℝ) ≤ x ^ (1 - ε)

/-- The ordered tuples `𝔩 = (ℓ_1, …, ℓ_d)` of distinct primes with `ℓ_i ∈ S i`
(`[P-07:0009–0010]`, `[P-06:0058–0059]`). -/
def slotTuples {d : ℕ} (S : Fin d → Finset ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset S).filter fun 𝔩 => Function.Injective 𝔩

/-- `f_x(u) = ∑_𝔩 1_{ℓ_1 ⋯ ℓ_d ∣ u}` (`[P-07:0008–0011]`, (ext:statistic)). -/
def slotCount {d : ℕ} (S : Fin d → Finset ℕ) (u : ℕ) : ℕ :=
  ((slotTuples S).filter fun 𝔩 => (∏ i, 𝔩 i) ∣ u).card

/-- `C_x = ∑_𝔩 1 / (ℓ_1 ⋯ ℓ_d)` (`[P-07:0012–0014]`, `[P-06:0062]`). -/
def slotMass {d : ℕ} (S : Fin d → Finset ℕ) : ℝ :=
  ∑ 𝔩 ∈ slotTuples S, 1 / ((∏ i, 𝔩 i : ℕ) : ℝ)

/-- For one slot the tuples are the primes of the slot: `f_x(u) = ω_S(u)`. -/
theorem slotCount_one (S : Finset ℕ) (u : ℕ) :
    slotCount (fun _ : Fin 1 => S) u = primeHits S u := by
  unfold slotCount slotTuples primeHits
  refine Finset.card_nbij' (fun 𝔩 : Fin 1 → ℕ => 𝔩 0) (fun (ℓ : ℕ) (_ : Fin 1) => ℓ) ?_ ?_ ?_ ?_
  · intro 𝔩 h𝔩
    have h := Finset.mem_filter.mp (Finset.mem_coe.mp h𝔩)
    have h1 := Fintype.mem_piFinset.mp (Finset.mem_filter.mp h.1).1 0
    have h2 : 𝔩 0 ∣ u := by
      have := h.2
      rwa [Fin.prod_univ_one] at this
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨h1, h2⟩)
  · intro ℓ hℓ
    have h := Finset.mem_filter.mp (Finset.mem_coe.mp hℓ)
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr fun _ => h.1, Function.injective_of_subsingleton _⟩, ?_⟩)
    rw [Fin.prod_univ_one]
    exact h.2
  · intro 𝔩 _
    funext i
    exact congrArg 𝔩 (Subsingleton.elim 0 i)
  · intro ℓ _
    rfl

/-- For one slot, `C_x = V_S`. -/
theorem slotMass_one (S : Finset ℕ) : slotMass (fun _ : Fin 1 => S) = reciprocalMass S := by
  unfold slotMass slotTuples reciprocalMass
  refine Finset.sum_nbij' (fun 𝔩 : Fin 1 → ℕ => 𝔩 0) (fun (ℓ : ℕ) (_ : Fin 1) => ℓ) ?_ ?_ ?_ ?_ ?_
  · intro 𝔩 h𝔩
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp h𝔩).1 0
  · intro ℓ hℓ
    exact Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr fun _ => hℓ, Function.injective_of_subsingleton _⟩
  · intro 𝔩 _
    funext i
    exact congrArg 𝔩 (Subsingleton.elim 0 i)
  · intro ℓ _
    rfl
  · intro 𝔩 _
    rw [Fin.prod_univ_one]

/-- The system of `d ≥ 1` empty slots is admissible. -/
theorem slotsAdmissible_empty {d : ℕ} (hd : 0 < d) (ε : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    SlotsAdmissible ε x (fun _ : Fin d => (∅ : Finset ℕ)) where
  prime := fun _ ℓ hℓ => absurd hℓ (Finset.notMem_empty ℓ)
  interval := fun _ ℓ₁ hℓ₁ => absurd hℓ₁ (Finset.notMem_empty ℓ₁)
  lower := fun _ ℓ hℓ => absurd hℓ (Finset.notMem_empty ℓ)
  upper := by
    have h0 : ∏ _i : Fin d, (((∅ : Finset ℕ).sup id : ℕ) : ℝ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (⟨0, hd⟩ : Fin d)) (by simp)
    rw [h0]
    exact Real.rpow_nonneg hx _

/-! ### The slot `(x^α, x^β]` of the public paper -/

/-- The primes `Q` with `x^α < Q ≤ x^β`: the slot of `[PUB-tex:0075–0079]` (eq:fx). This is the
index set of `longPrimeMass α β x` in `SupplyBridge.lean`. -/
def longSlot (α β x : ℝ) : Finset ℕ :=
  (Finset.range (⌊x ^ β⌋₊ + 1)).filter fun Q : ℕ => Q.Prime ∧ x ^ α < (Q : ℝ)

theorem reciprocalMass_longSlot (α β x : ℝ) :
    reciprocalMass (longSlot α β x) = longPrimeMass α β x := rfl

/-- On positive integers `ω_{(x^α, x^β]}` is `longPrimeCount` of `SupplyBridge.lean`. (At `n = 0`
they differ: every prime divides `0`, but `Nat.primeFactors 0 = ∅`.) -/
theorem primeHits_longSlot {α β x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    primeHits (longSlot α β x) n = longPrimeCount α β x n := by
  unfold primeHits longPrimeCount longSlot
  congr 1
  ext Q
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hr, hp, hlo⟩, hdvd⟩
    exact ⟨⟨hp, hdvd, hn⟩, hlo,
      (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hr)).trans (Nat.floor_le (Real.rpow_nonneg hx β))⟩
  · rintro ⟨⟨hp, hdvd, _⟩, hlo, hhi⟩
    exact ⟨⟨Nat.lt_succ_iff.mpr (Nat.le_floor hhi), hp, hlo⟩, hdvd⟩

/-- The slot `(x^α, x^β]` is admissible with margin `ε = min α (1 - β)`, for `x ≥ 1`
(`[PUB-tex:0075]`, `[P-07:0004–0007]` with `d = 1`). -/
theorem slotsAdmissible_longSlot (α β : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    SlotsAdmissible (min α (1 - β)) x (fun _ : Fin 1 => longSlot α β x) where
  prime := fun _ ℓ hℓ => (Finset.mem_filter.mp hℓ).2.1
  interval := by
    intro _ ℓ₁ h₁ ℓ₂ h₂ ℓ hℓ h1 h2
    obtain ⟨_, _, hlo⟩ := Finset.mem_filter.mp h₁
    obtain ⟨hr, _, _⟩ := Finset.mem_filter.mp h₂
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_lt h2 (Finset.mem_range.mp hr)),
      hℓ, lt_of_lt_of_le hlo (Nat.cast_le.mpr h1)⟩
  lower := by
    intro _ ℓ hℓ
    obtain ⟨_, _, hlo⟩ := Finset.mem_filter.mp hℓ
    exact (Real.rpow_le_rpow_of_exponent_le hx (min_le_left _ _)).trans hlo.le
  upper := by
    rw [Fin.prod_univ_one]
    have hsup : (longSlot α β x).sup id ≤ ⌊x ^ β⌋₊ :=
      Finset.sup_le fun ℓ hℓ =>
        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hℓ).1)
    calc (((longSlot α β x).sup id : ℕ) : ℝ) ≤ (⌊x ^ β⌋₊ : ℝ) := Nat.cast_le.mpr hsup
      _ ≤ x ^ β := Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hx) β)
      _ ≤ x ^ (1 - min α (1 - β)) :=
          Real.rpow_le_rpow_of_exponent_le hx (by have := min_le_right α (1 - β); linarith)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply
