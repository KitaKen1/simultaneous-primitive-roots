module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointEnergyForms

/-!
# Objects of the proof of the endpoint estimate (cor:SM) ([P] §6)

(cor:SM) (`verification/stage7-sources/P-06.tex`, lines 544–550; `EndpointEnergy` in
`Supply/TwoSided.lean`) is proved in `[P-06:0555–0925]`. This file defines the objects that occur
inside that proof. The intermediate statements are in `EndpointProof/Statements.lean`, the classical
inputs in `EndpointProof/ClassicalInputs.lean`, the proved chain in `EndpointProof/Assembly.lean`.

Conventions. `x` is the real parameter and `L = Real.log x`; a reference `[P-06:0563–0633]` means
lines 563–633 of `P-06.tex`. All integer ranges are sets of *positive* integers, and there is no
natural subtraction except the truncated exponents of the damping (as in `activeWeight`).

* `EndpointData`: the fixed data of (cor:SM), in the manuscript's form `k ≤ L^{C_6}`,
  `T_0 = x L^{C_6 + 1}`; `EndpointConfig d` and `EndpointConfig.Admissible`: the data that vary
  with `x` (active groups, slots, scale, marks, test, twist, cutoff) and their hypotheses. With
  these, `EndpointEnergyAt d C₆ (C₆ + 1)` is `EndpointEnergyBundled d` of `Statements.lean`.
* `timeBound D x = T_0`, `EndpointConfig.endpoint = 𝒰`, `HighEnergyLe`: an energy bound on every
  interval of times inside `{lo ≤ |τ| ≤ hi}`.
* `partialLists`, `partialWeight 𝔊 q₀ t test U`: the active weight `W_{𝐭'}^{𝐛}` with the marks of
  the groups of `U` removed (`t'_g = 0` for `g ∈ U`, `[P-06:0568–0570]`); `hMarks = H_marks`
  (`[P-06:0567]`); `markPrimes`, `totalMarkHits = ω_tot` (`[P-06:0613]`).
* `divisorSum A`, `IsDivisorModel`: a truncated divisor model (cor:divisor-model).
* `natIcc a b`: the integers of `[a, b]`; `normPoly R s c`: a normalized Dirichlet polynomial;
  `IsPrimeInterval`; `primeConv G c`: the convolution `1_G * c`; `slotCountRep`: the slot statistic
  with repeated primes allowed (`[P-06:0695–0697]`).
* `EndpointConfig.constCoeff`, `tupleCoeff` (cor:u-coefficient), `constEndpoint`, `tupleEndpoint`,
  `errEndpoint`: the endpoint after one small-prime mark has been extracted
  (`[P-06:0683–0715]`), so that `𝒰 = 𝒰_tuple - C_x 𝒰_const + 𝒰_err` (`EndpointConfig.endpoint_eq`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology ContDiff

noncomputable section

/-! ### The data of (cor:SM) -/

/-- **The fixed data of (cor:SM)**, in the order of `EndpointEnergyAt`: the slot margin `ε`; the
dampings `q, q₀ ∈ (0,1)`; the `K` inert bands; the active-group constants; the bound `m'` for the
marks; the support `[a₁, a₂] ⊂ (0, ∞)` of the cutoff and the exponents `Dψ j` of its derivatives;
the exponent `Cσ` of the twist; the constants `c₁, c₂` of the scale; and the exponent `C₆` of
(cor:major-arcs) (`[P-06:0455–0460]`): denominators `k ≤ L^{C₆}`, times `|τ| ≤ T₀ = x L^{C₆+1}`. -/
structure EndpointData where
  /-- the slot margin -/
  ε : ℝ
  /-- the damping of the inert weight `𝒲` -/
  q : ℝ
  /-- the damping of the active weight -/
  q₀ : ℝ
  /-- the number of inert bands -/
  K : ℕ
  /-- the inert bands -/
  𝔞 : MarkingArray K
  /-- the active-group constants `c₀, C₀, v₋, v₊` -/
  P : ActiveGroupConstants
  /-- the bound for the numbers of marks `t_g` -/
  m' : ℕ
  /-- lower end of the support of the cutoff -/
  a₁ : ℝ
  /-- upper end of the support of the cutoff -/
  a₂ : ℝ
  /-- the exponents bounding the derivatives of the cutoff -/
  Dψ : ℕ → ℝ
  /-- the exponent of the twist, `|σ| ≤ L^{Cσ}` -/
  Cσ : ℝ
  /-- lower scale constant: `Y ≥ x exp(2 L^{.39} - c₁)` -/
  c₁ : ℝ
  /-- upper scale constant: `Y ≤ x exp(c₂ L^{.46} log L)` -/
  c₂ : ℝ
  /-- the exponent `C₆` of the major arcs -/
  C₆ : ℝ
  ε_pos : 0 < ε
  q_pos : 0 < q
  q_lt_one : q < 1
  q₀_pos : 0 < q₀
  q₀_lt_one : q₀ < 1
  a₁_pos : 0 < a₁
  a₁_le_a₂ : a₁ ≤ a₂
  C₆_pos : 0 < C₆

/-- **The data of (cor:SM) that vary with `x`**: the active groups, the `d` slots, the scale `Y`,
the vector of marks `𝐭`, the list test `𝐛`, the twist `σ` and the cutoff `ψ₁`. -/
structure EndpointConfig (d : ℕ) where
  /-- the active groups -/
  𝔊 : ActiveGroups
  /-- the slots -/
  S : Fin d → Finset ℕ
  /-- the scale `Y = x H'` -/
  Y : ℝ
  /-- the numbers of marks `t_g` -/
  t : 𝔊.Index → ℕ
  /-- the list test `𝐛` -/
  test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ
  /-- the twist -/
  σ : ℝ
  /-- the cutoff -/
  ψ₁ : ℝ → ℂ

/-- `T₀ = L Y / H = x L^{C₆ + 1}` (`[P-06:0549]`). -/
def timeBound (D : EndpointData) (x : ℝ) : ℝ := x * Real.log x ^ (D.C₆ + 1)

/-- `∫_a^b |E(τ)|² dτ ≤ bound` for every interval `[a, b]` of times with `lo ≤ |τ| ≤ hi`, i.e.
`[a, b] ⊆ [lo, hi]` or `[a, b] ⊆ [-hi, -lo]`. The high-frequency estimates are stated in this
form: it is monotone in `lo`, and it does not need `lo ≤ hi`. -/
def HighEnergyLe (E : ℝ → ℂ) (lo hi bound : ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ((lo ≤ a ∧ b ≤ hi) ∨ (-hi ≤ a ∧ b ≤ -lo)) →
    ∫ τ in a..b, ‖E τ‖ ^ 2 ≤ bound

/-! ### Marked weights with some marks removed -/

/-- The represented lists at `n` for the vector `𝐭`, with the marks of the groups in `U` removed:
for `g ∉ U`, `t_g` ordered distinct prime divisors of `n` from `𝒫_g`; for `g ∈ U` the dummy list
`(0, …, 0)`. For `U = ∅` this is `ActiveGroups.representedLists`. The dummy entries keep the type
of the list test unchanged. -/
def partialLists (𝔊 : ActiveGroups) (t : 𝔊.Index → ℕ) (U : Finset 𝔊.Index) (n : ℕ) :
    Finset ((g : 𝔊.Index) → Fin (t g) → ℕ) :=
  Fintype.piFinset fun g : 𝔊.Index =>
    if g ∈ U then ({fun _ => 0} : Finset (Fin (t g) → ℕ))
    else (Fintype.piFinset fun _ : Fin (t g) => (𝔊.group g).filter fun p => p ∣ n).filter
      fun 𝔭 => Function.Injective 𝔭

/-- The active marked weight with the marks of the groups in `U` removed:
`W_{𝐭'}^{𝐛}(n) = q_0^{ω_P(n) - ∑_{g ∉ U} t_g} ∏_{g ∉ U} V_g^{-t_g} ∑_{lists} 𝐛`, the weight
(cor:marked-weight) for the vector `t'_g = t_g` (`g ∉ U`), `t'_g = 0` (`g ∈ U`)
(`[P-06:0036–0042, 0568–0570]`: "zero values of `t_g` are allowed; these occur when a small mark
is removed below"). The test is evaluated at the list completed by the dummy entries; when `𝐛`
does not depend on the marks of `U` (in the proof: `U` is one small group and `𝐛` depends only
on big marks) this is `W_{𝐭 - 𝐞_{g_s}}^{𝐛}` of (cor:extract-small). For `U = ∅` it is
`ActiveGroups.activeWeight`. -/
def partialWeight (𝔊 : ActiveGroups) (q₀ : ℝ) (t : 𝔊.Index → ℕ)
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (U : Finset 𝔊.Index) (n : ℕ) : ℂ :=
  ((q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, (if g ∈ U then 0 else t g)) *
      ∏ g : 𝔊.Index, (if g ∈ U then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) : ℝ) : ℂ) *
    ∑ 𝔭 ∈ partialLists 𝔊 t U n, test 𝔭

/-- `H_marks(n) = 𝒲(n) W_𝐭^𝐛(n)` (`[P-06:0567]`), with the marks of the groups in `U` removed. -/
def hMarks (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups)
    (t : 𝔊.Index → ℕ) (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (U : Finset 𝔊.Index)
    (n : ℕ) : ℂ :=
  ((markedWeight q 𝔞 x n : ℝ) : ℂ) * partialWeight 𝔊 q₀ t test U n

/-- The primes of the inert bands and of the active groups ("`p` in all groups",
`[P-06:0608, 0625]`). -/
def markPrimes {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups) : Finset ℕ :=
  (Finset.univ.biUnion fun i : Fin K => bandPrimes (𝔞.exponent i) x) ∪ 𝔊.allPrimes

/-- `ω_tot(n)`: the number of hits in all active and inert groups (`[P-06:0613]`). -/
def totalMarkHits {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups) (n : ℕ) : ℕ :=
  (∑ i : Fin K, primeHits (bandPrimes (𝔞.exponent i) x) n) + 𝔊.totalHits n

/-! ### Divisor models -/

/-- The divisor sum `H_0(n) = ∑_{d' ∣ n} A_{d'}` (`[P-06:0573]`). -/
def divisorSum (A : ℕ → ℂ) (n : ℕ) : ℂ := ∑ e ∈ n.divisors, A e

/-- The support and size conditions (cor:divisor-model) (`[P-06:0572–0577]`) on the coefficients
of a divisor model: `d' ≤ exp(Csupp L^{.47})`, all prime divisors of `d'` in the set `primes` (the
active and inert groups), and `∑_{d'} |A_{d'}| / d' ≤ L^{C₈}`. -/
structure IsDivisorModel (x Csupp C₈ : ℝ) (primes : Finset ℕ) (A : ℕ → ℂ) : Prop where
  /-- `d' ≥ 1` and `d' ≤ exp(O(L^{.47}))` -/
  size : ∀ e : ℕ, A e ≠ 0 → 0 < e ∧ (e : ℝ) ≤ Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))
  /-- the prime divisors of `d'` belong to the active or inert groups -/
  primes_mem : ∀ e : ℕ, A e ≠ 0 → ∀ p : ℕ, p.Prime → p ∣ e → p ∈ primes
  /-- `∑_{d'} |A_{d'}| / d' ≤ L^{C₈}` -/
  mass : ∑ e ∈ Finset.Icc 1 ⌊Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))⌋₊, ‖A e‖ / (e : ℝ) ≤
    Real.log x ^ C₈

/-! ### Ranges, polynomials, convolutions -/

/-- The integers `n` with `a ≤ n ≤ b`. The dyad `n ≍ R` is `natIcc R (2 * R)`. -/
def natIcc (a b : ℝ) : Finset ℕ := Finset.Icc ⌈a⌉₊ ⌊b⌋₊

theorem mem_natIcc {a b : ℝ} (hb : 0 ≤ b) {n : ℕ} :
    n ∈ natIcc a b ↔ a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b := by
  unfold natIcc
  rw [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hb]

/-- The normalized Dirichlet polynomial `R^{-1} ∑_{n ∈ s} c_n n^{it}`. -/
def normPoly (R : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  (R : ℂ)⁻¹ * ∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)

/-- A finite set of primes that contains every prime between two of its members. -/
def IsPrimeInterval (J : Finset ℕ) : Prop :=
  (∀ p ∈ J, p.Prime) ∧ ∀ p₁ ∈ J, ∀ p₂ ∈ J, ∀ p : ℕ, p.Prime → p₁ ≤ p → p ≤ p₂ → p ∈ J

/-- The Dirichlet convolution `(1_G * c)(w) = ∑_{p ∈ G, p ∣ w} c(w / p)`. -/
def primeConv (G : Finset ℕ) (c : ℕ → ℂ) (w : ℕ) : ℂ := ∑ p ∈ G.filter (fun p => p ∣ w), c (w / p)

/-- The slot statistic with repeated slot primes allowed (`[P-06:0695–0697]`):
`#{(l_1, …, l_d) ∈ ∏ S_i : l_1 ⋯ l_d ∣ u}`. For no slot it is `1`. -/
def slotCountRep {d : ℕ} (S : Fin d → Finset ℕ) (u : ℕ) : ℕ :=
  ((Fintype.piFinset S).filter fun 𝔩 => (∏ i, 𝔩 i) ∣ u).card

/-- The slots `S_2, …, S_d`. -/
def tailSlots {d : ℕ} (S : Fin (d + 1) → Finset ℕ) : Fin d → Finset ℕ := fun i => S i.succ

/-- `C_x ≥ 0`. -/
theorem slotMass_nonneg {d : ℕ} (S : Fin d → Finset ℕ) : 0 ≤ slotMass S := by
  unfold slotMass
  exact Finset.sum_nonneg fun 𝔩 _ => div_nonneg zero_le_one (Nat.cast_nonneg _)

/-- A sequence with a factor `ψ₁(w / Y)`, `supp ψ₁ ⊆ [a₁, a₂] ⊂ (0, ∞)`, lives on
`1 ≤ w ≤ a₂ Y`. -/
theorem cutoff_mem {ψ₁ : ℝ → ℂ} {a₁ a₂ Y : ℝ} (ha₁ : 0 < a₁)
    (hsupp : Function.support ψ₁ ⊆ Set.Icc a₁ a₂) (hY : 0 < Y) {w : ℕ}
    (hw : ψ₁ ((w : ℝ) / Y) ≠ 0) : w ∈ Finset.Icc 1 ⌊a₂ * Y⌋₊ := by
  have h : (w : ℝ) / Y ∈ Set.Icc a₁ a₂ := hsupp hw
  have hle : (w : ℝ) ≤ a₂ * Y := (div_le_iff₀ hY).mp h.2
  have hge : a₁ * Y ≤ (w : ℝ) := (le_div_iff₀ hY).mp h.1
  have hpos : (0 : ℝ) < (w : ℝ) := lt_of_lt_of_le (mul_pos ha₁ hY) hge
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hpos
    exact lt_irrefl _ hpos
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hw0, Nat.le_floor hle⟩

namespace EndpointConfig

variable {d : ℕ}

/-- **The hypotheses of (cor:SM) on a configuration at `x`** (those of `EndpointEnergyAt`): the
groups and the slots are admissible; `x exp(2 L^{.39} - c₁) ≤ Y ≤ x exp(c₂ L^{.46} log L)`
(`[P-06:0385–0389]`); `1 ≤ t_g ≤ m'` with `t_g = 1` on small groups; `|𝐛| ≤ 1` depending only on
big marks (`[P-06:0403–0405, 0683–0684]`); `|σ| ≤ L^{Cσ}`; `ψ₁` smooth, supported in `[a₁, a₂]`,
with derivatives bounded by `L^{Dψ j}` (`[P-06:0641–0642]`). -/
structure Admissible (D : EndpointData) (x : ℝ) (c : EndpointConfig d) : Prop where
  groups : c.𝔊.Admissible D.P x
  slots : SlotsAdmissible D.ε x c.S
  scale_ge : x * Real.exp (2 * Real.log x ^ (0.39 : ℝ) - D.c₁) ≤ c.Y
  scale_le : c.Y ≤ x * Real.exp (D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x))
  marks : ∀ g, 1 ≤ c.t g ∧ c.t g ≤ D.m'
  smallMarks : ∀ i : Fin c.𝔊.numSmall, c.t (Sum.inl i) = 1
  test_le : ∀ 𝔭, ‖c.test 𝔭‖ ≤ 1
  test_big : ∀ 𝔭 𝔭' : (g : c.𝔊.Index) → Fin (c.t g) → ℕ,
    (∀ j : Fin c.𝔊.numBig, 𝔭 (Sum.inr j) = 𝔭' (Sum.inr j)) → c.test 𝔭 = c.test 𝔭'
  twist : |c.σ| ≤ Real.log x ^ D.Cσ
  cutoff_smooth : ContDiff ℝ ∞ c.ψ₁
  cutoff_support : Function.support c.ψ₁ ⊆ Set.Icc D.a₁ D.a₂
  cutoff_deriv : ∀ (j : ℕ) (u : ℝ), ‖iteratedDeriv j c.ψ₁ u‖ ≤ Real.log x ^ D.Dψ j

/-- The first endpoint `𝒰` of (cor:U-form) (`[P-06:0635–0640]`). -/
def endpoint (c : EndpointConfig d) (D : EndpointData) (x : ℝ) : ℕ → ℂ :=
  comparisonEndpoint D.q D.q₀ D.𝔞 x c.𝔊 c.S c.t c.test c.ψ₁ c.σ c.Y

/-- The chosen small group `𝒫_{g_s}` (`[P-06:0683]`). -/
def smallGroup (c : EndpointConfig d) (i₀ : Fin c.𝔊.numSmall) : Finset ℕ :=
  c.𝔊.group (Sum.inl i₀)

/-- The coefficient of the constant part after the small mark of `g_s` has been removed
(`[P-06:0713–0715]`): "the remaining marked weight times `𝒲(n)`",
`W_{𝐭 - 𝐞_{g_s}}^{𝐛}(n) 𝒲(n)`. -/
def constCoeff (c : EndpointConfig d) (D : EndpointData) (x : ℝ) (i₀ : Fin c.𝔊.numSmall)
    (n : ℕ) : ℂ :=
  hMarks D.q D.q₀ D.𝔞 x c.𝔊 c.t c.test {Sum.inl i₀} n

/-- (cor:u-coefficient) (`[P-06:0705–0712]`): the coefficient on `u` of the tuple part,
`W_{𝐭 - 𝐞_{g_s}}^{𝐛}(u) 𝒲(u) ∑_{l_2, …, l_d} 1_{l_2 ⋯ l_d ∣ u}`, repeated slot primes allowed.
"For `d = 1` the final factor is one." -/
def tupleCoeff (c : EndpointConfig (d + 1)) (D : EndpointData) (x : ℝ) (i₀ : Fin c.𝔊.numSmall)
    (u : ℕ) : ℂ :=
  (slotCountRep (tailSlots c.S) u : ℂ) * c.constCoeff D x i₀ u

/-- The constant part with the small mark extracted, `w = p_s n` (`[P-06:0713–0715]`):
`ψ₁(w/Y) w^{iσ} V_{g_s}^{-1} ∑_{p_s ∈ 𝒫_{g_s}, p_s ∣ w} W_{𝐭 - 𝐞}^{𝐛}(w/p_s) 𝒲(w/p_s)`. -/
def constEndpoint (c : EndpointConfig d) (D : EndpointData) (x : ℝ) (i₀ : Fin c.𝔊.numSmall)
    (w : ℕ) : ℂ :=
  c.ψ₁ ((w : ℝ) / c.Y) * (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) *
    (((reciprocalMass (c.smallGroup i₀))⁻¹ : ℝ) : ℂ) *
      primeConv (c.smallGroup i₀) (c.constCoeff D x i₀) w

/-- The tuple part with the small mark extracted and repeated slot primes allowed,
`w = p_s p_l u` with `p_l = l_1` in the first slot (`[P-06:0705–0712]`):
`ψ₁(w/Y) w^{iσ} V_{g_s}^{-1} ∑_{p_s ∈ 𝒫_{g_s}} ∑_{l_1 ∈ S_1, p_s l_1 ∣ w} c(w / (p_s l_1))` with
`c` the coefficient (cor:u-coefficient). -/
def tupleEndpoint (c : EndpointConfig (d + 1)) (D : EndpointData) (x : ℝ)
    (i₀ : Fin c.𝔊.numSmall) (w : ℕ) : ℂ :=
  c.ψ₁ ((w : ℝ) / c.Y) * (w : ℂ) ^ ((c.σ : ℂ) * Complex.I) *
    (((reciprocalMass (c.smallGroup i₀))⁻¹ : ℝ) : ℂ) *
      primeConv (c.smallGroup i₀) (primeConv (c.S 0) (c.tupleCoeff D x i₀)) w

/-- The coefficient error of the extraction (`[P-06:0692–0703]`):
`𝒰 - (𝒰_tuple - C_x 𝒰_const)`. It vanishes unless the square of a prime of `𝒫_{g_s}` or of a slot
divides `w` (`ExtractedCoefficientIdentity`). -/
def errEndpoint (c : EndpointConfig (d + 1)) (D : EndpointData) (x : ℝ)
    (i₀ : Fin c.𝔊.numSmall) (w : ℕ) : ℂ :=
  c.endpoint D x w - c.tupleEndpoint D x i₀ w +
    ((slotMass c.S : ℝ) : ℂ) * c.constEndpoint D x i₀ w

/-- `𝒰 = 𝒰_tuple - C_x 𝒰_const + 𝒰_err`. -/
theorem endpoint_eq (c : EndpointConfig (d + 1)) (D : EndpointData) (x : ℝ)
    (i₀ : Fin c.𝔊.numSmall) (w : ℕ) :
    c.endpoint D x w = c.tupleEndpoint D x i₀ w -
      ((slotMass c.S : ℝ) : ℂ) * c.constEndpoint D x i₀ w + c.errEndpoint D x i₀ w := by
  unfold errEndpoint
  ring

theorem endpoint_eq_zero (c : EndpointConfig d) (D : EndpointData) (x : ℝ) {w : ℕ}
    (h : c.ψ₁ ((w : ℝ) / c.Y) = 0) : c.endpoint D x w = 0 := by
  unfold endpoint comparisonEndpoint
  rw [h, zero_mul, zero_mul, zero_mul]

theorem constEndpoint_eq_zero (c : EndpointConfig d) (D : EndpointData) (x : ℝ)
    (i₀ : Fin c.𝔊.numSmall) {w : ℕ} (h : c.ψ₁ ((w : ℝ) / c.Y) = 0) :
    c.constEndpoint D x i₀ w = 0 := by
  unfold constEndpoint
  rw [h, zero_mul, zero_mul, zero_mul]

theorem tupleEndpoint_eq_zero (c : EndpointConfig (d + 1)) (D : EndpointData) (x : ℝ)
    (i₀ : Fin c.𝔊.numSmall) {w : ℕ} (h : c.ψ₁ ((w : ℝ) / c.Y) = 0) :
    c.tupleEndpoint D x i₀ w = 0 := by
  unfold tupleEndpoint
  rw [h, zero_mul, zero_mul, zero_mul]

theorem errEndpoint_eq_zero (c : EndpointConfig (d + 1)) (D : EndpointData) (x : ℝ)
    (i₀ : Fin c.𝔊.numSmall) {w : ℕ} (h : c.ψ₁ ((w : ℝ) / c.Y) = 0) :
    c.errEndpoint D x i₀ w = 0 := by
  unfold errEndpoint
  rw [c.endpoint_eq_zero D x h, c.tupleEndpoint_eq_zero D x i₀ h,
    c.constEndpoint_eq_zero D x i₀ h, mul_zero, sub_zero, add_zero]

end EndpointConfig

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
