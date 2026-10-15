module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.Main
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The proof of [S] Theorem 3.5: residues, visit parameters and fixed constants

Source: `verification/stage7-sources/S-02.tex` (`[S-02:…]`), the proof of Theorem 3.5,
lines 188–1258. This file fixes the scalar objects which the whole proof uses.

* `Res p`, `ResVec Q`, `resModel Q`, `tagModel Q` — residues modulo the group primes and two
  position models (`PosModel`) built from them: "independent uniform residues at all group
  primes" [S-02:0236–0242, 0293–0296] and the same model with the integer offset `h_i` of the
  path as an additional coordinate, which is what the return condition `h_N = 0` of
  (eq:return-fourier) [S-02:0308–0311] refers to.
* `visitQ`, `visitEta` — `q_0 = q_N = √q`, `q_i = q` for `0 < i < N`, `η_i = 1 - q_i`
  [S-02:0223–0224, 0318].
* `lifeBaseline`, `tiltLaw`, `baselineProd` — `b_p`, `μ̃_g(p)` of (eq:lifespan-baseline) and the
  common baseline `∏_{p big} b_p` [S-02:0318–0325]. These are `Graph.primeLifespanBaseline` and
  `Graph.tiltedPrimeGroupLaw` for the visits `0, …, N` and the coefficients `η_i`.
* `memRho`, `memV` — the constants `ρ` ("choose `ρ ∈ (0,1)` with `ρ² > √q`", [S-02:0442–0443]) and
  `v` of (eq:memory-weight-choice) [S-02:0686–0693].
* `memCutoff`, `omissionNumber` — `B = ⌈L²⌉` of (eq:memory-truncation) [S-02:0797–0800] and
  `𝒟 = C(M, ℓ)^{|𝒮|}` of (eq:small-omission-number) [S-02:0833–0836].

## Choices

* **Residues.** `Res p = ZMod (p - 1 + 1)`. For `p ≥ 1` this is `ℤ/pℤ` (`Res.card`,
  `Res.intCast_eq_zero_iff`); it is a finite commutative ring for every `p`, so no primality
  hypothesis is needed to sum over residues. The reviewed `residuePos` uses `ZMod p`; for the
  groups of Definition 3.1 the two are the same ring.
* **`ρ`.** The paper allows any `ρ ∈ (0,1)` with `ρ² > √q`; here `ρ = q^{1/8}`, written
  `√√√q` (`memRho_pos`, `memRho_lt_one`, `sqrt_lt_memRho_sq`).
* **`v`.** The weight `v > 1` is the one supplied by `GroupParams.exists_ghost_weight`
  (= `Graph.exists_source_ghost_uniform_weight`) for this `ρ`; its defining property is
  `memV_spec`. It depends only on the constants of Definition 3.1.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Residues -/

/-- `ℤ/pℤ` as a type which is a finite commutative ring for every natural number `p`:
`ZMod (p - 1 + 1)`. For `p ≥ 1`, in particular for a prime, `p - 1 + 1 = p`. -/
abbrev Res (p : ℕ) : Type := ZMod (p - 1 + 1)

/-- `Res p` has `p` elements when `p ≥ 1`. -/
theorem Res.card (p : ℕ) (hp : 0 < p) : Fintype.card (Res p) = p := by
  rw [ZMod.card, Nat.sub_add_cancel hp]

/-- The class of the integer `a` in `Res p` vanishes if and only if `p ∣ a` (`p ≥ 1`). -/
theorem Res.intCast_eq_zero_iff (p : ℕ) (hp : 0 < p) (a : ℤ) :
    ((a : Res p) = 0) ↔ (p : ℤ) ∣ a := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.sub_add_cancel hp]

/-- A vector of residues: one residue `y_p ∈ ℤ/pℤ` for every `p ∈ Q`. With the uniform
probability measure this is the Haar probability measure of `∏_{p ∈ Q} ℤ/pℤ`
[S-02:0294–0296, 0397–0398]. -/
abbrev ResVec (Q : Finset ℕ) : Type := (p : {p : ℕ // p ∈ Q}) → Res p.1

/-- **Residue positions**: the position is a vector of residues at the primes of `Q`; `p` divides
the position `y` when `p ∈ Q` and `y_p = 0`; translation by `h` translates every residue. For
`Q = 𝒢.allPrimes` this is "independent uniform residues at all group primes" [S-02:0238–0240]
(the reviewed `residuePos`, with `Res p` in place of `ZMod p`). -/
def resModel (Q : Finset ℕ) : PosModel where
  Pos := ResVec Q
  hit q y := ∃ h : q ∈ Q, y ⟨q, h⟩ = 0
  shift h y := fun p => y p + (h : Res p.1)
  shift_neg_shift h y := by
    funext p
    simp

/-- **Residue positions with the integer offset**: a position is a pair `(h, y)` of an integer
offset and a residue vector. Divisibility only reads `y`; translation by `d` maps `(h, y)` to
`(h + d, y + d)`. A walk which starts at `(0, y)` ends at `(h_N, y + h_N)`, so "return to the
start" is the condition `h_N = 0` of the paper [S-02:0216–0222, 0308–0311], which the residue
vector alone does not see. -/
def tagModel (Q : Finset ℕ) : PosModel where
  Pos := ℤ × ResVec Q
  hit q n := ∃ h : q ∈ Q, n.2 ⟨q, h⟩ = 0
  shift h n := (n.1 + h, fun p => n.2 p + (h : Res p.1))
  shift_neg_shift h n := by
    refine Prod.ext ?_ ?_
    · simp
    · funext p
      simp

/-- The start `(0, y)` of a walk in `tagModel Q`. -/
def tagStart {Q : Finset ℕ} (y : ResVec Q) : (tagModel Q).Pos := ((0 : ℤ), y)

/-- The expectation `E_y f(y)` for independent uniform residues `y_p`, `p ∈ Q`
[S-02:0238–0240]. -/
def resAvg (Q : Finset ℕ) (f : ResVec Q → ℝ) : ℝ :=
  (Fintype.card (ResVec Q) : ℝ)⁻¹ * ∑ y, f y

theorem resAvg_const (Q : Finset ℕ) (c : ℝ) : resAvg Q (fun _ => c) = c := by
  have hne : (Fintype.card (ResVec Q) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold resAvg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hne]

theorem resAvg_mono (Q : Finset ℕ) {f g : ResVec Q → ℝ} (h : ∀ y, f y ≤ g y) :
    resAvg Q f ≤ resAvg Q g := by
  unfold resAvg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => h y)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-! ### Visits -/

/-- `q_i`: "put `q_0 = q_N = √q` and `q_i = q` for `0 < i < N`" [S-02:0223–0224]. Here `n = N` is
the number of edges and `i` the visit. -/
def visitQ (q : ℝ) (n i : ℕ) : ℝ := if i = 0 ∨ i = n then Real.sqrt q else q

/-- `η_i = 1 - q_i` [S-02:0318]. -/
def visitEta (q : ℝ) (n i : ℕ) : ℝ := 1 - visitQ q n i

theorem visitQ_eq (q : ℝ) (n i : ℕ) : visitQ q n i = q ∨ visitQ q n i = Real.sqrt q := by
  unfold visitQ
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem visitEta_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n i : ℕ) : 0 ≤ visitEta q n i := by
  have h := (Graph.source_ghost_visit_range q (visitQ q n i) hq0 hq1 (visitQ_eq q n i)).2.1
  unfold visitEta
  linarith

theorem visitEta_le_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n i : ℕ) : visitEta q n i ≤ 1 := by
  have h := (Graph.source_ghost_visit_range q (visitQ q n i) hq0 hq1 (visitQ_eq q n i)).1
  unfold visitEta
  linarith

/-- `b_p = 1 - p⁻¹ ∑_{i=0}^{N} η_i` of (eq:lifespan-baseline) [S-02:0319–0322]:
`Graph.primeLifespanBaseline` for the visits `0, …, n` and the coefficients `η_i`. -/
def lifeBaseline (q : ℝ) (n p : ℕ) : ℝ :=
  Graph.primeLifespanBaseline (Finset.range (n + 1)) (visitEta q n) p

/-- `μ̃_g(p) = 1 / (V_g p b_p)` of (eq:lifespan-baseline) [S-02:0319–0322] for the group `s = 𝒫_g`:
`Graph.tiltedPrimeGroupLaw` for the visits `0, …, n` and the coefficients `η_i`. -/
def tiltLaw (s : Finset ℕ) (q : ℝ) (n p : ℕ) : ℝ :=
  Graph.tiltedPrimeGroupLaw s (Finset.range (n + 1)) (visitEta q n) p

/-- The common baseline `∏_{p ∈ Q} b_p`; with `Q` the set of all big primes this is the factor
"`∏_{p big} b_p ≤ 1`" extracted from every path sum [S-02:0324–0325]. -/
def baselineProd (Q : Finset ℕ) (q : ℝ) (n : ℕ) : ℝ := ∏ p ∈ Q, lifeBaseline q n p

theorem lifeBaseline_le_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n p : ℕ) :
    lifeBaseline q n p ≤ 1 :=
  Graph.prime_lifespan_baseline_le_one _ _ p fun i _ => visitEta_nonneg hq0 hq1 n i

/-! ### The constants `ρ`, `v`, `B`, `𝒟` -/

theorem sqrt_lt_one_of {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : Real.sqrt t < 1 := by
  by_contra h
  have h' : 1 ≤ Real.sqrt t := not_lt.mp h
  have h2 := Real.sq_sqrt h0
  nlinarith [mul_le_mul h' h' zero_le_one (Real.sqrt_nonneg t)]

theorem lt_sqrt_of {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : t < Real.sqrt t := by
  by_contra h
  have h' : Real.sqrt t ≤ t := not_lt.mp h
  have hs := Real.sqrt_nonneg t
  have h2 := Real.sq_sqrt h0.le
  have ha : Real.sqrt t * Real.sqrt t ≤ t * Real.sqrt t := mul_le_mul_of_nonneg_right h' hs
  have hb : t * Real.sqrt t ≤ t * t := mul_le_mul_of_nonneg_left h' h0.le
  have hc : t * t < t := by nlinarith
  nlinarith

/-- **The constant `ρ`** [S-02:0442–0443]: "choose `ρ ∈ (0,1)` with `ρ² > √q`". Here
`ρ = √√√q = q^{1/8}`, so `ρ² = q^{1/4} > q^{1/2}`. -/
def memRho (P : GroupParams) : ℝ := Real.sqrt (Real.sqrt (Real.sqrt P.q))

theorem memRho_pos (P : GroupParams) : 0 < memRho P :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr P.q_pos))

theorem memRho_lt_one (P : GroupParams) : memRho P < 1 := by
  have h1 : Real.sqrt P.q < 1 := sqrt_lt_one_of P.q_pos.le P.q_lt_one
  have h2 : Real.sqrt (Real.sqrt P.q) < 1 := sqrt_lt_one_of (Real.sqrt_nonneg _) h1
  exact sqrt_lt_one_of (Real.sqrt_nonneg _) h2

/-- `ρ² > √q`. -/
theorem sqrt_lt_memRho_sq (P : GroupParams) : Real.sqrt P.q < memRho P ^ 2 := by
  have h1 : Real.sqrt P.q < 1 := sqrt_lt_one_of P.q_pos.le P.q_lt_one
  unfold memRho
  rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
  exact lt_sqrt_of (Real.sqrt_pos.mpr P.q_pos) h1

/-- **The Schur weight `v > 1` of (eq:memory-weight-choice)** [S-02:0686–0693], "chosen large
enough that, for both possible `q_i`, `q_i/ρ² + 2 max(1, v₊) η_i / (ρ v) < 1`". It is the weight
given by `GroupParams.exists_ghost_weight` for `ρ = memRho P`; "the same choice works when every
original ghost birth receives an extra factor two". -/
def memV (P : GroupParams) : ℝ :=
  _root_.Classical.choose (P.exists_ghost_weight (memRho_pos P) (sqrt_lt_memRho_sq P))

/-- The defining property of `v` (the conclusion of `GroupParams.exists_ghost_weight`). -/
theorem memV_spec (P : GroupParams) :
    1 < memV P ∧ ∀ qi V γ : ℝ,
      (qi = P.q ∨ qi = Real.sqrt P.q) → 0 ≤ V → V ≤ P.vPlus → 0 ≤ γ → γ ≤ 2 →
      0 ≤ Graph.sourceGhostA qi (memRho P) ∧
      Graph.sourceGhostA qi (memRho P) + |Graph.sourceGhostD qi (memRho P)| / memV P < 1 ∧
      Graph.sourceGhostA qi (memRho P) +
        |γ * Graph.sourceGhostC V qi (memRho P)| / memV P < 1 ∧
      |Graph.sourceGhostD qi (memRho P)| ≤ 1 / memRho P ∧
      |γ * Graph.sourceGhostC V qi (memRho P)| ≤ 2 * max 1 P.vPlus / memRho P :=
  _root_.Classical.choose_spec (P.exists_ghost_weight (memRho_pos P) (sqrt_lt_memRho_sq P))

theorem one_lt_memV (P : GroupParams) : 1 < memV P := (memV_spec P).1

/-- **The memory truncation `B = ⌈L²⌉`** of (eq:memory-truncation) [S-02:0797–0800]. -/
def memCutoff (L : ℝ) : ℕ := Nat.ceil (L ^ 2)

/-- **`𝒟 = C(M, ℓ)^{|𝒮|}`**, `M = J + ℓ`, of (eq:small-omission-number) [S-02:0833–0836]: the
number of choices of the `ℓ` omitted small labels in all small groups. -/
def omissionNumber (S : Type) [Fintype S] (J ℓ : ℕ) : ℕ := ((J + ℓ).choose ℓ) ^ Fintype.card S

theorem omissionNumber_pos (S : Type) [Fintype S] (J ℓ : ℕ) : 0 < omissionNumber S J ℓ :=
  pow_pos (Nat.choose_pos (Nat.le_add_left ℓ J)) _

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
