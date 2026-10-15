module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The proof of [S] Theorem 3.5, step 1: replacing the root by independent residues

Source: `verification/stage7-sources/S-02.tex`, lines 210–314 (`[S-02:0210–0314]`).

## Objects

* `pathFactor` — the factor (eq:path-residue-factor) [S-02:0226–0231] by which a path with active
  label sets `Λ_i` and offsets `h_i` depends on the position; it is defined for every position
  model, in particular for integer positions and for residue positions.
* `intAvg`, `resAvg` — the average over `I ∩ ℤ` and the expectation under independent uniform
  residues.
* `residueMoment` — the moment `⟨u, (𝒜 𝒜*)^R u⟩` in the independent residue model *with the return
  condition `h_N = 0`* [S-02:0293–0308]: the reviewed `physMoment` for the position model
  `tagModel` (residues at all group primes together with the integer offset), started at offset
  `0` and averaged over the residues.
* `phaseVec`, `phaseSum` — "the unrestricted signed path expression" with the phase `e(θ h_N)`
  of (eq:return-fourier) [S-02:0308–0313]: the same expression with the final vector `u` replaced
  by the vector `φ_θ = e(θ · offset)` on the physical states, so that no return condition is
  imposed.

Both `residueMoment` and `phaseSum` are built from the reviewed operators `physOp`, `physAdj`;
only the position model is new. Lemma 3.4 holds for it: `schur_bound` is proved for every position
model.

## Statements

* `UniformResidueReplacement` — [S] Lemma 3.6 (`lem:transference-crt`) [S-02:0236–0242].
* `ResidueReduction` — the conclusion "we may therefore use the independent residue model"
  [S-02:0293–0307]: the averaged moment and `residueMoment` differ by at most `L^{-A'N}`.
* `ResidueSummation` — the implication from the first to the second (summation over paths with
  absolute coefficients, using Lemma 3.4, which is proved).
* `ReturnFourier` — (eq:return-fourier) in the form in which it is used: "it suffices to bound the
  unrestricted signed path expression uniformly in `θ`" [S-02:0308–0313].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### The path factor -/

open _root_.Classical in
/-- **The factor (eq:path-residue-factor)** [S-02:0226–0231] of a path with `n` edges, active
label sets `Λ_0, …, Λ_n` and offsets `h_0, …, h_n`, at the position `pos`:
`∏_{i=0}^{n} (∏_{p ∈ Λ_i} 1_{p ∣ pos + h_i}) · q_i^{#{p ∈ Q ∖ Λ_i : p ∣ pos + h_i}}`,
where `Q` is the set of all group primes and `q_0 = q_n = √q`, `q_i = q` otherwise.
"Divides" and "`+`" are those of the position model `𝔭`. -/
def pathFactor (𝔭 : PosModel) (Q : Finset ℕ) (q : ℝ) (n : ℕ) (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ)
    (pos : 𝔭.Pos) : ℝ :=
  ∏ i ∈ Finset.range (n + 1),
    if ∀ p ∈ Λ i, 𝔭.hit p (𝔭.shift (h i) pos) then
      visitQ q n i ^ countHits (fun p => 𝔭.hit p (𝔭.shift (h i) pos)) (Q \ Λ i)
    else 0

/-- The average over `I ∩ ℤ`, `I = [X, 2X)`, of a function of the integer position. -/
def intAvg (X : ℝ) (f : ℤ → ℝ) : ℝ :=
  ((intWindow X).card : ℝ)⁻¹ * ∑ n ∈ intWindow X, f n

/-- `averagedMoment` is the window average of the integer-position moments. -/
theorem averagedMoment_eq_intAvg {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B]
    [DecidableEq S] [DecidableEq B] (𝔊 : PrimeGroups P x S B) {J : ℕ} {N : Type} [Fintype N]
    (𝔉 : N → Pattern 𝔊.big J P.ℓ) (k : ℤ) (ζ : ℝ) (X : ℝ) :
    averagedMoment 𝔊 𝔉 k ζ X =
      intAvg X fun n => physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ (transferR (Real.log x)) n :=
  rfl

/-! ### The residue model with the return condition -/

section Raw

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type} [Fintype N]

/-- The integer offset of a position of `tagModel Q`. -/
def tagOffset {Q : Finset ℕ} (n : (tagModel Q).Pos) : ℤ := (show ℤ × ResVec Q from n).1

/-- **The moment in the independent residue model, with the return condition**
[S-02:0293–0308]: `E_y ⟨u_{(0,y)}, (𝒜 𝒜*)^R u_{(0,y)}⟩`, where the position is the pair of the
integer offset and the residues at all group primes, `y` is uniform, and `u_{(0,y)}` is one on the
physical states at that position. Returning to `(0, y)` is the condition `h_N = 0`. -/
def residueMoment (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (R : ℕ) : ℝ :=
  resAvg 𝒢.allPrimes fun y => physMoment (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ R (tagStart y)

open _root_.Classical in
/-- The phase vector `φ_θ`: `e(θ h)` on every physical state at a position with offset `h`, and
zero elsewhere. It is the sum over all offsets `h` and residues `y'` of `e(θ h) u_{(h, y')}`. -/
def phaseVec (θ : ℝ) : PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ → ℂ :=
  fun s => if IsPhys (tagModel 𝒢.allPrimes) s.1 s.2 then expUnit (θ * (tagOffset s.1 : ℝ)) else 0

/-- **The unrestricted signed path expression with the phase `e(θ h_N)`** [S-02:0308–0313]:
`E_y ⟨u_{(0,y)}, (𝒜 𝒜*)^R φ_θ⟩`, where `φ_θ` is `e(θ h)` on the physical states at offset `h`.
The walks start at offset `0` and end anywhere; a walk ending at offset `h_N` carries the phase
`e(θ h_N)`. -/
def phaseSum (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (R : ℕ) (θ : ℝ) : ℂ :=
  ((Fintype.card (ResVec 𝒢.allPrimes) : ℝ) : ℂ)⁻¹ *
    ∑ y : ResVec 𝒢.allPrimes,
      pairUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y)
        (((physOp (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ *
            physAdj (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ) ^ R) (phaseVec 𝒢 θ))

end Raw

/-! ### Lemma 3.6 -/

/-- **The conclusion of Lemma 3.6 for fixed constants** `(P, J, γ, A)`: for all sufficiently large
`x`, every system of prime groups, all sets `Λ_0, …, Λ_N` of group primes with at most `M s`
elements (`M = J + ℓ`, `s` the number of groups), all integer offsets `h_0 = 0, h_1, …, h_N` and
every window `I = [X, 2X)` with `x^γ ≤ X ≤ x^{1/γ}`: the average over `I ∩ ℤ` of
(eq:path-residue-factor) differs from its expectation `E` under independent uniform residues by
at most `exp(-A N T) · E` (`T = log L`). -/
def ResidueReplacementBound (P : GroupParams) (J : ℕ) (γ A : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ),
      (∀ i, Λ i ⊆ 𝔊.allPrimes) → (∀ i, (Λ i).card ≤ (J + P.ℓ) * groupCount S B) → h 0 = 0 →
      ∀ X : ℝ, x ^ γ ≤ X → X ≤ x ^ (1 / γ) →
        |intAvg X (fun n => pathFactor intPos 𝔊.allPrimes P.q
              (Graph.sourceMemoryLength (Real.log x)) Λ h n) -
            resAvg 𝔊.allPrimes (pathFactor (resModel 𝔊.allPrimes) 𝔊.allPrimes P.q
              (Graph.sourceMemoryLength (Real.log x)) Λ h)| ≤
          Real.exp (-(A * (Graph.sourceMemoryLength (Real.log x) : ℝ) *
              Real.log (Real.log x))) *
            resAvg 𝔊.allPrimes (pathFactor (resModel 𝔊.allPrimes) 𝔊.allPrimes P.q
              (Graph.sourceMemoryLength (Real.log x)) Λ h)

/-- **[S] Lemma 3.6 (uniform residue replacement, `lem:transference-crt`)** [S-02:0236–0242].

"For each compatible fixed path and every fixed `A > 0`, the average of (eq:path-residue-factor)
over `I ∩ ℤ` equals its expectation under independent uniform residues at all group primes,
multiplied by `1 + O(exp(-ANT))`. Incompatible active congruences give zero in both models."

Quantifiers: `P, J, γ > 0, A > 0 ⟶ x₀ ⟶ x`, groups, the path, `X`. The threshold is uniform in
the path: the application [S-02:0303–0307] sums the error over all paths, and the constants in
the proof [S-02:0244–0291] depend on the path only through `N`, `M s` and the group data. The
`O`-constant is absorbed in `A` (the statement is for every `A`). Only the active label sets and
the offsets of the path enter, so the statement is for arbitrary sets `Λ_i` of at most `M s`
group primes (`|Λ_i| = M s` for the paths of the expansion) and arbitrary offsets; the proof uses
no more [S-02:0245–0249]. In the incompatible case both sides vanish and the inequality reads
`0 ≤ 0`. -/
def UniformResidueReplacement : Prop :=
  ∀ (P : GroupParams) (J : ℕ) (γ A : ℝ), 0 < γ → 0 < A → ResidueReplacementBound P J γ A

/-! ### The reduction to the residue model -/

/-- **The reduction to the independent residue model for fixed constants** [S-02:0293–0307]: for
all sufficiently large `x`, every system of prime groups, every admissible pattern family and `k`,
every `ζ` and every window: the averaged moment (eq:transference-moment) and the moment of the
independent residue model (with the return condition) differ by at most `L^{-A'N}`. -/
def ResidueReductionBound (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ γ A' : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      ∀ X : ℝ, x ^ γ ≤ X → X ≤ x ^ (1 / γ) →
        |averagedMoment 𝔊 𝔉 k ζ X -
            residueMoment 𝔊.toGroupFamily P.q 𝔉 k ζ (transferR (Real.log x))| ≤
          Real.log x ^ (-(A' * (Graph.sourceMemoryLength (Real.log x) : ℝ)))

/-- **"We may therefore use the independent residue model"** [S-02:0293–0307].

"This replacement may be summed over paths with absolute coefficients. … By Lemma 3.4, the
absolute mass of all length `N` paths, even without a return condition, is `L^{O(N)}`. Taking `A`
sufficiently large in Lemma 3.6 makes the summed error smaller than `L^{-A'N}` for any desired
fixed `A'`."

Quantifiers: `P, m, C₁, J, C₂, γ > 0, A' ⟶ x₀`. -/
def ResidueReduction : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ γ A' : ℝ), 0 < γ →
    ResidueReductionBound P m C₁ J C₂ γ A'

/-- **The summation over paths** [S-02:0212–0234, 0293–0307]: Lemma 3.6 implies the reduction to
the residue model. What the implication contains: the expansion of the moment into paths, for
integer positions and for `tagModel` (the same paths and the same position-independent
coefficients; the position enters through (eq:path-residue-factor) only); the bound
(eq:initial-factorial-mass); and Lemma 3.4 for residue positions, which is the proved
`schur_bound` for the position model `tagModel`. -/
def ResidueSummation : Prop := UniformResidueReplacement → ResidueReduction

/-! ### The return condition -/

/-- **(eq:return-fourier), as it is used** [S-02:0308–0313]: "the return condition is now imposed
by the exact identity `1_{h_N = 0} = ∫_0^1 e(θ h_N) dθ`. It suffices to bound the unrestricted
signed path expression uniformly in `θ`."

For every family of groups, every pattern family and all parameters: if `|phaseSum θ| ≤ ε` for all
real `θ`, then `|residueMoment| ≤ ε`. The statement is exact (no threshold) and holds for raw
families: the offset of a walk takes finitely many values, the residue vector of a walk which
returns to offset `0` returns to its start, and `residueMoment` is the real part of the `θ`-mean
of `phaseSum`. -/
def ReturnFourier : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (q : ℝ) (J ℓ : ℕ) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (R : ℕ) (ε : ℝ),
    (∀ θ : ℝ, ‖phaseSum 𝒢 q 𝔉 k ζ R θ‖ ≤ ε) → |residueMoment 𝒢 q 𝔉 k ζ R| ≤ ε

/-! ### Lemma 3.4 in the residue model with offsets -/

/-- **Lemma 3.4 for the residue model with offsets** (`schur_bound` for the position model
`tagModel`): "the same assertion holds if the position is replaced by independent uniform
residues at all group primes" [S-02:0138–0139]. This is the bound used in [S-02:0303–0304]. -/
theorem tag_schur_bound (P : GroupParams) (m : ℕ) (C₁ : ℝ) {J : ℕ} {C₂ : ℝ} {x : ℝ}
    (hx : 0 < Real.log x) {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (𝔊 : PrimeGroups P x S B) {N : Type} [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ) (ζ : ℝ)
    (k : ℤ) (hadm : Admissible (Real.log x) m C₁ C₂ 𝔉 k)
    (s : PState (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily J P.ℓ) :
    physAbsRowSum (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily P.q 𝔉 k ζ s ≤
        Real.log x ^ schurExponent P m C₁ ∧
      physAbsColSum (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily P.q 𝔉 k ζ s ≤
        Real.log x ^ schurExponent P m C₁ :=
  schur_bound P m C₁ hx 𝔊 (tagModel 𝔊.allPrimes) 𝔉 ζ k hadm s

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
