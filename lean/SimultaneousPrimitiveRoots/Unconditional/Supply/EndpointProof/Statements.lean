module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Objects
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ClassicalInputs

/-!
# The intermediate results of the proof of (cor:SM) ([P] §6)

(cor:SM) (`[P-06:0544–0550]`) is `EndpointEnergyPaper d` of `Supply/TwoSided.lean`; with the data
bundled as in `EndpointProof/Objects.lean` it is `EndpointEnergyBundled d`. Its proof is
`[P-06:0555–0925]` (`verification/stage7-sources/P-06.tex`). This file states the intermediate
results of that proof, one `def … : Prop` for each; `EndpointProof/Assembly.lean` proves the chain
from them to `EndpointEnergy (d + 1)`.

A *node* is an estimate; a *link* is a `def XLink`-like implication that appears as a field of
`EndpointLeaves` (the statement that one step of the manuscript works). The number of slots is
`d` in the low-frequency part and `d + 1` (a first slot and `d` further ones) in the
high-frequency part; `d + 1 = 1` is the case needed downstream.

## The plan of `[P-06:0555–0562]`

"At low Mellin frequencies, a finite divisor model makes the centering in `F_x` cancel the main
term. At high frequencies, one small-prime mark supplies a polynomial that is small outside a
sparse set of times. On that sparse set we treat the positive tuple sum and its subtracted
constant separately: the tuple sum has a long-prime factor, whereas the constant term requires
cancellation on the divisor progressions of the finite model."

* Low frequencies (`[P-06:0563–0679]`): `OmegaMoment` → `DivisorModel`; `LowMainTerm`;
  `SlotMassBounded`; the link to `LowFrequencyBound`.
* Extraction (`[P-06:0681–0715]`): `ExtractSmallIdentity`, `ExtractedCoefficientIdentity`,
  `PartialMarkedBound`, `CoefficientBound`, `ExtractionErrorBound`.
* Separation (`[P-06:0717–0754]`): the links `TupleProductBound → TupleEnergy` and
  `ConstantProductBound → ConstantEnergy`.
* Exceptional times (`[P-06:0756–0832]`): `PrimePowerNorm` → `ExceptionalCount`; `SparseBound`.
* The tuple part (`[P-06:0834–0858]`): `LongPrimeSaving`; the link to `TupleProductBound`.
* The constant part (`[P-06:0860–0925]`): `ModelPolynomialMedium`, `ModelPolynomialHigh`; the link
  to `ConstantProductBound`.
* `ScaleFacts`: the relations between `Y`, `T₀` and `L` used by the assembly.

## The order of the constants

`C₆` is part of the fixed data. `C₈` and the support constant of the divisor model, the exponent of
`PartialMarkedBound`/`CoefficientBound`, and the costs of the separation depend on the fixed data
only. For a saving `A`: the thresholds `A_s` (small polynomial) and `A_l` (long prime) are chosen
inside `TupleProductBound`/`ConstantProductBound`, then the low-time exponent `B'` (it exceeds the
retained shifts, the threshold `B₀` of `LongPrimeSaving`, and `2 C₁₇ + A`), then the precision `N`
of the divisor model ("choosing `N` last", `[P-06:0873–0876]`). The low-frequency bound is then
used with this `B'` and with a precision chosen after `B'` (`[P-06:0678–0679]`: "Choosing `N`
after `B'`"). The threshold for `x` is always last.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology ContDiff

noncomputable section

/-! ### (cor:SM) and its two ranges of times -/

/-- **(cor:SM) with bundled data** (`[P-06:0544–0550]`): for every fixed `A' > 0`,
`∫_{|t| ≤ T_0} |Y^{-1} ∑_w 𝒰(w) e(hw/k) w^{it}|² dt ≪_{A'} L^{-A'}`, `T_0 = x L^{C_6 + 1}`,
`k ≤ L^{C_6}`, uniformly in the admissible configurations, in `k` and in `h`. It is
`EndpointEnergyAt d C₆ (C₆ + 1)` for the data `D` (`endpointEnergyPaper_of_bundled`). -/
def EndpointEnergyBundled (d : ℕ) : Prop :=
  ∀ D : EndpointData, ∀ A : ℝ, 0 < A → ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ c : EndpointConfig d, c.Admissible D x →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ D.C₆ → ∀ h : ℤ,
        ∫ τ in (-(timeBound D x))..(timeBound D x),
          ‖endpointPolynomial (c.endpoint D x) c.Y h k τ‖ ^ 2 ≤ M * Real.log x ^ (-A)

/-- **Low Mellin frequencies** (`[P-06:0643–0644]`, proved in `[P-06:0646–0679]`): "For every
fixed `B' > 0`, we claim uniformly for `|t| ≤ L^{B'}` that the normalized sum in (cor:SM) saves
any prescribed log power."

Order: the fixed data, `B'`, the saving `N`; then `M`, `x₀`. The bound is pointwise in `τ`, and
uniform in the configuration, in `k ≤ L^{C₆}` and in `h` (not necessarily coprime to `k`: the main
terms cancel "including the complete residue average", `[P-06:0678]`). -/
def LowFrequencyBound (d : ℕ) : Prop :=
  ∀ D : EndpointData, ∀ B' N : ℝ, 0 < B' → 0 < N → ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ c : EndpointConfig d, c.Admissible D x →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ D.C₆ → ∀ (h : ℤ) (τ : ℝ),
        |τ| ≤ Real.log x ^ B' →
          ‖endpointPolynomial (c.endpoint D x) c.Y h k τ‖ ≤ M * Real.log x ^ (-N)

/-- **High Mellin frequencies** (`[P-06:0681–0925]`): for every saving `A` there is a low-time
exponent `B'` such that the energy of the times `L^{B'} ≤ |τ| ≤ T_0` is `≪ L^{-A}`.

Order: the fixed data, `A`; then `B'`; then `M`, `x₀`. (`B'` is "enlarged" several times in the
manuscript, `[P-06:0733–0737, 0846, 0899]`; the form `HighEnergyLe` is monotone in it.) -/
def HighFrequencyBound (d : ℕ) : Prop :=
  ∀ D : EndpointData, ∀ A : ℝ, 0 < A → ∃ B' : ℝ, 0 < B' ∧ ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ c : EndpointConfig d, c.Admissible D x →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ D.C₆ → ∀ h : ℤ,
        HighEnergyLe (endpointPolynomial (c.endpoint D x) c.Y h k)
          (Real.log x ^ B') (timeBound D x) (M * Real.log x ^ (-A))

/-! ### Bookkeeping -/

/-- **`C_x = O_ε(1)`** (`[P-06:0079]`: "The harmonic prime estimates give `C_x = O_ε(1)`"; used at
`[P-06:0651, 0670]`), uniformly in the admissible slot systems. For `d = 1` it is proved
(`slotMassBounded_one` in `EndpointProof/SlotMass.lean`). -/
def SlotMassBounded (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S → slotMass S ≤ B

/-- **The scales** (`[P-06:0385–0389, 0549, 0703, 0765–0769]`). For large `x` and every scale
`x exp(2 L^{.39} - c₁) ≤ Y ≤ x exp(c₂ L^{.46} log L)`: `L > 1`; `Y > 0`; `T₀ = x L^{C₆+1} ≤ Y`
("`T_0 / Y = L / H = o(1)`"); and `4 N (1 + log N) ≤ Cs · Y · L` for `N = ⌊a₂ Y⌋`, the length term
of the mean-value theorem (`log Y ≪ L` because `Y = x^{1 + o(1)}`).

These are the only asymptotic facts used by the assembly itself. -/
def ScaleFacts : Prop :=
  ∀ D : EndpointData, ∃ Cs x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Y : ℝ,
    x * Real.exp (2 * Real.log x ^ (0.39 : ℝ) - D.c₁) ≤ Y →
    Y ≤ x * Real.exp (D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) →
      1 < Real.log x ∧ 0 < Y ∧ timeBound D x ≤ Y ∧
        4 * (⌊D.a₂ * Y⌋₊ : ℝ) * (1 + Real.log (⌊D.a₂ * Y⌋₊ : ℝ)) ≤ Cs * Y * Real.log x

/-! ### The divisor model and low frequencies -/

/-- **(cor:omega-moment)** (`[P-06:0621–0630]`): "For any fixed `B > 1`, expanding `B^{ω_tot}`
into squarefree divisors and counting their multiples gives
`∑_{n ≍ R} B^{ω_tot(n)} ≪ R ∏_{p in all groups} (1 + (B-1)/p) ≪ R L^{C(B)}`. Indeed only divisors
at most a constant times `R` can occur, and each has `O(R/d)` multiples in the dyad."

Order: the bands, the active-group constants, `B`; then `C`, `M`, `x₀` (the threshold depends on
the bands: they must be pairwise disjoint and disjoint from the active groups, and of mass
`≤ 1`); then `x`, the groups, and every `R ≥ 1` (no upper bound for `R` is needed). `B = 1` is
allowed. -/
def OmegaMoment : Prop :=
  ∀ (K : ℕ) (𝔞 : MarkingArray K) (P : ActiveGroupConstants) (B : ℝ), 1 ≤ B →
    ∃ C M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ 𝔊 : ActiveGroups, 𝔊.Admissible P x →
      ∀ R : ℝ, 1 ≤ R →
        ∑ n ∈ natIcc R (2 * R), B ^ totalMarkHits 𝔞 x 𝔊 n ≤ M * R * Real.log x ^ C

/-- **Lemma `lem:divisor-model`, the truncated divisor model** (`[P-06:0565–0585]`, proof
`[P-06:0587–0633]`): "Let `H_marks(n) = 𝒲(n) W_𝐭^𝐛(n)`, where `0 ≤ t_g ≤ m'` for fixed `m'` and
`|𝐛| ≤ 1`. In particular, zero values of `t_g` are allowed; these occur when a small mark is
removed below. There is a divisor sum `H_0(n) = ∑_{d' ∣ n} A_{d'}`, `d' ≤ exp(O(L^{.47}))`,
`∑_{d'} |A_{d'}| / d' ≤ L^{C_8}`, whose prime divisors all belong to the active or inert groups,
such that, on every positive integer dyad `n ≍ R`,
`∑_{n ≍ R} |H_marks(n) - H_0(n)|² ≪_N R L^{-N}` for every fixed `N`. The assertion is uniform in
the bounded tuple test `𝐛`, with no regularity assumption on that test."

Order: the dampings, the bands, the active-group constants, `m'`; then the support constant and
`C₈`; then the precision `N`; then `M`, `x₀`; then `x`, the groups, the marks `t_g ≤ m'`, the
test, the set `U` of groups whose marks are removed; then the coefficients `A`. In the manuscript
the model (truncation after `h_0 = ⌊L^{.01}⌋` additional primes) does not depend on `N`; here `A`
may depend on `N`, which is all that is used, but `Csupp` and `C₈` may not. The dyad is
`R ≤ n ≤ 2R`, for every `R ≥ 1`. -/
def DivisorModel : Prop :=
  ∀ q q₀ : ℝ, 0 < q → q < 1 → 0 < q₀ → q₀ < 1 →
    ∀ (K : ℕ) (𝔞 : MarkingArray K) (P : ActiveGroupConstants) (m' : ℕ),
      ∃ Csupp C₈ : ℝ, ∀ N : ℝ, 0 < N → ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∀ 𝔊 : ActiveGroups, 𝔊.Admissible P x → ∀ t : 𝔊.Index → ℕ, (∀ g, t g ≤ m') →
          ∀ test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ, (∀ 𝔭, ‖test 𝔭‖ ≤ 1) →
            ∀ U : Finset 𝔊.Index, ∃ A : ℕ → ℂ,
              IsDivisorModel x Csupp C₈ (markPrimes 𝔞 x 𝔊) A ∧
                ∀ R : ℝ, 1 ≤ R →
                  ∑ n ∈ natIcc R (2 * R),
                      ‖hMarks q q₀ 𝔞 x 𝔊 t test U n - divisorSum A n‖ ^ 2 ≤
                    M * R * Real.log x ^ (-N)

/-- **(cor:low-main-term)** (`[P-06:0652–0667]`): "For a fixed divisor `d'`, all primes in `l d'`
exceed `k` for large `x`, so `gcd(l d', k) = 1`. Smooth sum–integral comparison on the
progressions modulo `k` gives

`(1/Y) ∑_{v ≥ 1} ψ_1(l d' v / Y) (l d' v)^{i(t+σ)} e(h l d' v / k)
  = (1/(l d')) ((1/k) ∑_{a mod k} e(ha/k)) ∫_0^∞ ψ_1(z) (Yz)^{i(t+σ)} dz + O(Y^{-1} L^{C(B')})`.

… The error follows by summing the endpoint and total-variation errors over `k` residue classes;
all derivative and modulus costs are fixed log powers."

Here `m = l d'` is any positive integer coprime to `k`, and the display is multiplied by `Y`. The
bound is uniform in `m` and in `Y > 0` (the total variation of `v ↦ ψ_1(mv/Y)(mv)^{iu}` does not
depend on them); the manuscript's remark "The sum has scale `Y/(l d') ≥ x^{ε - o(1)}`" is not
needed for the statement. Order: the support of the cutoff, the exponents `D₀, D₁` (for `ψ_1` and
`ψ_1'`), `Cσ`, `C₆`, `B'`; then `C`, `M`, `x₀`. -/
def LowMainTerm : Prop :=
  ∀ a₁ a₂ : ℝ, 0 < a₁ → a₁ ≤ a₂ → ∀ D₀ D₁ Cσ C₆ B' : ℝ,
    ∃ C M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Y : ℝ, 0 < Y →
      ∀ ψ₁ : ℝ → ℂ, ContDiff ℝ ∞ ψ₁ → Function.support ψ₁ ⊆ Set.Icc a₁ a₂ →
        (∀ u : ℝ, ‖ψ₁ u‖ ≤ Real.log x ^ D₀) → (∀ u : ℝ, ‖deriv ψ₁ u‖ ≤ Real.log x ^ D₁) →
      ∀ σ τ : ℝ, |σ| ≤ Real.log x ^ Cσ → |τ| ≤ Real.log x ^ B' →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ C₆ → ∀ (h : ℤ) (m : ℕ), 0 < m → m.Coprime k →
        ‖(∑ᶠ v : ℕ, ψ₁ (((m * v : ℕ) : ℝ) / Y) *
                ((m * v : ℕ) : ℂ) ^ (((τ + σ : ℝ) : ℂ) * Complex.I) *
              addChar ((h : ℝ) * ((m * v : ℕ) : ℝ) / (k : ℝ))) -
            ((Y : ℂ) / (m : ℂ) *
              ((k : ℂ)⁻¹ * ∑ a ∈ Finset.range k, addChar ((h : ℝ) * (a : ℝ) / (k : ℝ))) *
              ∫ z in a₁..a₂, ψ₁ z * ((Y * z : ℝ) : ℂ) ^ (((τ + σ : ℝ) : ℂ) * Complex.I))‖ ≤
          M * Real.log x ^ C

/-! ### The extraction of a small-prime mark -/

/-- **(cor:extract-small)** (`[P-06:0683–0692]`): "Choose a small group `g_s`. It has
`t_{g_s} = 1` in every comparison, and the tuple test depends only on big marks. Except when a
prime of this group divides `w` twice,
`W_𝐭^𝐛(w) = V_{g_s}^{-1} ∑_{p_s ∣ w, p_s ∈ 𝒫_{g_s}} W_{𝐭 - 𝐞_{g_s}}^𝐛(w / p_s)`.
This follows directly by removing the represented small prime; the remaining damping exponent is
unchanged."

An exact identity, for pairwise disjoint groups of primes, `t_{g_s} = 1`, a test that does not
depend on the mark of `g_s`, and `w ≥ 1` not divisible by the square of a prime of `𝒫_{g_s}`; no
condition on `q₀`. Checked with exact arithmetic on small cases (`sm_agent/check_extract*.py`). -/
def ExtractSmallIdentity : Prop :=
  ∀ 𝔊 : ActiveGroups, (∀ g : 𝔊.Index, ∀ p ∈ 𝔊.group g, p.Prime) →
    (∀ g g' : 𝔊.Index, g ≠ g' → Disjoint (𝔊.group g) (𝔊.group g')) →
    ∀ (q₀ : ℝ) (t : 𝔊.Index → ℕ) (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ)
      (i₀ : Fin 𝔊.numSmall), t (Sum.inl i₀) = 1 →
      (∀ 𝔭 𝔭' : (g : 𝔊.Index) → Fin (t g) → ℕ,
        (∀ g : 𝔊.Index, g ≠ Sum.inl i₀ → 𝔭 g = 𝔭' g) → test 𝔭 = test 𝔭') →
      ∀ w : ℕ, 0 < w → (∀ p ∈ 𝔊.group (Sum.inl i₀), ¬ p ^ 2 ∣ w) →
        𝔊.activeWeight q₀ t test w =
          (((reciprocalMass (𝔊.group (Sum.inl i₀)))⁻¹ : ℝ) : ℂ) *
            primeConv (𝔊.group (Sum.inl i₀)) (partialWeight 𝔊 q₀ t test {Sum.inl i₀}) w

/-- **The extracted coefficients are exact away from squares** (`[P-06:0692–0715]`): "In the
positive tuple part we may also allow repeated slot primes: the extra terms have a square of a
prime at least `x^ε` dividing `w` … In the tuple part factor `w = p_s p_l u`, where `p_l = l_1`
lies in the first long-prime slot. After allowing repeated slots the coefficient on `u` is exactly
(cor:u-coefficient) … In the constant part write `w = p_s n`; its coefficient is just the
remaining marked weight times `𝒲(n)`."

An exact identity: if the groups and the slots consist of primes, the groups are pairwise
disjoint, the slots are disjoint from all marked primes and the bands from the active groups,
`t_{g_s} = 1` and the test depends only on big marks, then `𝒰_err(w) = 0` for every `w ≥ 1` not
divisible by the square of a prime of `𝒫_{g_s}` or of a slot. (For an admissible configuration the
disjointness hypotheses hold for large `x`.) Checked with exact arithmetic on small cases, with
one, two and three slots, overlapping slots included. -/
def ExtractedCoefficientIdentity (d : ℕ) : Prop :=
  ∀ (D : EndpointData) (x : ℝ) (c : EndpointConfig (d + 1)) (i₀ : Fin c.𝔊.numSmall),
    (∀ g : c.𝔊.Index, ∀ p ∈ c.𝔊.group g, p.Prime) →
    (∀ g g' : c.𝔊.Index, g ≠ g' → Disjoint (c.𝔊.group g) (c.𝔊.group g')) →
    (∀ i, ∀ l ∈ c.S i, l.Prime) →
    (∀ i, Disjoint (c.S i) (markPrimes D.𝔞 x c.𝔊)) →
    (∀ j : Fin D.K, Disjoint (bandPrimes (D.𝔞.exponent j) x) c.𝔊.allPrimes) →
    c.t (Sum.inl i₀) = 1 →
    (∀ 𝔭 𝔭' : (g : c.𝔊.Index) → Fin (c.t g) → ℕ,
      (∀ j : Fin c.𝔊.numBig, 𝔭 (Sum.inr j) = 𝔭' (Sum.inr j)) → c.test 𝔭 = c.test 𝔭') →
    ∀ w : ℕ, 0 < w → (∀ p ∈ c.smallGroup i₀, ¬ p ^ 2 ∣ w) → (∀ i, ∀ l ∈ c.S i, ¬ l ^ 2 ∣ w) →
      c.errEndpoint D x i₀ w = 0

/-- **(cor:marked-bound) with marks removed** (`[P-06:0044–0053]`): "For every fixed `m'`,
`|W_𝐭^𝐛(n)| ≤ W_𝐭(n) ≤ L^{C(m')}` (`t_g ≤ m'`, `|𝐛| ≤ 1`). … Indeed, each factor
`q_0^{u-t} (u)_t / V_g^t`, for `u ≥ t`, is bounded by a constant depending only on `m', q_0, v_-`,
and there are `O(log L)` factors." With the marks of `U` removed the factor of `g ∈ U` is
`q_0^{ω_g(n)} ≤ 1` (`[P-06:0692]`: "Both sides are bounded by fixed log powers").

Order as in `TwoSidedProof.MarkedBound` (the case `U = ∅`): `P`, `q₀`, `m'`; then `C`, `x₀`.
`t_g = 0` and `n = 0` are allowed. -/
def PartialMarkedBound : Prop :=
  ∀ (P : ActiveGroupConstants) (q₀ : ℝ), 0 < q₀ → q₀ < 1 → ∀ m' : ℕ, ∃ C x₀ : ℝ,
    ∀ x : ℝ, x₀ ≤ x → ∀ 𝔊 : ActiveGroups, 𝔊.Admissible P x →
      ∀ t : 𝔊.Index → ℕ, (∀ g, t g ≤ m') →
        ∀ test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ, (∀ 𝔭, ‖test 𝔭‖ ≤ 1) →
          ∀ (U : Finset 𝔊.Index) (n : ℕ), ‖partialWeight 𝔊 q₀ t test U n‖ ≤ Real.log x ^ C

/-- **The extracted coefficients are bounded by a fixed log power** (`[P-06:0712–0713]`: "This
is bounded by a fixed log power times a fixed divisor power"; `[P-06:0697–0698]`: "Slot
multiplicities at each `w ≍ Y` remain bounded"). On `1 ≤ u ≤ x²` (all scales of the proof are
below `x²`) the slot multiplicity is `≤ (2/ε)^d`, `𝒲` is bounded for fixed `K, q` (Mertens), and
the remaining marked weight is `≤ L^C` (`PartialMarkedBound`), so no divisor power is needed.

Order: the fixed data; then `C`, `x₀`. -/
def CoefficientBound (d : ℕ) : Prop :=
  ∀ D : EndpointData, ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ c : EndpointConfig (d + 1), c.Admissible D x → ∀ (i₀ : Fin c.𝔊.numSmall) (u : ℕ),
      1 ≤ u → (u : ℝ) ≤ x ^ (2 : ℝ) →
        ‖c.constCoeff D x i₀ u‖ ≤ Real.log x ^ C ∧ ‖c.tupleCoeff D x i₀ u‖ ≤ Real.log x ^ C

/-- **The coefficient error of the extraction** (`[P-06:0692–0703]`): "The square exceptions have
relative count at most `L^{O(1)} exp(-L^{.27})` on the relevant dyads. … the extra terms have a
square of a prime at least `x^ε` dividing `w`, a relative count `O(x^{-ε})`. … Indeed their
squared coefficient norm is at most `Y L^{O(1)} (exp(-L^{.27}) + x^{-ε})`."

Stated with an arbitrary log saving: `∑_w |𝒰_err(w)|² ≤ M Y L^{-A}`, for every choice of the small
group. Order: the fixed data, `A`; then `M`, `x₀`. The passage to the integrated square over
`|t| ≤ T_0` ("Lemma `lem:moment-bounds`, applied to these coefficient errors", with
`T_0 / Y = o(1)`) is done in the assembly with the mean-value theorem of
`Classical/DirichletMeanSquare.lean`. -/
def ExtractionErrorBound (d : ℕ) : Prop :=
  ∀ D : EndpointData, ∀ A : ℝ, 0 < A → ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ c : EndpointConfig (d + 1), c.Admissible D x → ∀ i₀ : Fin c.𝔊.numSmall,
      ∑ w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊, ‖c.errEndpoint D x i₀ w‖ ^ 2 ≤
        M * c.Y * Real.log x ^ (-A)

/-! ### The two extracted parts at high frequencies -/

/-- **The tuple part at high times** (`[P-06:0705–0712, 0834–0858]`): for every saving `A` there
is `B'` with `∫_{L^{B'} ≤ |τ| ≤ T_0} |Y^{-1} ∑_w 𝒰_tuple(w) e(hw/k) w^{iτ}|² dτ ≪ L^{-A}`, for
every choice of the small group. "Together with the ordinary-time estimate this handles the tuple
part." -/
def TupleEnergy (d : ℕ) : Prop :=
  ∀ D : EndpointData, ∀ A : ℝ, 0 < A → ∃ B' : ℝ, 0 < B' ∧ ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ c : EndpointConfig (d + 1), c.Admissible D x → ∀ i₀ : Fin c.𝔊.numSmall,
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ D.C₆ → ∀ h : ℤ,
        HighEnergyLe (endpointPolynomial (c.tupleEndpoint D x i₀) c.Y h k)
          (Real.log x ^ B') (timeBound D x) (M * Real.log x ^ (-A))

/-- **The constant part at high times** (`[P-06:0713–0715, 0860–0925]`): the same for
`𝒰_const` (the factor `C_x = O(1)` is put back in the assembly). "Equations
(cor:constant-model-error), (cor:constant-medium-integral), and (cor:constant-high) complete the
constant-term estimate." -/
def ConstantEnergy (d : ℕ) : Prop :=
  ∀ D : EndpointData, ∀ A : ℝ, 0 < A → ∃ B' : ℝ, 0 < B' ∧ ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ c : EndpointConfig (d + 1), c.Admissible D x → ∀ i₀ : Fin c.𝔊.numSmall,
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ D.C₆ → ∀ h : ℤ,
        HighEnergyLe (endpointPolynomial (c.constEndpoint D x i₀) c.Y h k)
          (Real.log x ^ B') (timeBound D x) (M * Real.log x ^ (-A))

/-! ### Products of normalized polynomials at a common time -/

/-- **The tuple products** (`[P-06:0739–0752, 0763–0772, 0834–0858]`): "It remains to treat
products of normalized polynomials at a common time, with `L^{B'} ≤ |t| ≤ 2T_0`. In every such
product there is a small-prime factor `P_s(t) = P^{-1} ∑_{p_s ≍ P, p_s ∈ 𝒫_{g_s}} b_s(p_s)
p_s^{it}`, `c L^{.27} ≤ log P ≤ L^{.36}` … In the tuple part the remaining factors are a
long-prime polynomial `P_l(t)` and a polynomial `R(t)` at scales `N_l` and
`R_0 ≍ Y / (P N_l) ≥ x^{ε - o(1)}`."

For every saving `A` there is `B'` such that, for all large `x`, every product `P_s P_l R` has
energy `≤ M L^{-A}` on `L^{B'} ≤ |t| ≤ 2 T_0`, where
* `P_s(t) = P^{-1} ∑_{p ∈ G, P ≤ p ≤ 2P} b(p) p^{it}` for a finite set of primes `G`, a dyad
  `exp(L^{.27})/2 ≤ P ≤ exp(L^{.36})` and coefficients `|b| ≤ 1` ("The coefficients include
  residue restrictions and retained twists"; the normalization `|b_s| ≤ L^{C_{12}}` of the
  manuscript is moved to the constants);
* `P_l(t) = N_l^{-1} ∑_{l ∈ J} χ(l) l^{it}` for an interval of primes `J ⊆ [N_l, 2N_l]`,
  `x^ε / 2 ≤ N_l ≤ x^{1-ε}`, and a character `χ` modulo `k ≤ L^{C₆}`;
* `R(t) = R_0^{-1} ∑_{R_0 ≤ u ≤ (4a₂/a₁) R_0} c_u u^{it}` with `R_0 = a₁ Y / (4 P N_l)` (the range
  of `u` forced by `a₁ Y ≤ p l u ≤ a₂ Y`) and arbitrary coefficients `|c_u| ≤ L^{C_R}`.

Order: `ε`, the support of the cutoff, `c₁, c₂`, `C₆`, the exponent `C_R`; then `A`; then `B'`;
then `M`, `x₀`. Nothing else about the small group or the coefficient is used: the ordinary times
`|P_s| ≤ L^{-A_s}` are handled by the mean square of the collapsed `P_l R` (length
`≍ Y/P ≫ T_0`, (cor:length-dominates-time)), the exceptional unit intervals by
`ExceptionalCount`, `LongPrimeSaving` and `SparseBound`. For `ε > 1/2` the range of `N_l` is
empty for large `x`. -/
def TupleProductBound : Prop :=
  ∀ ε a₁ a₂ c₁ c₂ C₆ CR : ℝ, 0 < ε → 0 < a₁ → a₁ ≤ a₂ → 0 < C₆ → ∀ A : ℝ, 0 < A →
    ∃ B' : ℝ, 0 < B' ∧ ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ Y : ℝ, x * Real.exp (2 * Real.log x ^ (0.39 : ℝ) - c₁) ≤ Y →
        Y ≤ x * Real.exp (c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) →
      ∀ G : Finset ℕ, (∀ p ∈ G, p.Prime) →
      ∀ P : ℝ, Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P →
        P ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) →
      ∀ b : ℕ → ℂ, (∀ p, ‖b p‖ ≤ 1) →
      ∀ Nl : ℝ, x ^ ε / 2 ≤ Nl → Nl ≤ x ^ (1 - ε) →
      ∀ J : Finset ℕ, IsPrimeInterval J → (∀ l ∈ J, Nl ≤ (l : ℝ) ∧ (l : ℝ) ≤ 2 * Nl) →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ C₆ → ∀ χ : DirichletCharacter ℂ k,
      ∀ cR : ℕ → ℂ, (∀ u, ‖cR u‖ ≤ Real.log x ^ CR) →
        HighEnergyLe
          (fun t => normPoly P (G ∩ natIcc P (2 * P)) b t *
            normPoly Nl J (fun l => χ (l : ZMod k)) t *
            normPoly (a₁ * Y / (4 * P * Nl))
              (natIcc (a₁ * Y / (4 * P * Nl)) (a₂ * Y / (P * Nl))) cR t)
          (Real.log x ^ B') (2 * (x * Real.log x ^ (C₆ + 1))) (M * Real.log x ^ (-A))

/-- **The constant products** (`[P-06:0753–0754, 0763–0772, 0860–0925]`): "In the constant part
the remaining polynomial `N(t)` has scale `R_0 ≍ Y/P`."

For every saving `A` there is `B'` such that, for all large `x`, every product `P_s N` has energy
`≤ M L^{-A}` on `L^{B'} ≤ |t| ≤ 2T_0`, where `P_s` is as in `TupleProductBound` for the chosen
small group and `N(t) = R_0^{-1} ∑_{R_0 ≤ n ≤ (2a₂/a₁) R_0, n ≡ a (k)} c(n) n^{it}` with
`R_0 = a₁ Y / (2P)` and `c(n) = W_{𝐭 - 𝐞_{g_s}}^𝐛(n) 𝒲(n)` (`[P-06:0862]`: "Keep its
residue-class restriction separately"). The residue `a` is arbitrary (`n` need not be a unit,
`[P-06:0721–0722]`).

Here the coefficient is the specific one: the exceptional times need the cancellation of the
divisor model. Order: the fixed data, `A`; then `B'`; then `M`, `x₀`. -/
def ConstantProductBound (d : ℕ) : Prop :=
  ∀ D : EndpointData, ∀ A : ℝ, 0 < A → ∃ B' : ℝ, 0 < B' ∧ ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ c : EndpointConfig (d + 1), c.Admissible D x → ∀ i₀ : Fin c.𝔊.numSmall,
      ∀ P : ℝ, Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P →
        P ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) →
      ∀ b : ℕ → ℂ, (∀ p, ‖b p‖ ≤ 1) →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ D.C₆ → ∀ a : ℕ,
        HighEnergyLe
          (fun t => normPoly P (c.smallGroup i₀ ∩ natIcc P (2 * P)) b t *
            normPoly (D.a₁ * c.Y / (2 * P)) (natIcc (D.a₁ * c.Y / (2 * P)) (D.a₂ * c.Y / P))
              (fun n => if n ≡ a [MOD k] then c.constCoeff D x i₀ n else 0) t)
          (Real.log x ^ B') (2 * timeBound D x) (M * Real.log x ^ (-A))

/-! ### Exceptional times -/

/-- **The factorial coefficient estimate** (`[P-06:0781–0789]`): "we use the factorial
prime-polynomial coefficient estimate, as in [Soundararajan 2009, Lemma 3 and its proof] …
Unique factorization gives squared coefficient norm for `P_s^{j_0}` at most
`j_0! (P^{-2} ∑_{p_s ≍ P} |b_s(p_s)|²)^{j_0}`."

Exact form, without normalization: for a finite set of primes `G`, coefficients `b` and `j ≥ 0`,
the coefficient of `n` in `(∑_{p ∈ G} b_p p^{it})^j` is `∑_{(p_1,…,p_j) ∈ G^j, p_1 ⋯ p_j = n}
∏ b_{p_i}`, and the sum of the squares of these coefficients is `≤ j! (∑_{p ∈ G} |b_p|²)^j`
(Cauchy–Schwarz; an integer has at most `j!` representations as an ordered product of `j`
primes). `j = 0` gives `1 ≤ 1`. Primality is needed. -/
def PrimePowerNorm : Prop :=
  ∀ G : Finset ℕ, (∀ p ∈ G, p.Prime) → ∀ (b : ℕ → ℂ) (j : ℕ),
    ∑ n ∈ (Fintype.piFinset fun _ : Fin j => G).image (fun f => ∏ i, f i),
        ‖∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
            ∏ i, b (f i)‖ ^ 2 ≤
      (j.factorial : ℝ) * (∑ p ∈ G, ‖b p‖ ^ 2) ^ j

/-- **(cor:exceptional-count)** (`[P-06:0774–0801]`): "Let `𝒥` be the integer unit intervals
meeting `{|t| ≤ 2T_0 : |P_s(t)| > L^{-A_s}}`. Then
`|𝒥| ≤ exp(O(L^{.36} + L^{.73} log L)) ≤ exp(O(L^{.9}))`. … Select a point exceeding the
threshold from each occupied interval, and split their integer indices modulo three to get
separated sets. … The separated-point mean-square bound of Lemma `lem:moment-bounds` therefore
gives `|𝒥| ≪ Z L^{O(1)} j_0! (L^{C_{13} + 2A_s} / P)^{j_0}`. Since `Z P^{-j_0} ≤ 2P 2^{j_0}` and
`j_0 = O(L^{.73})`, taking logarithms proves (cor:exceptional-count)."

Stated for separated points: for every `A_s` and all large `x`, a set of reals `|t| ≤ x²` with
pairwise distances `≥ 1` at which `|P_s(t)| > L^{-A_s}` has at most `exp(L^{.9})` elements
(the implied constant is absorbed for large `x`). `P_s` is as in `TupleProductBound`: any finite
set of primes `G`, `exp(L^{.27})/2 ≤ P ≤ exp(L^{.36})`, `|b| ≤ 1`. The lower bound for `P` gives
`j_0 = O(L^{.73})`, the upper bound the factor `2P`; `2T_0 + 1 ≤ x²`. -/
def ExceptionalCount : Prop :=
  ∀ As : ℝ, 0 < As → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ G : Finset ℕ, (∀ p ∈ G, p.Prime) →
    ∀ P : ℝ, Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P →
      P ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) →
    ∀ b : ℕ → ℂ, (∀ p, ‖b p‖ ≤ 1) →
    ∀ 𝒯 : Finset ℝ, (∀ t ∈ 𝒯, |t| ≤ x ^ (2 : ℝ)) →
      (∀ t ∈ 𝒯, ∀ t' ∈ 𝒯, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ 𝒯, Real.log x ^ (-As) < ‖normPoly P (G ∩ natIcc P (2 * P)) b t‖) →
        (𝒯.card : ℝ) ≤ Real.exp (Real.log x ^ (0.9 : ℝ))

/-- **(cor:sparse-bound)** (`[P-06:0803–0832]`): "We will also use the following sparse bound for
any normalized polynomial `R(t) = ∑_{n ≍ R_0} c_n n^{it}` with `x^{ε/2} ≤ R_0 ≤ x^2` and
`∑ |c_n|² ≤ L^{C_{14}} / R_0`: `∑_{I ∈ 𝒥} sup_{t ∈ I} |R(t)|² ≪ L^{C_{15}}`. Choose maximizing
points and again split into three separated classes. For `1 ≤ |Δ| ≤ T_mod := exp(L / (log L)^2)`,
sum–integral comparison on the full integer dyad gives `R_0^{-1} |∑_{n ≍ R_0} n^{iΔ}| ≪
|Δ|^{-1} + x^{-c_ε}`. For larger differences, Lemma `lem:log-phase` gives
`O(exp(-L / (log L)^{C_{16}}))` instead. … The Gram matrix of the vectors `(n^{it_i})_{n ≍ R_0}`
consequently has absolute row sum `≪ R_0 (1 + log(2T_0) + |𝒥| {x^{-c_ε} + exp(-L/(log
L)^{C_{16}})}) ≪ R_0 L`."

Stated for separated points and in a homogeneous form: for `x^δ ≤ R_0 ≤ x^2`, arbitrary
coefficients on `R_0 ≤ n ≤ ρ R_0`, and a set `𝒯` of reals `|t| ≤ 2x³` with pairwise distances
`≥ 1` and at most `2 exp(L^{.9})` elements,
`∑_{t ∈ 𝒯} |R(t)|² ≤ M L · R_0^{-1} ∑_n |c_n|²` for the normalized polynomial
`R(t) = R_0^{-1} ∑ c_n n^{it}`. The differences are `≤ 4x³`, the range of `lem:log-phase`.
Order: `δ`, `ρ`; then `M`, `x₀`. -/
def SparseBound : Prop :=
  ∀ δ ρ : ℝ, 0 < δ → 1 ≤ ρ → ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ R₀ : ℝ, x ^ δ ≤ R₀ → R₀ ≤ x ^ (2 : ℝ) → ∀ c : ℕ → ℂ,
    ∀ 𝒯 : Finset ℝ, (∀ t ∈ 𝒯, |t| ≤ 2 * x ^ (3 : ℝ)) →
      (∀ t ∈ 𝒯, ∀ t' ∈ 𝒯, t ≠ t' → 1 ≤ |t - t'|) →
      (𝒯.card : ℝ) ≤ 2 * Real.exp (Real.log x ^ (0.9 : ℝ)) →
        ∑ t ∈ 𝒯, ‖normPoly R₀ (natIcc R₀ (ρ * R₀)) c t‖ ^ 2 ≤
          M * Real.log x * (R₀⁻¹ * ∑ n ∈ natIcc R₀ (ρ * R₀), ‖c n‖ ^ 2)

/-! ### The tuple part: the long-prime saving -/

/-- **(cor:long-prime-saving)** (`[P-06:0836–0847]`): "In the tuple term the long-prime polynomial
is, after partial summation, a normalized prime sum with a character modulo `k` and a fixed
log-power twist. Its dyad lies between `x^ε / 2` and `x^{1-ε}`. Choose fixed `0 < τ < ε` and
`1 - ε < η < 1` to apply Lemma `lem:long-prime`. For any prescribed `A_l`, it gives
`|P_l(t)| ≪ L^{-A_l}` (`L^{B'} ≤ |t| ≤ 2T_0`), after increasing `B'` beyond its threshold and all
retained shifts. The upper frequencies are `< x^2`."

Order: `ε`, `C₆`, `A_l`; then the threshold `B₀`, `M`, `x₀`. `J` is an interval of primes inside
`[N_l, 2N_l]` (a dyadic piece of the first slot), and the twist is part of `t`. For `ε > 1/2` the
range of `N_l` is empty for large `x`. -/
def LongPrimeSaving : Prop :=
  ∀ ε C₆ Al : ℝ, 0 < ε → 0 < C₆ → 0 < Al → ∃ B₀ M x₀ : ℝ, 0 < B₀ ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ Nl : ℝ, x ^ ε / 2 ≤ Nl → Nl ≤ x ^ (1 - ε) →
    ∀ J : Finset ℕ, IsPrimeInterval J → (∀ l ∈ J, Nl ≤ (l : ℝ) ∧ (l : ℝ) ≤ 2 * Nl) →
    ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ C₆ → ∀ χ : DirichletCharacter ℂ k,
    ∀ t : ℝ, Real.log x ^ B₀ ≤ |t| → |t| ≤ x ^ (2 : ℝ) →
      ‖normPoly Nl J (fun l => χ (l : ZMod k)) t‖ ≤ M * Real.log x ^ (-Al)

/-! ### The constant part: the model polynomial -/

/-- **(cor:constant-medium)** (`[P-06:0878–0893]`): "For the truncated model, a divisor `d'`
leaves a progression modulo `k` at scale `R' = R_0 / d'`. Its normalization in `N(t)` is
`A_{d'} / d'` times normalization at `R'`. Since `d' ≤ exp(O(L^{.47}))`, one has
`R' = x^{1 - o(1)}`. The divisor is a unit modulo `k`, so the original residue restriction becomes
a single residue restriction at this scale. For `L^{B'} ≤ |t| ≤ T_mod`, comparison with the
integral of the logarithmic phase gives `|N_0(t)| ≪ L^{C_{17}} (|t|^{-1} + x^{-c'})`. … sum using
`∑ |A_{d'}| / d' ≤ L^{C_8}`."

Stated for arbitrary coefficients `A` with the support and mass conditions of the model (divisors
`≤ exp(Csupp L^{.47})` and coprime to `k`, mass `≤ L^{C₈}`), a scale `R_0 ≥ x^δ`, the range
`R_0 ≤ n ≤ ρ R_0`, and all `1 ≤ |t| ≤ T_mod = exp(L / (log L)²)` (the lower limit `L^{B'}` is not
needed for the pointwise bound). Then `C_{17} = C₈`. Order: `δ, ρ, C₆, Csupp, C₈`; then `c'`,
`M`, `x₀`. The integral (cor:constant-medium-integral) is taken in the link to
`ConstantProductBound`. -/
def ModelPolynomialMedium : Prop :=
  ∀ δ ρ C₆ Csupp C₈ : ℝ, 0 < δ → 1 ≤ ρ → 0 < C₆ → ∃ c' M x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ R₀ : ℝ, x ^ δ ≤ R₀ → ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ C₆ → ∀ a : ℕ,
    ∀ A : ℕ → ℂ, (∀ e : ℕ, A e ≠ 0 →
        0 < e ∧ (e : ℝ) ≤ Real.exp (Csupp * Real.log x ^ (0.47 : ℝ)) ∧ e.Coprime k) →
      ∑ e ∈ Finset.Icc 1 ⌊Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))⌋₊, ‖A e‖ / (e : ℝ) ≤
        Real.log x ^ C₈ →
    ∀ t : ℝ, 1 ≤ |t| → |t| ≤ Real.exp (Real.log x / Real.log (Real.log x) ^ 2) →
      ‖normPoly R₀ (natIcc R₀ (ρ * R₀))
          (fun n => if n ≡ a [MOD k] then divisorSum A n else 0) t‖ ≤
        M * Real.log x ^ C₈ * (|t|⁻¹ + x ^ (-c'))

/-- **(cor:constant-high)** (`[P-06:0903–0912]`): "For `T_mod < |t| ≤ 2T_0`, apply Lemma
`lem:log-phase` to each such progression. Its modulus is at most `L^{C_6}`, its scale is
`x^{1 - o(1)}`, and, including retained shifts, its frequency is at least
`T_mod / 2 > exp(L / (2 (log L)²))` and at most `x^{1 + o(1)} < 4x^3`. After summing the reciprocal
divisor coefficients this yields `|N_0(t)| ≪ L^{C_{18}} exp(-L / (log L)^{C_{19}})`."

Stated as `ModelPolynomialMedium`, for `x^δ ≤ R_0 ≤ x²` and
`exp(L / (log L)²) ≤ |t| ≤ 4x³`; `C_{18} = C₈` and `C_{19}` is the constant `C_3` of
`lem:log-phase`. Order: `δ, ρ, C₆, Csupp, C₈`; then `C₁₉`, `M`, `x₀`. -/
def ModelPolynomialHigh : Prop :=
  ∀ δ ρ C₆ Csupp C₈ : ℝ, 0 < δ → 1 ≤ ρ → 0 < C₆ → ∃ C₁₉ M x₀ : ℝ, 0 < C₁₉ ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ R₀ : ℝ, x ^ δ ≤ R₀ → R₀ ≤ x ^ (2 : ℝ) →
    ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ C₆ → ∀ a : ℕ,
    ∀ A : ℕ → ℂ, (∀ e : ℕ, A e ≠ 0 →
        0 < e ∧ (e : ℝ) ≤ Real.exp (Csupp * Real.log x ^ (0.47 : ℝ)) ∧ e.Coprime k) →
      ∑ e ∈ Finset.Icc 1 ⌊Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))⌋₊, ‖A e‖ / (e : ℝ) ≤
        Real.log x ^ C₈ →
    ∀ t : ℝ, Real.exp (Real.log x / Real.log (Real.log x) ^ 2) ≤ |t| → |t| ≤ 4 * x ^ (3 : ℝ) →
      ‖normPoly R₀ (natIcc R₀ (ρ * R₀))
          (fun n => if n ≡ a [MOD k] then divisorSum A n else 0) t‖ ≤
        M * Real.log x ^ C₈ * Real.exp (-Real.log x / Real.log (Real.log x) ^ C₁₉)

/-! ### The leaves -/

/-- **The leaves and links of the proof of (cor:SM)**: everything that
`EndpointProof/Assembly.lean` uses and does not prove. Each field is a node that is not decomposed
further here (possibly with the classical or earlier inputs of its proof as hypotheses) or a link.
`EndpointProof/Open.lean` lists the fields that remain open. -/
structure EndpointLeaves (d : ℕ) : Prop where
  /-- (cor:omega-moment), `[P-06:0621–0630]`. -/
  omegaMoment : MertensReciprocal → OmegaMoment
  /-- Lemma `lem:divisor-model`, `[P-06:0565–0633]`. -/
  divisorModel : MertensReciprocal → OmegaMoment → DivisorModel
  /-- (cor:low-main-term), `[P-06:0652–0667]`. -/
  lowMainTerm : SmoothProgressionSum → LowMainTerm
  /-- `C_x = O_ε(1)`, `[P-06:0079]`. -/
  slotMass : MertensReciprocal → SlotMassBounded (d + 1)
  /-- The low-frequency step, `[P-06:0646–0679]`: `w = l n`, `H_marks(ln) = H_marks(n)`, the model
  on the scales `Y/l` and `Y`, Cauchy and (cor:model-error), (cor:low-main-term) for `m = l d'` and
  `m = d'`, `∑_𝔩 1 ≤ x^{1-ε} C_x`, `∑ |A_{d'}| ≤ exp(O(L^{.47})) L^{C_8}`, and the exact
  cancellation of the main terms (`∑_𝔩 1/l = C_x`). -/
  lowFrequency : DivisorModel → LowMainTerm → SlotMassBounded (d + 1) →
    LowFrequencyBound (d + 1)
  /-- The scales, `[P-06:0385–0389, 0549, 0703]`. -/
  scaleFacts : ScaleFacts
  /-- (cor:extract-small), `[P-06:0683–0692]`. -/
  extractSmall : ExtractSmallIdentity
  /-- (cor:u-coefficient) and the constant coefficient, `[P-06:0692–0715]`. -/
  extractedCoefficient : ExtractSmallIdentity → ExtractedCoefficientIdentity d
  /-- (cor:marked-bound) with marks removed, `[P-06:0044–0053]`. -/
  markedBound : PartialMarkedBound
  /-- `[P-06:0697–0698, 0712–0713]`. -/
  coefficientBound : MertensReciprocal → PartialMarkedBound → CoefficientBound d
  /-- The square exceptions, `[P-06:0692–0703]`. -/
  extractionError : ExtractedCoefficientIdentity d → MertensReciprocal → PartialMarkedBound →
    ExtractionErrorBound d
  /-- The factorial coefficient estimate, `[P-06:0781–0789]`. -/
  primePowerNorm : PrimePowerNorm
  /-- (cor:exceptional-count), `[P-06:0774–0801]`; uses the spaced mean value
  `sum_normSq_dirichletPolynomial_le_nat`. -/
  exceptionalCount : PrimePowerNorm → ExceptionalCount
  /-- (cor:sparse-bound), `[P-06:0803–0832]`. -/
  sparseBound : LogPhase → ModeratePhase → SparseBound
  /-- (cor:long-prime-saving), `[P-06:0836–0847]`: partial summation of Lemma 2.3. -/
  longPrimeSaving : LongPrimePolynomial → LongPrimeSaving
  /-- The tuple products, `[P-06:0763–0772, 0848–0858]`: on `|P_s| ≤ L^{-A_s}` the mean square of
  the collapsed `P_l R` ((cor:collapsed-coefficients), (cor:length-dominates-time)); on the
  exceptional unit intervals `|P_s| ≤ 2`, `|P_l| ≪ L^{-A_l}` and (cor:sparse-bound). -/
  tupleProduct : ExceptionalCount → SparseBound → LongPrimeSaving → TupleProductBound
  /-- The separation of the tuple part, `[P-06:0717–0737]`: residue classes of `p_s`, `u` and
  characters of `p_l` modulo `k`, dyads, Fourier separation of the cutoff in logarithmic size,
  tails by Dirichlet mean squares on translated intervals, retained shifts below `L^{B'}`. -/
  tupleSeparation : CoefficientBound d → TupleProductBound → TupleEnergy d
  /-- (cor:constant-medium), `[P-06:0878–0893]`. -/
  modelMedium : ModeratePhase → ModelPolynomialMedium
  /-- (cor:constant-high), `[P-06:0903–0912]`. -/
  modelHigh : LogPhase → ModelPolynomialHigh
  /-- The constant products, `[P-06:0763–0772, 0860–0925]`: ordinary times as for the tuple part;
  (cor:constant-model-error) from `DivisorModel` and the mean value on the whole interval;
  (cor:constant-medium-integral); (cor:constant-high) on the exceptional unit intervals with
  (cor:exceptional-count). -/
  constantProduct : CoefficientBound d → ExceptionalCount → DivisorModel →
    ModelPolynomialMedium → ModelPolynomialHigh → ConstantProductBound d
  /-- The separation of the constant part, `[P-06:0717–0737]`: residue classes of `p_s`, `n`
  modulo `k`, dyads of `p_s`, Fourier separation, tails. -/
  constantSeparation : CoefficientBound d → ConstantProductBound d → ConstantEnergy d

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
