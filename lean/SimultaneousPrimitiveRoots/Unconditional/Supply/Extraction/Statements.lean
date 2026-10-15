module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Objects

/-!
# The intermediate results of the prime extraction ([P] §7 with a fixed residue class)

`PrimeExtractionReductionAt d H b` (`Supply/Reduction.lean`) is the statement that [P] §7
(`verification/stage7-sources/P-07.tex`) proves Theorem 7.1 with the factor `1_{p ≡ b (mod H)}`
from Theorems 3.1 and 6.1 and the classical lemmas, the class being carried as in the public paper
(`[PUB-tex:0462–0535]`). This file states the intermediate results of that proof, one
`def … : Prop` for each. `Extraction/Assembly.lean` proves the chain from them to
`PrimeExtractionReductionAt d H b`.

## Parameters

* `d`: the number of slots (`d = 1` is what is needed downstream; nothing below uses `d`).
* `H`, `b`: the modulus and the class; the statements are claimed for `0 < H` and `b.Coprime H`.
* `q`, `q₀`: the dampings of the array weight `𝒲` and of the active marks (`[P-07:0033–0034]`:
  "Fix `q, q_0 ∈ (0,1)`, for example `q = q_0 = 1/2`"); the statements are claimed for
  `0 < q < 1`, `0 < q₀ < 1`.
* The class enters exactly four statements: `ProgressionSlots`/`ProgressionUnit` (the CRT count),
  `PresieveBound` (the sieve density), `ProxyReplacement` (characters modulo `H`),
  `RetainedBound` (the joint residue weight of Theorem 6.1). The absolute estimates
  (`StripMass`, `CoinFailure`, `SquareExceptions`, `SiftedDecomposition`) and the removal of the
  array weight (`VarianceBound`) are class-free, as in `[PUB-tex:0527–0534]`.

## Nodes and links

A *node* is an estimate. A *link* is a `def XLink : Prop := (inputs and nodes) → node`, the
statement that one step of the manuscript works; it is a proposition to be proved, like the
nodes that have no further decomposition here (the *leaves*). `ExtractionLeaves d H b q q₀`
collects everything that is not proved in this directory.

Every estimate is stated for all sufficiently large `x` (`∀ᶠ x in atTop` or `∃ x₀, ∀ x ≥ x₀`), so
`Real.log x`, `Real.log (Real.log x)` and the real powers of `x` and of `Real.log x` are used only
where they are meaningful. Scale and level parameters are guarded: `0 < γ < 1`, `0 < c₀ < ε/2`
and `c₀ < 1/4`, `2 ≤ j`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology ContDiff

noncomputable section

/-! ### Bounded quantities -/

/-- **The slot statistic is bounded** (`[P-07:0016–0019]`): `C_x = O_{d,ε}(1)`, and on a range
`u ≤ R x` also `f_x(u) = O_{d,ε,R}(1)` ("there are only `O_ε(1)` prime divisors of `u` exceeding
`x^ε`"), uniformly in the admissible slot systems.

`u ≥ 1` is needed: every prime divides `0`. The bound `B` depends on `d, ε, R` only. -/
def SlotBounded (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 0 < R → ∃ B : ℝ, ∀ᶠ x : ℝ in atTop,
    ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
      slotMass S ≤ B ∧ ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ R * x → (slotCount S u : ℝ) ≤ B

/-- **The array weight is bounded** (`[P-07:0043–0045]`, `[P-03:0033–0035]`): "since
`V_i = log 2 + o(1)` and `sup_n n q^{n-1} < ∞`, these weights are bounded by a constant depending
only on `K, q`, for large `x`". The threshold for `x` may depend on the array. -/
def ArrayWeightBounded (q : ℝ) : Prop :=
  ∀ K : ℕ, ∃ C : ℝ, ∀ 𝔞 : MarkingArray K, ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
    |markedWeight q 𝔞 x n| ≤ C

/-- **The centered core `F_x = 𝒲 (f_x - C_x)` is bounded on `1 ≤ u ≤ R x`** (`[P-06:0079–0082]`,
used at `[P-07:0237–0238, 0385, 0512]`). The bound depends on `d, ε, R, K, q`; it is a consequence
of `SlotBounded` and `ArrayWeightBounded` (`coreBounded_of`). -/
def CoreBounded (d : ℕ) (q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 0 < R → ∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ 𝔞 : MarkingArray K,
    ∀ᶠ x : ℝ in atTop, ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
      ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ R * x → |centeredCore q 𝔞 x S u| ≤ B

/-- **The number of primes under a cutoff** (`[P-07:0680–0681]`: "the prime number theorem"; a
Chebyshev bound suffices): `∑_p Φ((p-1)/x) ≪_Φ x / log x`. -/
def PrimeMassBound : Prop :=
  ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
    shiftSum Φ x Nat.Prime (fun _ => 1) ≤ C * (x / Real.log x)

/-- **The mass of a dyadic band of primes** (`[P-02:0060–0064]`, (eq:band-mass)):
`∑_{exp(y) ≤ p ≤ exp(2y)} 1/p = log 2 + o(1)` as `y → ∞`, for every set `T` of primes between the
open and the closed band. This auxiliary statement is not a hypothesis of the proved chain; it is
the form of Mertens' estimate used inside `ArrayWeightBounded`, `ModelBounds` (`y = L^{a_i}`) and
`CandidateAdmissible` (`y = 2^k L^{0.28}`, `2^k L^{0.40}`, half-open bands), uniformly in `y`. -/
def DyadicPrimeMass : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ Y₀ : ℝ, ∀ y : ℝ, Y₀ ≤ y → ∀ T : Finset ℕ,
    (∀ p ∈ T, p.Prime ∧ Real.exp y ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (2 * y)) →
    (∀ p : ℕ, p.Prime → Real.exp y < (p : ℝ) → (p : ℝ) < Real.exp (2 * y) → p ∈ T) →
      |reciprocalMass T - Real.log 2| ≤ δ

/-! ### The independent divisor model -/

/-- **(ext:model-bounds)** (`[P-07:0063–0075]`): there are constants `0 < c_K ≤ C_K` with
`c_K ≤ m_𝒲 ≤ C_K` and `M_x(𝒲²) ≤ C_K`, "independently of the particular fixed exponents".

Order of quantifiers: `K`, then `c_K, C_K` (they depend on `K` and `q` only), then the array, then
`x` large (the threshold depends on the array: its bands must be disjoint, which needs
`L^{a_{i+1} - a_i} > 2`). -/
def ModelBounds (q : ℝ) : Prop :=
  ∀ K : ℕ, ∃ c C : ℝ, 0 < c ∧ ∀ 𝔞 : MarkingArray K, ∀ᶠ x : ℝ in atTop,
    c ≤ arrayMean q 𝔞 x ∧ arrayMean q 𝔞 x ≤ C ∧
      modelMean (arrayPrimes 𝔞 x) (fun n => markedWeight q 𝔞 x n ^ 2) ≤ C

/-- **(ext:deweight-model)** (`[P-07:0641–0648]`): for `n` disjoint arrays of `K` bands,
`M_x(Z) = n^{-2} ∑_a Var_M(𝒲_a / m_a) ≤ C_K / n`. The constant depends on `K` and `q` only (it is
`C_K / c_K²` in the notation of `ModelBounds`); the threshold for `x` depends on the family.
`0 < n` is needed: for `n = 0` the deviation is the constant `1`. -/
def ModelVariance (q : ℝ) : Prop :=
  ∀ K : ℕ, ∃ C : ℝ, ∀ n : ℕ, 0 < n → ∀ 𝔄 : Fin n → MarkingArray K, ArraysDisjoint 𝔄 →
    ∀ᶠ x : ℝ in atTop, modelMean (familyPrimes 𝔄 x) (arrayDeviation q 𝔄 x) ≤ C / (n : ℝ)

/-! ### Lemma 7.2: summed progression remainders -/

/-- **[P] Lemma 7.2 with the class, with the long-prime statistic** (`[P-07:0077–0093]`,
proof `[P-07:0095–0192]`; the class: `[PUB-tex:0518–0522]`). For `0 < c₀ < ε/2`, a fixed finite
family of disjoint arrays, each monomial `W ∈ {1, 𝒲_a, 𝒲_a 𝒲_{a'}}` (a repeated array allowed)
and every fixed `A > 0`,

`∑_{r ≤ x^{c₀}} | ∑_{u ≥ 1, r ∣ u+1, u+1 ≡ b (H)} Φ(u/x) f_x(u) W(u)
    - 1_{(r,H)=1} x/(H r) (∫ Φ) C_x M_x(W) | ≪_A x L^{-A}`,

uniformly in the admissible slot systems. `M_x` is the model on all the bands of the family.

Order of quantifiers: `ε`, `c₀`, `Φ`, the family, `A`; then `M` and `x₀` (they "may depend on the
fixed arrays"); then `x`, the monomial, the slot system. The bounded linear combinations of the
lemma follow by the triangle inequality and the linearity of `M_x` (`modelMean_add`,
`modelMean_const_mul`) and are not part of the statement. The sum is over all `1 ≤ r ≤ x^{c₀}` as
in the manuscript; the sieve uses the squarefree `r`. -/
def ProgressionSlots (d H b : ℕ) (q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ c₀ : ℝ, 0 < c₀ → c₀ < ε / 2 → ∀ Φ : ℝ → ℝ, IsCutoff Φ →
    ∀ (n K : ℕ) (𝔄 : Fin n → MarkingArray K), ArraysDisjoint 𝔄 → ∀ A : ℝ, 0 < A →
      ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ a a' : Option (Fin n), ∀ S : Fin d → Finset ℕ,
        SlotsAdmissible ε x S →
          progressionRemainder H b Φ x c₀ (fun u => (slotCount S u : ℝ)) (slotMass S)
              (pairWeight q 𝔄 x a a')
              (modelMean (familyPrimes 𝔄 x) (pairWeight q 𝔄 x a a')) ≤
            M * x * Real.log x ^ (-A)

/-- **[P] Lemma 7.2 with the class, without tuple factors** (`[P-07:0090]`: "The same assertion
holds with `f_x, C_x` replaced by `1, 1`"; rounding errors `[P-07:0177–0178]`).

The level exponent is restricted to `0 < c₀ < 1/4`. In the manuscript `c₀ < ε/2` for the margin
`ε` of a slot system, and a nonempty system has `ε ≤ 1/2`; a slot-free statement must say this
explicitly (for `c₀ ≥ 1` the statement is false: the terms with `r > R x` have an empty sum and a
main term `x/r`). The proof gives every `c₀ < 1`; only one value is needed. -/
def ProgressionUnit (H b : ℕ) (q : ℝ) : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → c₀ < 1 / 4 → ∀ Φ : ℝ → ℝ, IsCutoff Φ →
    ∀ (n K : ℕ) (𝔄 : Fin n → MarkingArray K), ArraysDisjoint 𝔄 → ∀ A : ℝ, 0 < A →
      ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ a a' : Option (Fin n),
        progressionRemainder H b Φ x c₀ (fun _ => 1) 1 (pairWeight q 𝔄 x a a')
            (modelMean (familyPrimes 𝔄 x) (pairWeight q 𝔄 x a a')) ≤
          M * x * Real.log x ^ (-A)

/-! ### Presieving -/

/-- **(ext:presift) with the class** (`[P-07:0196–0228]`; the sieve density with the class:
`[PUB-tex:0360–0383, 0523–0525]`). With `γ = c₀/(4h+3)` and `z = x^γ`,

`limsup_x  L / (x m_𝒲) · | ∑_{u ≥ 1, P⁻(u+1) > z, u+1 ≡ b (H)} Φ(u/x) 𝒲(u) (f_x(u) - C_x) |
    ≤ C₁ e^{-h} / γ`.

Order of quantifiers: `ε`, `c₀`, `Φ`; then `C₁` and `h₀`; then the even `h ≥ h₀`; then `K` and the
array; then the precision `η`; then `x` large; then the slot system. So `C₁` "depends on the slot
and cutoff data but is independent of `K, h` and of the fixed array" (`[P-07:0223–0224]`); it may
depend on `d, H, b, q` (the manuscript's constant does not depend on `q`; this is not needed).
`h₀` comes from the block sieve ("for every sufficiently large even integer `h`").

The extra hypothesis `c₀ < 1/4` is the one of `ProgressionUnit`; it is automatic when there is a
nonempty admissible slot system (`ε ≤ 1/2`). -/
def PresieveBound (d H b : ℕ) (q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ c₀ : ℝ, 0 < c₀ → c₀ < ε / 2 → c₀ < 1 / 4 → ∀ Φ : ℝ → ℝ, IsCutoff Φ →
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → Even h →
      ∀ (K : ℕ) (𝔞 : MarkingArray K), ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop,
        ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
          |shiftSum Φ x
              (fun v => IsRough (x ^ (c₀ / (4 * (h : ℝ) + 3))) v ∧ v ≡ b [MOD H])
              (centeredCore q 𝔞 x S)| ≤
            (C₁ * Real.exp (-(h : ℝ)) * ((4 * (h : ℝ) + 3) / c₀) + η) *
              arrayMean q 𝔞 x * (x / Real.log x)

/-- **The presieve step** (`[P-07:0196–0228]`): the block sieve (Lemma 2.6) for the bad conditions
`r' ∣ u + 1`, `r' ≤ z` prime, with density `g(r') = 1/r'` for `r' ∤ H` and `0` for `r' ∣ H`,
applied to the two weights `Φ(u/x) 1_{u+1 ≡ b} 𝒲(u) f_x(u)` and `Φ(u/x) 1_{u+1 ≡ b} 𝒲(u)`; the
remainders are the two forms of Lemma 7.2 for the monomial `𝒲` because
`z^{4h+2} = x^{c₀(4h+2)/(4h+3)} < x^{c₀}` (ext:sieve-level); the main terms cancel after
subtracting `C_x` times the second formula; Mertens' product gives
`∏_{r' ≤ z}(1 - 1/r') ≍ 1/(γ L)` and Mertens' sum bounds the density in the blocks `(w, w²]`. -/
def PresieveLink (d H b : ℕ) (q : ℝ) : Prop :=
  ProgressionSlots d H b q → ProgressionUnit H b q → ModelBounds q → SlotBounded d →
    BlockSieve → MertensProduct → MertensReciprocal → PresieveBound d H b q

/-! ### Composite integers and their prime factorizations -/

/-- **The integers that survive the presieve** (`[P-07:0230–0240]`). For `z = x^γ`, the sum over
the `u` with `P⁻(u+1) > z` is the sum over the primes `u + 1`, plus for each `2 ≤ j ≤ 2/γ` the sum
over the ordered `j`-tuples of primes `> z` with product `u + 1` counted with weight `1/j!`, up to
`o(x/L)`: "integers divisible by `p²` for a prime `p > z` number `≪ x/z`", and "we may discard
these integers at error `o(x/L)`, count the others with weight `1/j!`, and restore repeated factors
at the same cost".

The statement is for every function `F` bounded by `B` on the support of the cutoff, uniformly in
`F` and in the class. `γ < 1` is needed (for large `x` the primes in the support exceed `z`). -/
def SiftedDecomposition : Prop :=
  ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ B η : ℝ, 0 < η →
    ∀ᶠ x : ℝ in atTop, ∀ (H b : ℕ) (F : ℕ → ℝ), (∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → |F u| ≤ B) →
      |shiftSum Φ x (fun v => IsRough (x ^ γ) v ∧ v ≡ b [MOD H]) F -
          shiftSum Φ x (fun v => v.Prime ∧ v ≡ b [MOD H]) F -
          ∑ j ∈ Finset.Icc 2 ⌊2 / γ⌋₊, 1 / (j.factorial : ℝ) *
            shiftSum Φ x (fun v => v ≡ b [MOD H])
              (fun u => F u * convPow j (primeCoeff (x ^ γ)) (u + 1))| ≤
        η * (x / Real.log x)

/-- **(ext:composite-vanishing) with the class** (`[P-07:0241–0247]`): for each fixed `j`,

`∑_{p_1, …, p_j > z, p_1 ⋯ p_j ≡ b (H)} Φ((p_1 ⋯ p_j - 1)/x) 𝒲(p_1 ⋯ p_j - 1)
    (f_x(p_1 ⋯ p_j - 1) - C_x) = o(x/L)`.

Order of quantifiers: `ε`, `Φ`, `γ`; then `K₀` ("we then choose `K` sufficiently large for that
target, simultaneously for all `2 ≤ j ≤ 2/γ`", `[P-07:0300–0304]`); then `K ≥ K₀` and the array
("independent of the particular fixed band exponents"); then `j`; then `η`; then `x`; then the
slot system. -/
def CompositeVanishing (d H b : ℕ) (q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∀ γ : ℝ, 0 < γ → γ < 1 →
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ 𝔞 : MarkingArray K, ∀ j : ℕ, 2 ≤ j → (j : ℝ) ≤ 2 / γ →
      ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop, ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
        |shiftSum Φ x (fun v => v ≡ b [MOD H])
            (fun u => centeredCore q 𝔞 x S u * convPow j (primeCoeff (x ^ γ)) (u + 1))| ≤
          η * (x / Real.log x)

/-! ### Replacement of the prime slots (Theorem 3.1) -/

/-- **(ext:proxy-replacement) with the class** (`[P-07:0249–0315]`; the class:
`[PUB-tex:0503–0516]`): replacing every prime variable by the proxy coefficient
`a(m) = 1_{m > z} 1_{P⁻(m) > W} κ(m)` changes the tuple sum by `o(x/L)`:

`∑_{p_1, …, p_j > z} … = ∑_{m_1, …, m_j} Φ(…) 𝒲(…) (f_x(…) - C_x) ∏_i a(m_i) + o(x/L)`,

both sums with the factor `1_{product ≡ b (H)}`. This is the only place where `K` must be large.
Quantifiers as in `CompositeVanishing`. -/
def ProxyReplacement (d H b : ℕ) (q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∀ γ : ℝ, 0 < γ → γ < 1 →
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ 𝔞 : MarkingArray K, ∀ j : ℕ, 2 ≤ j → (j : ℝ) ≤ 2 / γ →
      ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop, ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
        |shiftSum Φ x (fun v => v ≡ b [MOD H])
            (fun u => centeredCore q 𝔞 x S u *
              (convPow j (primeCoeff (x ^ γ)) (u + 1) -
                convPow j (proxyCoeff x γ) (u + 1)))| ≤
          η * (x / Real.log x)

/-- **The Type II step** (`[P-07:0256–0304]`, `[PUB-tex:0503–0516]`). Telescope one variable `m`
at a time, `n` being the product of the others; `O(L²)` dyadic boxes with `H_m H_n ≍ x`,
`H_m, H_n ≥ x^{γ/2}`; the companion coefficient is rough-supported and `≤ L^{C_j} τ_{j-1}(n)`
(needs `V(W) ≍ L^{-0.24}`, Mertens' product), truncated at `L^B` by the divisor moments
(`divisorMoments`); `Φ((mn-1)/x)` is replaced by `Φ(mn/x)` and separated by Fourier inversion in
`log(mn/x)` into `m^{iv} n^{iv}`; `F` is the normalized clipped `f_x - C_x` (needs `SlotBounded`),
invariant under the band primes; the truncation and the replacement of `Φ` use "the bounded
endpoint factor" `𝒲 (f_x - C_x)` [P-07:0278–0285], which is `CoreBounded`; the class is `φ(H)^{-1} ∑_λ λ̄(b) λ(m) λ(n)`, the characters go to
the two coefficients, and the bound for `α_m λ(m)` is `markedTypeII_twisted`
(`Supply/Twist.lean`), which follows from the two Type II inputs. -/
def ProxyLink (d H b : ℕ) (q : ℝ) : Prop :=
  MarkedTypeIICoefficientForm → PrimeMinusRoughLongCoefficient → SlotBounded d →
    CoreBounded d q → MertensProduct → ProxyReplacement d H b q

/-! ### Removing candidate prime parts; the success coins -/

/-- **Stripping the candidate prime parts** (`[P-07:0317–0386]`): replacing `a(m)` by
`ã(m) = 1_{P⁻(m) > W} 1_{m̄ > x^γ} κ(m̄)` in every slot changes the positive tuple mass by
`o(x/L)`, "before any cancellation is used":

`∑_{m_1, …, m_j} Φ((m_1 ⋯ m_j - 1)/x) | ∏_i a(m_i) - ∏_i ã(m_i) | = o(x/L)`.

The statement has no array, no slot and no class: the bounded factor `𝒲 (f_x - C_x)` and the
indicator of the class are applied afterwards (`compositeVanishing_of`). `j ≥ 2` is used
(`[P-07:0375–0376]`). -/
def StripMass : Prop :=
  ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ j : ℕ, 2 ≤ j → ∀ η : ℝ, 0 < η →
    ∀ᶠ x : ℝ in atTop,
      shiftSum Φ x (fun _ => True)
          (fun u => ∑ e ∈ orderedFactorizations j (u + 1),
            |∏ i, proxyCoeff x γ (e i) - ∏ i, strippedCoeff x γ (candidatePrimes x) (e i)|) ≤
        η * (x / Real.log x)

/-- **The stripping step** (`[P-07:0347–0386]`): product dyads `m_i ≍ H_i`, `H_i ≥ x^γ/2`; rough
counts in each dyad (Lemma 2.5, (eq:rough-count)); (ext:removed-log-mean) (needs the bounded
masses of the candidate groups, i.e. Mertens' sum); `V(W) ≍ L^{-0.24}` (Mertens' product); the
strips `γ L < log m_i ≤ γ L + L^{0.9}`. -/
def StripLink : Prop :=
  RoughCounts → MertensProduct → MertensReciprocal → StripMass

/-- **Many successes** (`[P-07:0388–0514]`): there are `c₁ > 0` (so small that the success
probabilities (ext:success-probability) are at most one) and `c₂ > 0` such that the outcomes with
fewer than `c₂ log L` successes in either family have total positive weighted mass `o(x/L)` under
the coefficient `∏_i ã(m_i)`:

`∑_{m_1, …, m_j} Φ((v-1)/x) ∏_i ã(m_i) · (failed coin mass at u = v - 1) = o(x/L)`, `v = ∏ m_i`.

`c₁, c₂` depend on `Φ, γ, j, q₀`. The statement has no array, no slot and no class. The absolute
value is `|ã^{*j}(v) · failed mass|`; both factors are nonnegative once the probabilities are in
`[0, 1]` (first clause). -/
def CoinFailure (q₀ : ℝ) : Prop :=
  ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ j : ℕ, 2 ≤ j →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      (∀ᶠ x : ℝ in atTop, ∀ (u : ℕ) (g : (candidateGroups x).Index),
        coinProb (candidateGroups x) c₁ q₀ j u g ≤ 1) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop,
        shiftSum Φ x (fun _ => True)
            (fun u => |convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1) *
              failedMass (candidateGroups x) c₁ c₂ q₀ j x u|) ≤
          η * (x / Real.log x)

/-- **The coin step** (`[P-07:0409–0514]`): equidistribution of residues modulo products `Q` of a
fixed number of candidate primes among the rough integers of a dyad (Lemma 2.5,
(eq:rough-off-sieve-progression) with `d = Q ≤ exp(O(L^{0.45}))`), the model probabilities
(ext:prime-event-probabilities), fixed joint factorial moments, (ext:success-covariance),
Chebyshev (ext:success-chebyshev), and the transfer to the weighted tuples. Mertens' sum gives
`v_- ≤ V_g ≤ v_+`, Mertens' product `V(W) ≍ L^{-0.24}`. -/
def CoinLink (q₀ : ℝ) : Prop :=
  RoughCounts → MertensReciprocal → MertensProduct → CoinFailure q₀

/-! ### Allocation and the two-sided correlation (Theorem 6.1) -/

/-- **The candidate groups are admissible active groups** (`[P-07:0324–0329, 0533–0535]`): "there
are between positive constant multiples of `log L` groups of each kind; they are disjoint, their
reciprocal sums `V_g` are bounded above and below by positive constants, and they lie in the
allowed small and big ranges of Theorem 6.1; the big groups are full prime intervals; all
candidate primes exceed `W`", and "every active set `P` has between fixed positive multiples of
`log L` groups of each kind and satisfies all the active-group hypotheses".

For every `c₂ > 0` there are constants `Pc` such that for large `x` every index set `P` with at
least `c₂ log L` groups of each kind gives an admissible system `restrictGroups (candidateGroups x)
P`. -/
def CandidateAdmissible : Prop :=
  (∀ᶠ x : ℝ in atTop, ∀ p ∈ candidatePrimes x, p.Prime ∧ roughCutoff x < (p : ℝ)) ∧
  ∀ c₂ : ℝ, 0 < c₂ → ∃ Pc : ActiveGroupConstants, ∀ᶠ x : ℝ in atTop,
    ∀ P : Finset (candidateGroups x).Index,
      c₂ * Real.log (Real.log x) ≤ (P.toLeft.card : ℝ) →
      c₂ * Real.log (Real.log x) ≤ (P.toRight.card : ℝ) →
        (restrictGroups (candidateGroups x) P).Admissible Pc x

/-- **(ext:core-bound)** (`[P-07:0569–0574]`):
`|G_P(v)| ≤ (C/(L V(W)))^j τ_j(v_*) ≤ L^{C_j} τ(v_*)^{C_j}`. With the invariance
`allocationCore_coreInvariant` (`Supply/CoreSanity.lean`) this is `CoreAdmissible` for the
allocation core. The bound uses nothing about the two sets of primes, so it is stated for
arbitrary finite sets; `C` depends on `γ` and `j`. -/
def CoreGrowth : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ j : ℕ, ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
    ∀ (candidates active : Finset ℕ) (v : ℕ), 0 < v →
      |allocationCore x γ j candidates active v| ≤
        Real.log x ^ C * ((freePart active v).divisors.card : ℝ) ^ C

/-- **The allocation identity** (`[P-07:0576–0594]`, (ext:allocation-identity)). Let the active
primes be primes of the candidate set that exceed `W`, in pairwise disjoint groups, and let `v` be
divisible by the square of no active prime. Every factorization `e_1 ⋯ e_j = v_*` comes from
exactly `j^{ω_P(v)}` factorizations `m_1 ⋯ m_j = v` ("every active prime dividing `v` can be
assigned independently to any of the `j` slots"), all with the same coefficient `∏ ã(m_i)`. With
`j^{ω_P(v)} (q₀/j)^{ω_P(v) - s_P} = j^{s_P} q₀^{ω_P(v) - s_P}`:

`ã^{*j}(v) · ∏_g (q₀/j)^{ω_g(v)-1} ω_g(v)/V_g = j^{s_P} W_{1,q₀}(v) G_P(v)`.

This is an exact identity, for all real `x, γ, q₀`; `W_{1,q₀}(v) = ∏_g markFactor q₀ (𝒫_g) v`
(`ActiveGroups.oneMark_eq`). -/
def AllocationIdentity : Prop :=
  ∀ (x γ q₀ : ℝ) (j : ℕ), 1 ≤ j → ∀ (candidates : Finset ℕ) (𝔊 : ActiveGroups),
    (∀ g : 𝔊.Index, ∀ p ∈ 𝔊.group g, p.Prime ∧ p ∈ candidates ∧ roughCutoff x < (p : ℝ)) →
    (∀ g g' : 𝔊.Index, g ≠ g' → Disjoint (𝔊.group g) (𝔊.group g')) →
    ∀ v : ℕ, 0 < v → (∀ p ∈ 𝔊.allPrimes, ¬ p ^ 2 ∣ v) →
      convPow j (strippedCoeff x γ candidates) v *
          ∏ g : 𝔊.Index, markFactor (q₀ / (j : ℝ)) (𝔊.group g) v =
        (j : ℝ) ^ 𝔊.numGroups * (∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) v) *
          allocationCore x γ j candidates 𝔊.allPrimes v

/-- **Square exceptions** (`[P-07:0542–0557]`, (ext:candidate-square-count)): the integers
`v = u + 1` divisible by the square of a candidate prime number `≪ x exp(-c L^{0.28})`, and
"Cauchy–Schwarz and a fixed divisor moment bound give an exponential saving in a power of `L` for
sums of any fixed divisor power over this exceptional set". Only a saving of every fixed power of
`L` is stated. -/
def SquareExceptions : Prop :=
  ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∀ k : ℕ, ∀ A : ℝ, 0 < A → ∀ᶠ x : ℝ in atTop,
    shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
        (fun u => ((u + 1).divisors.card : ℝ) ^ k) ≤
      x * Real.log x ^ (-A)

/-- **The retained outcomes** (`[P-07:0516–0615]`; the class: `[PUB-tex:0527–0530]`): the part of
the stripped tuple sum carried by the outcomes with at least `c₂ log L` successes of each kind is
`o(x/L)`:

`∑_{m_1, …, m_j, v ≡ b (H)} Φ(u/x) 𝒲(u) (f_x(u) - C_x) ∏_i ã(m_i) · (retained coin mass at u)
    = o(x/L)`, `v = ∏ m_i = u + 1`.

It holds for every array (no lower bound on `K`), every `c₁, c₂ > 0` (the coin probabilities need
not be `≤ 1` here: only `c₁^{|P|} ≤ L^{O(1)}` is used) and every `j ≥ 2`, uniformly in the slot
systems. -/
def RetainedBound (d H b : ℕ) (q q₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∀ γ : ℝ, 0 < γ → γ < 1 →
    ∀ (K : ℕ) (𝔞 : MarkingArray K), ∀ j : ℕ, 2 ≤ j → ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
      ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop, ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
        |shiftSum Φ x (fun v => v ≡ b [MOD H])
            (fun u => centeredCore q 𝔞 x S u *
              convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1) *
              retainedMass (candidateGroups x) c₁ c₂ q₀ j x u)| ≤
          η * (x / Real.log x)

/-- **The allocation step** (`[P-07:0518–0615]`). Expand the failure factors of each retained
outcome: at most `3^{|𝒞|} = L^{O(1)}` terms `± ∏_{g ∈ P} s_g`, `P = S ∪ T` (ext:active-term);
every `P` is admissible (`CandidateAdmissible`); off the square exceptions (`SquareExceptions`,
used once to remove and once to restore them, with `CoreBounded` for the bounded factor) the
`v`-side of the term is `j^{s_P} W_{1,q₀}(v) G_P(v)` (`AllocationIdentity`); the class
`1_{v ≡ b (H)}` is a function of the product `v = u + 1` and is the joint factor
`𝓑_{H,b}(u, u+1)` (`twoSidedSum_classWeight`); with `Ψ(y) = y Φ(y)` each term is `x` times the sum
of Theorem 6.1^{𝔅} (ext:correlation-to-use), whose core hypotheses are
`allocationCore_coreInvariant` and `CoreGrowth`; `A` is chosen after the fixed costs
`3^{|𝒞|}`, `j^{s_P}`, `c₁^{|P|}`. -/
def AllocationLink (d H b : ℕ) (q q₀ : ℝ) : Prop :=
  TwoSidedCorrelation d H (classWeight H b) → CandidateAdmissible → CoreGrowth →
    AllocationIdentity → SquareExceptions → CoreBounded d q → RetainedBound d H b q q₀

/-! ### The weighted prime sum and the removal of the array weight -/

/-- **(ext:weighted-primes) with the class** (`[P-07:0619–0629]`, `[PUB-tex:0410–0417]`):

`limsup_x  L/x · | ∑_{p ≡ b (H)} Φ((p-1)/x) 𝒲(p-1)/m_𝒲 · (f_x(p-1) - C_x) | ≤ C₁ e^{-h}/γ`,
`γ = c₀/(4h+3)`.

Order of quantifiers: `ε`, `c₀`, `Φ`; then `C₁` and `h₀`; then the even `h ≥ h₀`; then `K₀`; then
`K ≥ K₀` and the array; then `η`; then `x`; then the slot system. "The constant here remains
independent of `K, h`"; the lower bound `K₀` for `K` depends on `h` and "is independent of the
particular fixed band exponents". -/
def WeightedPrimeBound (d H b : ℕ) (q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ c₀ : ℝ, 0 < c₀ → c₀ < ε / 2 → c₀ < 1 / 4 → ∀ Φ : ℝ → ℝ, IsCutoff Φ →
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → Even h → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ 𝔞 : MarkingArray K, ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop,
        ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
          |shiftSum Φ x (fun v => v.Prime ∧ v ≡ b [MOD H])
              (fun u => normWeight q 𝔞 x u * ((slotCount S u : ℝ) - slotMass S))| ≤
            (C₁ * Real.exp (-(h : ℝ)) * ((4 * (h : ℝ) + 3) / c₀) + η) * (x / Real.log x)

/-- **(ext:prime-deweight-square)** (`[P-07:0653–0670]`): for `n` disjoint arrays of `K` bands,

`limsup_x  L/x · ∑_p Φ((p-1)/x) Z(p-1) ≤ C / n`.

There is no class here: `1_{p ≡ b (H)} Z(p-1) ≤ Z(p-1)` (`[PUB-tex:0531–0532]`).

Order of quantifiers: `Φ`, `K`; then `C`; then `n ≥ 1` and the family; then `η`; then `x`. In the
manuscript the bound is `≪ C_K / b` with an implied constant that depends on `c₀` and the cutoff
but not on `b, K`; here the two constants are merged into one `C` depending on `Φ, K, q`, which
is all that the limit `b → ∞` at fixed `h, K` needs. -/
def VarianceBound (q : ℝ) : Prop :=
  ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∀ K : ℕ, ∃ C : ℝ, ∀ n : ℕ, 0 < n →
    ∀ 𝔄 : Fin n → MarkingArray K, ArraysDisjoint 𝔄 → ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop,
      shiftSum Φ x Nat.Prime (arrayDeviation q 𝔄 x) ≤ (C / (n : ℝ) + η) * (x / Real.log x)

/-- **The variance step** (`[P-07:0649–0670]`): `Z` is a combination of the monomials
`1, 𝒲_a, 𝒲_a 𝒲_{a'}` with coefficients `1, -2/(n m_a), 1/(n² m_a m_{a'})`, bounded by
`ModelBounds`, so Lemma 7.2 without tuple factors and without class (`ProgressionUnit 1 1 q`)
bounds the sieve remainders; the upper bound of the block sieve at depth `2` with
`z' = x^{c₀/20}` (remainder range `(z')^{10} = x^{c₀/2} < x^{c₀}`); "every prime `u + 1` in the
support exceeds `z'`"; the main term is `≪ x M_x(Z) / log z'` (`ModelVariance`, Mertens'
product). -/
def VarianceLink (q : ℝ) : Prop :=
  ProgressionUnit 1 1 q → ModelBounds q → ModelVariance q → BlockSieve → MertensProduct →
    MertensReciprocal → VarianceBound q

/-! ### What remains to be proved -/

/-- **The leaves of the extraction**: everything that `Extraction/Assembly.lean` assumes, for one
choice of `d, H, b, q, q₀` (claimed for `0 < H`, `b.Coprime H`, `0 < q < 1`, `0 < q₀ < 1`; `d = 1`
suffices downstream). Each field is a statement with its inputs;
`primeExtractionReductionAt_of` derives `PrimeExtractionReductionAt d H b` from them. -/
structure ExtractionLeaves (d H b : ℕ) (q q₀ : ℝ) : Prop where
  /-- `[P-07:0016–0019]`: `C_x`, `f_x` bounded (Mertens' sum; prime divisors `≥ x^ε`). -/
  slotBounded : MertensReciprocal → SlotBounded d
  /-- `[P-07:0043–0045]`: `𝒲` bounded (`V_i = log 2 + o(1)`). -/
  weightBounded : MertensReciprocal → ArrayWeightBounded q
  /-- `[P-07:0680–0681]`: `∑_p Φ((p-1)/x) ≪ x/L`. -/
  primeMass : SiegelWalfiszPrimeCounting → PrimeMassBound
  /-- `[P-07:0063–0075]`, (ext:model-bounds). -/
  modelBounds : MertensReciprocal → ModelBounds q
  /-- `[P-07:0641–0648]`, (ext:deweight-model). -/
  modelVariance : ModelBounds q → ModelVariance q
  /-- Lemma 7.2 with the class and the long-prime statistic, `[P-07:0077–0192]`. -/
  progressionSlots : MertensReciprocal → ProgressionSlots d H b q
  /-- Lemma 7.2 with the class, without tuple factors, `[P-07:0090, 0177–0178]`. -/
  progressionUnit : MertensReciprocal → ProgressionUnit H b q
  /-- Lemma 7.2 without class and without tuple factors (for the variance step). -/
  progressionUnitOne : MertensReciprocal → ProgressionUnit 1 1 q
  /-- The presieve step, `[P-07:0196–0228]`. -/
  presieve : PresieveLink d H b q
  /-- `[P-07:0230–0240]`: primes, tuples of primes, and squares. -/
  sifted : SiftedDecomposition
  /-- The Type II step, `[P-07:0249–0315]`. -/
  proxy : ProxyLink d H b q
  /-- The stripping step, `[P-07:0317–0386]`. -/
  strip : StripLink
  /-- The coin step, `[P-07:0388–0514]`. -/
  coin : CoinLink q₀
  /-- `[P-07:0319–0329, 0533–0535]`: candidate groups and active sets. -/
  candidateAdmissible : MertensReciprocal → CandidateAdmissible
  /-- `[P-07:0569–0574]`, (ext:core-bound). -/
  coreGrowth : MertensProduct → CoreGrowth
  /-- `[P-07:0576–0594]`, (ext:allocation-identity). -/
  allocationIdentity : AllocationIdentity
  /-- `[P-07:0542–0557]`, (ext:candidate-square-count). -/
  squareExceptions : SquareExceptions
  /-- The allocation step, `[P-07:0518–0615]`. -/
  allocation : AllocationLink d H b q q₀
  /-- The variance step, `[P-07:0649–0670]`. -/
  variance : VarianceLink q

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
