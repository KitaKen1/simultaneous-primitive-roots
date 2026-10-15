module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.PrimeStatistic
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TypeII
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSided
public import SimultaneousPrimitiveRoots.Unconditional.Supply.ClassicalInputs

/-!
# The prime extraction as a reduction ([P] §7, re-run with a fixed residue class)

[P] §7 (`[P-07:0056–0702]`) derives Theorem 7.1 from the one-sided Type II estimate (Theorem 3.1),
the two-sided correlation (Theorem 6.1) and the classical inputs of §2. The public paper
(`[PUB-tex:0462–0535]`, `[PUB-ja:0416–0483]`) re-runs it with the factor `1_{p ≡ b (mod H)}`:

* presieve (`[P-07:0194–0228]`): Lemma 7.2 with the class (`[PUB-tex:0518–0525]`) and the block
  sieve; the main term carries `1/φ(H)`;
* composite terms, one-sided replacement (`[P-07:0249–0315]`): the class is moved to the two
  coefficients by characters `λ (mod H)` (`[PUB-tex:0503–0516]`), so the **coefficient form** of
  Theorem 3.1 is needed, together with [P] Lemma 5.2 at the modulus exponent `A_0 + 1`;
* candidate primes, success coins (`[P-07:0317–0514]`): absolute estimates;
* allocation (`[P-07:0516–0615]`): the class is a function of the actual product `v = u + 1`, so
  it is a joint factor `𝓑(u, u+1)` of the two endpoints of the two-sided correlation: this is
  **Theorem 6.1^{𝔅}** with `𝔅 = 𝓑_{H,b}`;
* removal of the array weight (`[P-07:0617–0693]`): unchanged (`1_{p ≡ b} Z_b ≤ Z_b`).

`PrimeExtractionReductionAt d H b` is the statement that this argument works, for one class. It is
a proposition (`def … : Prop`) and is **not proved here**; proving it is the "E" group of
`docs/s-side-map.md` §2.2.

## Where (cor:SM) enters

(cor:SM) (`EndpointEnergy`) is not used by §7. It is the endpoint estimate inside the proof of
Theorem 6.1 (`[P-06:0544–0550, 0927–0935]`), and the fixed-class Theorem 6.1^{𝔅} uses it at a
larger exponent (`[PUB-tex:0496–0500]`). With `TwoSidedCorrelation d H (classWeight H b)` as a
hypothesis, `EndpointEnergy d` is therefore redundant. `PrimeExtractionReductionWithEnergyAt`
records the reduction with all three statements as hypotheses; it follows from
`PrimeExtractionReductionAt`. The second-level reduction "graph inputs (Propositions 6.2, 6.3)
∧ (cor:SM) ⇒ Theorem 6.1^{𝔅}" is `TwoSidedReduction` in `Supply/TwoSidedReduction.lean`; its
graph inputs are stated in `Unconditional/Transference/GraphInputs.lean`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply

noncomputable section

/-! ### The allocation core

The second endpoint `G` of Theorem 6.1^{𝔅} is arbitrary in the statement. In the reduction it is
the allocation core `G_P` of `[P-07:0559–0572]`, recorded here; it is not used in the statements
below. -/

/-- The proxy weight `κ(m) = 1 / (V(W) log m)` for `m ≥ 2` and `κ(1) = 0`
(`[P-07:0249–0254]`, (ext:proxy-weight)). -/
def proxyKappa (x : ℝ) (m : ℕ) : ℝ :=
  if 2 ≤ m then 1 / (mertensProduct (roughCutoff x) * Real.log m) else 0

/-- The ordered factorizations `e_1 ⋯ e_j = n` into `j` positive integers. -/
def orderedFactorizations (j n : ℕ) : Finset (Fin j → ℕ) :=
  (Fintype.piFinset fun _ : Fin j => n.divisors).filter fun e => ∏ i, e i = n

open _root_.Classical in
/-- **The allocation core** (`[P-07:0559–0565]`, (ext:allocation-core)):
`G_P(v) = ∑_{e_1 ⋯ e_j = v_*} ∏_i [1_{P⁻(e_i) > W} 1_{ē_i > x^γ} κ(ē_i)]`, where `v_*` removes the
parts of `v` at the primes of the active set (`active`) and the bar removes the parts at all
candidate primes (`candidates`), the inactive ones included. The definition implies
`G_P(v) = G_P(v_*)` (`[P-07:0566–0568]`), and `|G_P(v)| ≤ L^{C_j} τ(v_*)^{C_j}` is
(ext:core-bound) `[P-07:0569–0574]`: these are the two hypotheses `CoreAdmissible` of
Theorem 6.1^{𝔅} (neither is proved in Lean here). -/
def allocationCore (x γ : ℝ) (j : ℕ) (candidates active : Finset ℕ) (v : ℕ) : ℝ :=
  ∑ e ∈ orderedFactorizations j (freePart active v),
    ∏ i, if IsRough (roughCutoff x) (e i) ∧ x ^ γ < (freePart candidates (e i) : ℝ) then
      proxyKappa x (freePart candidates (e i)) else 0

/-! ### The reduction -/

/-- **[P] §7 with a fixed class, as a reduction** (for `d` slots, modulus `H`, class `b`):

* `MarkedTypeIICoefficientForm`: Theorem 3.1 in coefficient form (`[A-08:0099–0123]`);
* `PrimeMinusRoughLongCoefficient`: [P] Lemma 5.2 (`[P-05:0044–0055]`), the coefficient test for
  the prime-minus-rough coefficient;
* `TwoSidedCorrelation d H (classWeight H b)`: Theorem 6.1^{𝔅} for `𝔅 = 𝓑_{H,b}`;
* the classical inputs of [P] §2: `SiegelWalfiszPrimeCounting` and the two Mertens estimates
  (Lemma 2.1), `RoughCounts` (Lemma 2.5), `BlockSieve` (Lemma 2.6). The divisor moments
  (Lemma 2.2) are also used; they are a theorem (`divisorMoments`), not a hypothesis.

imply Theorem 7.1^{H,b}, `PrimeStatisticFixedClassAt d H b`.

The public paper writes this argument for `d = 1`; for `H = 1` it is [P] §7 (all `d ≥ 1`). -/
def PrimeExtractionReductionAt (d H b : ℕ) : Prop :=
  MarkedTypeIICoefficientForm → PrimeMinusRoughLongCoefficient →
    TwoSidedCorrelation d H (classWeight H b) →
      SiegelWalfiszPrimeCounting → MertensReciprocal → MertensProduct → RoughCounts →
        BlockSieve → PrimeStatisticFixedClassAt d H b

/-- The reduction for every modulus `H ≥ 1` and every reduced class `b`. -/
def PrimeExtractionReduction (d : ℕ) : Prop :=
  ∀ H b : ℕ, 0 < H → b.Coprime H → PrimeExtractionReductionAt d H b

/-- The reduction with (cor:SM) (`EndpointEnergy d`) as an additional hypothesis:
"Theorem 3.1 (coefficient form) ∧ Theorem 6.1^{𝔅} ∧ (cor:SM) ∧ classical inputs ⇒
Theorem 7.1^{H,b}". The hypothesis `EndpointEnergy d` is not needed once Theorem 6.1^{𝔅} is
assumed (`primeExtractionReductionWithEnergyAt_of_reductionAt`). -/
def PrimeExtractionReductionWithEnergyAt (d H b : ℕ) : Prop :=
  MarkedTypeIICoefficientForm → PrimeMinusRoughLongCoefficient →
    TwoSidedCorrelation d H (classWeight H b) → EndpointEnergy d →
      SiegelWalfiszPrimeCounting → MertensReciprocal → MertensProduct → RoughCounts →
        BlockSieve → PrimeStatisticFixedClassAt d H b

theorem primeExtractionReductionWithEnergyAt_of_reductionAt {d H b : ℕ}
    (h : PrimeExtractionReductionAt d H b) : PrimeExtractionReductionWithEnergyAt d H b :=
  fun h1 h2 h3 _ h4 h5 h6 h7 h8 => h h1 h2 h3 h4 h5 h6 h7 h8

/-- The reduction and its inputs give Theorem 7.1^{H,b} for all classes. -/
theorem primeStatisticFixedClass_of_reduction {d : ℕ} (hred : PrimeExtractionReduction d)
    (hII : MarkedTypeIICoefficientForm) (h52 : PrimeMinusRoughLongCoefficient)
    (h61 : TwoSidedFixedClass d) (hSW : SiegelWalfiszPrimeCounting) (hM1 : MertensReciprocal)
    (hM2 : MertensProduct) (hR : RoughCounts) (hB : BlockSieve) : PrimeStatisticFixedClass d :=
  fun H b hH hb => hred H b hH hb hII h52 (h61 H b hH hb) hSW hM1 hM2 hR hB

/-- **The top of the S side.** The reduction for one slot and its inputs give the fixed-class
long-prime statistic of `SupplyBridge.lean` for every `0 < α`, `β < 1`; in particular for the
exponents `α = 1 - δ/2`, `β = 1 - δ/4`, `δ = 10⁻⁶` of the Lean reduction. -/
theorem fixedClassLongPrimeStatistic_of_reduction (hred : PrimeExtractionReduction 1)
    (hII : MarkedTypeIICoefficientForm) (h52 : PrimeMinusRoughLongCoefficient)
    (h61 : TwoSidedFixedClass 1) (hSW : SiegelWalfiszPrimeCounting) (hM1 : MertensReciprocal)
    (hM2 : MertensProduct) (hR : RoughCounts) (hB : BlockSieve) {α β : ℝ} (hα : 0 < α)
    (hβ : β < 1) : FixedClassLongPrimeStatistic α β :=
  fixedClassLongPrimeStatistic_of_primeStatisticFixedClass hα hβ
    (primeStatisticFixedClass_of_reduction hred hII h52 h61 hSW hM1 hM2 hR hB)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply
