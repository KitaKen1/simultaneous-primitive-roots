module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Reduction
public import SimultaneousPrimitiveRoots.Unconditional.Transference.GraphInputs

/-!
# The two-sided correlation as a reduction ([P] §6, re-run with a joint residue weight)

[P] §6 proves Theorem 6.1 from three inputs: the two graph inputs, Propositions 6.2 and 6.3
(`[P-06:0152–0251]`; they are [S] Theorem 3.5 with Corollary 3.11 and Lemma 3.4, and [S]
Theorem 4.1 with Lemma 4.3), and the endpoint estimate (cor:SM) (`[P-06:0544–0550]`). The steps of
the reduction are

* endpoint bounds and the Mellin insertion (`[P-06:0260–0316]`);
* removal of the shared labels (`[P-06:0318–0377]`);
* comparison multipliers, major arcs and the local Mellin energy (`[P-06:0379–0553]`);
* the assembly (`[P-06:0927–0935]`).

The public paper re-runs them with the joint factor `𝓑(w, w+1)` (`[PUB-tex:0479–0501]`,
`[PUB-ja:0416–0445]`): the weight is split into at most `H²` products of residue indicators at the
two endpoints, recombined before the shared labels are divided out, and in a comparison
correlation it becomes a residue condition on the first endpoint, which costs (cor:SM) with a
larger denominator exponent. This is where the quantification of (cor:SM) over its exponents is
used.

* `TwoSidedReduction d H 𝔅`: the statement that this argument works, with the graph inputs
  `Transference.GraphTransferInput`, `Transference.IdealFamilyInput` of
  `Unconditional/Transference/GraphInputs.lean` and (cor:SM) (`EndpointEnergy d`) as hypotheses.
  It is a proposition (`def … : Prop`) and is **not proved here** (rows C3–C5 and C14 of
  `docs/s-side-map.md` §2.4). The classical inputs of this part of [P] §6 are the divisor moments
  and the Dirichlet mean squares of [P] Lemma 2.2, which are theorems of
  `Unconditional/Classical/`.
* `fixedClassLongPrimeStatistic_of_inputs`: the two reductions (`PrimeExtractionReduction 1` and
  `TwoSidedReduction 1 H (classWeight H b)`) and the inputs — Theorem 3.1 in coefficient form,
  [P] Lemma 5.2, Propositions 6.2 and 6.3, (cor:SM), and the classical inputs of [P] §2 — give
  `FixedClassLongPrimeStatistic α β`. This is pure logic.

The graph inputs are stated for [S]'s prime groups (`Transference.GroupParams`,
`Transference.PrimeGroups`); the identification of the active groups of [P] §6 (`ActiveGroups`)
with them, at the exponents `(0.27, 0.36, 0.39, 0.46)` and `ℓ = k = 1` (`[P-06:0256–0258]`), is
part of the proof of the reduction.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply

noncomputable section

/-- **[P] §6 with a joint residue weight, as a reduction** (for `d` slots and the weight `𝔅`
modulo `H`): Proposition 6.2, Proposition 6.3, (cor:SM) for all fixed exponents and Mertens'
estimate for `∑ 1/p` imply Theorem 6.1^{𝔅} (`[P-06:0260–0553, 0927–0935]`,
`[PUB-tex:0479–0501]`). Mertens is used outside (cor:SM) for `V_i = log 2 + o(1)` and
`C_x = O_ε(1)` (`[P-06:0079–0085]`, `[P-03:0027–0035]`).

For `𝔅 = 1` this is the proof of [P] Theorem 6.1, which uses (cor:SM) only at the exponent `C_6`
of its major arcs; the public paper writes the case `𝔅 = 𝓑_{H,b}` for `d = 1`. -/
def TwoSidedReduction (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop :=
  Transference.GraphTransferInput → Transference.IdealFamilyInput → EndpointEnergy d →
    MertensReciprocal → TwoSidedCorrelation d H 𝔅

/-- The reduction of [P] §6 for the class weights `𝓑_{H,b}` of all moduli and reduced classes. -/
def TwoSidedReductionFixedClass (d : ℕ) : Prop :=
  ∀ H b : ℕ, 0 < H → b.Coprime H → TwoSidedReduction d H (classWeight H b)

/-- The reduction of [P] §6 and its inputs give Theorem 6.1 with the class factor. -/
theorem twoSidedFixedClass_of_reduction {d : ℕ} (hred : TwoSidedReductionFixedClass d)
    (h62 : Transference.GraphTransferInput) (h63 : Transference.IdealFamilyInput)
    (hSM : EndpointEnergy d) (hM1 : MertensReciprocal) : TwoSidedFixedClass d :=
  fun H b hH hb => hred H b hH hb h62 h63 hSM hM1

/-- **The S side in one statement.** The two reductions ([P] §7 and [P] §6, re-run with the class)
and their inputs — Theorem 3.1 in coefficient form, [P] Lemma 5.2, Propositions 6.2 and 6.3,
(cor:SM), Siegel–Walfisz, the two Mertens estimates, the rough counts and the block sieve — give
the fixed-class long-prime statistic of `SupplyBridge.lean` for every `0 < α`, `β < 1`. -/
theorem fixedClassLongPrimeStatistic_of_inputs (hE : PrimeExtractionReduction 1)
    (hC : TwoSidedReductionFixedClass 1) (hII : MarkedTypeIICoefficientForm)
    (h52 : PrimeMinusRoughLongCoefficient) (h62 : Transference.GraphTransferInput)
    (h63 : Transference.IdealFamilyInput) (hSM : EndpointEnergy 1)
    (hSW : SiegelWalfiszPrimeCounting) (hM1 : MertensReciprocal) (hM2 : MertensProduct)
    (hR : RoughCounts) (hB : BlockSieve) {α β : ℝ} (hα : 0 < α) (hβ : β < 1) :
    FixedClassLongPrimeStatistic α β :=
  fixedClassLongPrimeStatistic_of_reduction hE hII h52
    (twoSidedFixedClass_of_reduction hC h62 h63 hSM hM1) hSW hM1 hM2 hR hB hα hβ

end

end SimultaneousPrimitiveRoots.Unconditional.Supply
