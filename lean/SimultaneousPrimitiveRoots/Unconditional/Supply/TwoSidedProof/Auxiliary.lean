module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements

/-!
# Auxiliary statements inside the leaves `insertion` and `separation`

These two statements are not hypotheses of the proved chain (`TwoSidedProof/Assembly.lean`). They
are self-contained lemmas that the manuscript uses inside the insertion of the cutoff
(`InsertionLink`) and inside the separation of the comparison correlations (`SeparationLink`),
stated here so that they can be proved separately. They are not proved in this directory.

* `SchurPairing`: `[P-06:0306–0308]`, "the absolute Schur estimate and the endpoint norms cost at
  most a fixed power of `L`": if the operator with absolute coefficients and its adjoint have row
  sums at most `R`, then `|⟨f, 𝒜 g⟩| ≤ R ‖f‖ ‖g‖` for a mark-free `f`.
* `MellinSeparationComplex`: (cor:insertion-separation) `[P-06:0290–0296]`, for a complex cutoff
  (`Extraction.MellinSeparation` is the same statement for the real nonnegative cutoffs of
  [P] §7).

The third ingredient of `InsertionLink`, the pairing of two mark-free vectors as an edge sum, is
proved: `pairMarkFree_physOp_markFree` (`TwoSidedProof/PairingExpansion.lean`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open scoped ContDiff

noncomputable section

/-- **Schur's test for the pairing** (`[P-06:0177–0180, 0306–0308]`): if the row sums of `𝒜` with
absolute coefficients (`physAbsRowSum`) and of its adjoint (`physAbsColSum`) are at most `R` at
every state, then for `f = ∑_{n ∈ I} f_n u_n` (independent of the marks) and every `g ∈ ℋ_ph`,

`|⟨f, 𝒜 g⟩| ≤ R ‖f‖ ‖g‖`.

The two sums are averages of the unsymmetrized row and column sums over the slot permutations of
the state; this suffices because `f` is constant on these orbits and `Sym g` is invariant, and
all physical states have the same mass. The statement is for integer positions, an arbitrary
family of groups and an arbitrary pattern family. -/
def SchurPairing : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (q : ℝ) (J ℓ : ℕ) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ R : ℝ),
    (∀ s : PState intPos 𝒢 J ℓ, physAbsRowSum intPos 𝒢 q 𝔉 k ζ s ≤ R) →
    (∀ s : PState intPos 𝒢 J ℓ, physAbsColSum intPos 𝒢 q 𝔉 k ζ s ≤ R) →
    ∀ (I : Finset ℤ) (fn : ℤ → ℂ) (g : PState intPos 𝒢 J ℓ → ℂ), MemPhysL2 intPos 𝒢 J ℓ g →
      ‖pairMarkFree intPos 𝒢 J ℓ I fn (physOp intPos 𝒢 q 𝔉 k ζ g)‖ ≤
        R * (Real.sqrt (markFreeNormSq intPos 𝒢 J ℓ I fn) *
          Real.sqrt (physNormSq intPos 𝒢 J ℓ g))

/-- **(cor:insertion-separation) for a complex cutoff** (`[P-06:0290–0296]`): "Let
`φ(u) = Ψ(e^u)` and use the convention `φ̂(ζ) = ∫ φ(u) e^{-iζu} du`. Then
`Ψ(n/(xD)) = (1/2π) ∫ φ̂(ζ) (n/x)^{iζ} D^{-iζ} dζ`": for a smooth compactly supported
`Ψ : (0, ∞) → ℂ` there is a continuous, rapidly decreasing density `w = φ̂/(2π)` with
`Ψ(t) = ∫ w(v) t^{iv} dv` for all `t > 0`. The rapid decrease gives
`∫_{|ζ| > L} |φ̂(ζ)| dζ ≪_N L^{-N}` (`[P-06:0309–0312]`). -/
def MellinSeparationComplex : Prop :=
  ∀ Ψ : ℝ → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Set.Ioi 0 →
    ∃ w : ℝ → ℂ, Continuous w ∧
      (∀ N : ℕ, ∃ C : ℝ, ∀ v : ℝ, ‖w v‖ * (1 + |v|) ^ N ≤ C) ∧
      ∀ t : ℝ, 0 < t → Ψ t = ∫ v : ℝ, w v * (t : ℂ) ^ ((v : ℂ) * Complex.I)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
