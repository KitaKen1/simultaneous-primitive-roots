module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Objects

/-!
# Auxiliary statements inside the two "re-run" leaves

These two statements are not hypotheses of the proved chain (`Extraction/Assembly.lean`). They are
self-contained analytic lemmas that the manuscript uses inside the proofs of Lemma 7.2
(`ProgressionSlots`, `ProgressionUnit`) and of the Type II step (`ProxyLink`), stated here so that
they can be proved separately.

* `SmoothProgressionCount`: (ext:crt-count) `[P-07:0155–0163]`, smooth summation in one
  progression with an error `O_Φ(1)` uniform in the modulus, the residue and the dilation.
* `MellinSeparation`: `[P-07:0285–0289]`, "Fourier inversion of the smooth function in
  `log(mn/x)` separates the two variables into factors `m^{iv}` and `n^{iv}`, with a rapidly
  decreasing Fourier density".
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

/-- **(ext:crt-count)** (`[P-07:0155–0163]`): for a cutoff `Φ`,

`∑_{y ≥ 1, y ≡ a (mod m)} Φ(ℓ y / x) = x / (ℓ m) · ∫ Φ + O_Φ(1)`,

"by comparing each sampling interval with its integral and using the bounded total variation of
`Φ`"; the error is uniform in `x > 0`, in the dilation `ℓ ≥ 1`, in the modulus `m ≥ 1` and in the
residue `a`. In Lemma 7.2 the progression is the class of `y` modulo `m = H r d'` given by
`ℓ y ≡ -1 (mod r)`, `ℓ y + 1 ≡ b (mod H)` and `d' ∣ y` (`[PUB-tex:0518–0521]`).

The sum is a finite sum for `x > 0` (`Φ` has compact support and `ℓ ≥ 1`), and the term `y = 0`
vanishes (`Φ(0) = 0`). -/
def SmoothProgressionCount : Prop :=
  ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∃ C : ℝ, ∀ x : ℝ, 0 < x → ∀ ℓ m a : ℕ, 0 < ℓ → 0 < m →
    |(∑ᶠ y : ℕ, if y ≡ a [MOD m] then Φ ((ℓ : ℝ) * (y : ℝ) / x) else 0) -
        x / ((ℓ : ℝ) * (m : ℝ)) * ∫ t, Φ t| ≤ C

/-- **Separation of the cutoff** (`[P-07:0285–0289]`): for a cutoff `Φ` there is a continuous,
rapidly decreasing density `w` with `Φ(t) = ∫ w(v) t^{iv} dv` for all `t > 0`. Then
`Φ(mn/x) = ∫ w(v) x^{-iv} m^{iv} n^{iv} dv`, and the tails `|v| > L^C` are discarded with any
saving. (`w` is the Fourier transform of `s ↦ Φ(e^s)`, a smooth compactly supported function.)

The integral converges absolutely: `|t^{iv}| = 1` for `t > 0` and `w` is continuous with
`|w(v)| (1 + |v|)^2` bounded. -/
def MellinSeparation : Prop :=
  ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∃ w : ℝ → ℂ, Continuous w ∧
    (∀ N : ℕ, ∃ C : ℝ, ∀ v : ℝ, ‖w v‖ * (1 + |v|) ^ N ≤ C) ∧
    ∀ t : ℝ, 0 < t →
      ((Φ t : ℝ) : ℂ) = ∫ v : ℝ, w v * (t : ℂ) ^ ((v : ℂ) * Complex.I)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
