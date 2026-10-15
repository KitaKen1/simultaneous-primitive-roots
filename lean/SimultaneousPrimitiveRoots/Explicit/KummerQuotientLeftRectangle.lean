module

public import SimultaneousPrimitiveRoots.KummerQuotientLeftRectangle
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientZeroCount
public import SimultaneousPrimitiveRoots.Explicit.GaussianZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLogResidue
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientContourChoice
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientRectangle
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientLeftZeroCount
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientFiniteFormula
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLeftZeroCounting

/-! Generalization of `SimultaneousPrimitiveRoots.KummerQuotientLeftRectangle` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField Metric Classical
noncomputable section


/-- The negative-real-part portion of the actual finite rectangle residue sum
is uniformly bounded from boundary growth; it need not be classified as trivial. -/
theorem kummerEntireFullQuotientContinuation_leftRectangleSignedSum_le
    {a q : ℕ} [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {C x σ T : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hσ : -1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 0 ≤ T)
    (hb : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (U + 3) ^ 2)) :
    (∑' s : {s : ℂ | s ∈ Complex.Rectangle ((σ : ℂ) - Complex.I * T)
        ((2 : ℂ) + Complex.I * T) ∧ H s = 0 ∧ s.re < 0},
      (-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
        ((x : ℂ) ^ (s : ℂ) * artinGaussianMellin s)).re ≤
      (2 * artinGaussianConstant * kummerGaussianZeroMassConstant C) *
        (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  let z : ℂ := (σ : ℂ) - Complex.I * T
  let w : ℂ := (2 : ℂ) + Complex.I * T
  let J := {s : ℂ // s ∈ Complex.Rectangle z w ∧ H s = 0 ∧ s.re < 0}
  have hc : IsCompact (Complex.Rectangle z w) :=
    (isCompact_uIcc : IsCompact (Set.uIcc z.re w.re)).reProdIm isCompact_uIcc
  have hf : {s : ℂ | s ∈ Complex.Rectangle z w ∧ H s = 0 ∧ s.re < 0}.Finite :=
    (numberFieldEntireFullQuotientContinuation_finite_zeros_compact
      (PrimeKummerField a q) (CyclotomicField q ℚ) hH hc).subset (fun _ hs => ⟨hs.1, hs.2.1⟩)
  let : Fintype J := hf.fintype
  have hleft (s : J) : -1 ≤ s.val.re := by
    have hm := (PNTAnd.mem_Rect (z := z) (w := w)
      (by simpa [z, w] using hσ2)
      (by simpa [z, w] using (show -T ≤ T by linarith)) s.val).mp s.property.1
    have hh : σ ≤ s.val.re := by simpa [z] using hm.1
    exact hσ.trans hh
  let e : J ↪ {s : ℂ // -1 ≤ s.re ∧ s.re < 0 ∧ H s = 0} :=
    ⟨fun s => ⟨s.val, hleft s, s.property.2.2, s.property.2.1⟩,
      fun s t h => Subtype.ext (congrArg
        (fun v : {s : ℂ // -1 ≤ s.re ∧ s.re < 0 ∧ H s = 0} => v.val) h)⟩
  let S := (Finset.univ : Finset J).map e
  have h := kummerEntireFullQuotientContinuation_leftFiniteSignedSum_le hH hC hx hb S
  change (∑' s : J, (-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
    ((x : ℂ) ^ (s : ℂ) * artinGaussianMellin s)).re ≤ _
  rw [tsum_fintype]
  simpa [S, Finset.sum_map, e, artinGaussianZeroTerm] using h

end
end SimultaneousPrimitiveRoots.Explicit
