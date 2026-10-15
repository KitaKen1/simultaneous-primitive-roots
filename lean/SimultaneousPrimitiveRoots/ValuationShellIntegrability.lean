module

public import SimultaneousPrimitiveRoots.FiniteBesselSheetJets
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set
open scoped Pointwise
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A geometric shell envelope proves actual absolute integrability. The shell
mass bound is an explicit input; no additive/multiplicative Haar convention is
silently identified. Overlap of the measurable shells is allowed. -/
theorem artinGeometricShell_integrableOn {f : X → ℂ} {S : ℕ → Set X}
    (hm : ∀ k, MeasurableSet (S k)) (hf : AEStronglyMeasurable f μ)
    {C m r : ℝ} (hC : 0 ≤ C) (_hmass : 0 ≤ m) (hr : 0 ≤ r) (hr1 : r < 1)
    (hfin : ∀ k, μ (S k) < ⊤) (hμ : ∀ k, μ.real (S k) ≤ m)
    (hb : ∀ k x, x ∈ S k → ‖f x‖ ≤ C * r ^ k) :
    IntegrableOn f (⋃ k, S k) μ := by
  have hi (k : ℕ) : IntegrableOn f (S k) μ := by
    apply Measure.integrableOn_of_bounded (hfin k).ne hf
    exact (ae_restrict_mem (hm k)).mono (fun x hx => hb k x hx)
  apply integrableOn_iUnion_of_summable_integral_norm hi
  apply Summable.of_nonneg_of_le (fun k => integral_nonneg (fun _ => norm_nonneg _))
    (fun k => ?_) ((summable_geometric_of_lt_one hr hr1).mul_left (C * m))
  have h := norm_setIntegral_le_of_norm_le_const_ae (f := fun x => ‖f x‖) (hfin k)
    ((ae_restrict_mem (hm k)).mono (fun x hx => by
      simpa only [Real.norm_eq_abs, abs_norm] using hb k x hx))
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at h
  calc
    (∫ x in S k, ‖f x‖ ∂μ) ≤ (C * r ^ k) * μ.real (S k) := h
    _ ≤ (C * r ^ k) * m := mul_le_mul_of_nonneg_left (hμ k) (by positivity)
    _ = (C * m) * r ^ k := by ring

theorem artinGeometricShell_integrable_of_support {f : X → ℂ} {S : ℕ → Set X}
    (hm : ∀ k, MeasurableSet (S k)) (hf : AEStronglyMeasurable f μ)
    {C m r : ℝ} (hC : 0 ≤ C) (hmass : 0 ≤ m) (hr : 0 ≤ r) (hr1 : r < 1)
    (hfin : ∀ k, μ (S k) < ⊤) (hμ : ∀ k, μ.real (S k) ≤ m)
    (hb : ∀ k x, x ∈ S k → ‖f x‖ ≤ C * r ^ k)
    (hs : Function.support f ⊆ ⋃ k, S k) : Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset hs).mp
    (artinGeometricShell_integrableOn hm hf hC hmass hr hr1 hfin hμ hb)

theorem artinValuationShell_ratio {Q β : ℝ} (hQ : 1 < Q) (hβ : 0 < β) :
    0 < Q ^ (-β) ∧ Q ^ (-β) < 1 :=
  ⟨Real.rpow_pos_of_pos (by linarith) _,
    Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)⟩

theorem artinValuationShell_weighted_envelope {Q ρ δ σ C : ℝ} {k : ℕ}
    (hQ : 0 < Q) (hρ : ρ = Q ^ (-(k : ℝ))) {z : ℂ}
    (hz : ‖z‖ ≤ C * ρ ^ δ) :
    ‖((ρ ^ σ : ℝ) : ℂ) * z‖ ≤ C * (Q ^ (-(δ + σ))) ^ k := by
  have hp : 0 < ρ := by rw [hρ]; exact Real.rpow_pos_of_pos hQ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _)]
  calc
    ρ ^ σ * ‖z‖ ≤ ρ ^ σ * (C * ρ ^ δ) :=
      mul_le_mul_of_nonneg_left hz (Real.rpow_nonneg hp.le _)
    _ = C * ρ ^ (δ + σ) := by
      calc
        _ = C * (ρ ^ δ * ρ ^ σ) := by ring
        _ = _ := by rw [← Real.rpow_add hp]
    _ = C * (Q ^ (-(δ + σ))) ^ k := by
      rw [hρ, ← Real.rpow_mul hQ.le, ← Real.rpow_mul_natCast hQ.le]
      congr 2
      ring

/-- Weighted L1 of the small-norm tail, with ratio Q^(-(delta+sigma)).
The radius and the actual measure of each shell must still be verified when
applying this to a local field. -/
theorem artinWeightedValuationTail_integrableOn {f : X → ℂ} {ρ : X → ℝ}
    {S : ℕ → Set X} (hm : ∀ k, MeasurableSet (S k))
    (hf : AEStronglyMeasurable f μ) (hρm : Measurable ρ)
    {Q δ σ C m : ℝ} (hQ : 1 < Q) (hσ : 0 < δ + σ)
    (hC : 0 ≤ C) (hmass : 0 ≤ m)
    (hfin : ∀ k, μ (S k) < ⊤) (hμ : ∀ k, μ.real (S k) ≤ m)
    (hρ : ∀ k x, x ∈ S k → ρ x = Q ^ (-(k : ℝ)))
    (hb : ∀ k x, x ∈ S k → ‖f x‖ ≤ C * (ρ x) ^ δ) :
    IntegrableOn (fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x) (⋃ k, S k) μ := by
  have hr := artinValuationShell_ratio hQ hσ
  apply artinGeometricShell_integrableOn hm
    ((Complex.measurable_ofReal.comp (hρm.pow_const σ)).aestronglyMeasurable.mul hf)
    hC hmass hr.1.le hr.2 hfin hμ
  intro k x hx
  exact artinValuationShell_weighted_envelope (by linarith) (hρ k x hx) (hb k x hx)

/-- The finitely many large-norm shells can be supplied together as T. It is
their weighted integrability, rather than compact multiplicative support at
zero, that is required. -/
theorem artinWeightedValuationFactor_integrable {f : X → ℂ} {ρ : X → ℝ}
    {S : ℕ → Set X} {T : Set X} (hm : ∀ k, MeasurableSet (S k))
    (hf : AEStronglyMeasurable f μ) (hρm : Measurable ρ)
    {Q δ σ C m : ℝ} (hQ : 1 < Q) (hσ : 0 < δ + σ)
    (hC : 0 ≤ C) (hmass : 0 ≤ m)
    (hfin : ∀ k, μ (S k) < ⊤) (hμ : ∀ k, μ.real (S k) ≤ m)
    (hρ : ∀ k x, x ∈ S k → ρ x = Q ^ (-(k : ℝ)))
    (hb : ∀ k x, x ∈ S k → ‖f x‖ ≤ C * (ρ x) ^ δ)
    (hT : IntegrableOn (fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x) T μ)
    (hs : Function.support f ⊆ T ∪ ⋃ k, S k) :
    Integrable (fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x) μ := by
  have hi := hT.union
    (artinWeightedValuationTail_integrableOn hm hf hρm hQ hσ hC hmass hfin hμ hρ hb)
  apply (integrableOn_iff_integrable_of_support_subset (s := T ∪ ⋃ k, S k) ?_).mp hi
  intro x hx
  apply hs
  exact Function.mem_support.mpr (fun hz => by
    exact (Function.mem_support.mp hx) (by simp [hz]))

section HaarShells

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    {ν : Measure G} [ν.IsMulLeftInvariant]

theorem artinMultiplicativeHaarShell_mass (a : G) (U : Set G) :
    ν (a • U) = ν U := measure_smul ν a U

theorem artinMultiplicativeHaarShell_measurable (a : G) {U : Set G}
    (hU : MeasurableSet U) : MeasurableSet (a • U) := by
  change MeasurableSet ((MeasurableEquiv.mulLeft a) '' U)
  exact (MeasurableEquiv.mulLeft a).measurableSet_image.mpr hU

omit [MeasurableSpace G] [MeasurableMul G] in
theorem artinMultiplicativeHaarShell_radius (ρ : G →* ℝ) {π : G} {U : Set G}
    {Q : ℝ} (hQ : 0 < Q) (hπ : ρ π = Q ^ (-1 : ℝ))
    (hU : ∀ u ∈ U, ρ u = 1) (k : ℕ) {x : G} (hx : x ∈ π ^ k • U) :
    ρ x = Q ^ (-(k : ℝ)) := by
  obtain ⟨u, hu, rfl⟩ := hx
  dsimp only
  rw [smul_eq_mul, map_mul, map_pow, hπ, hU u hu, mul_one,
    ← Real.rpow_mul_natCast hQ.le]
  congr 1
  ring

/-- Uniform shell masses are proved by multiplicative Haar invariance. Only
the local radius convention, unit shell and local-factor envelope remain as
inputs. This applies to an arbitrary actual invariant measure. -/
theorem artinHaarValuationTail_integrableOn {f : G → ℂ} (ρ : G →* ℝ)
    (hρm : Measurable ρ) (hf : AEStronglyMeasurable f ν)
    {π : G} {U : Set G} (hUm : MeasurableSet U) (hUfin : ν U < ⊤)
    {Q δ σ C : ℝ} (hQ : 1 < Q) (hσ : 0 < δ + σ) (hC : 0 ≤ C)
    (hπ : ρ π = Q ^ (-1 : ℝ)) (hU : ∀ u ∈ U, ρ u = 1)
    (hb : ∀ k x, x ∈ π ^ k • U → ‖f x‖ ≤ C * (ρ x) ^ δ) :
    IntegrableOn (fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x) (⋃ k : ℕ, π ^ k • U) ν := by
  apply artinWeightedValuationTail_integrableOn
    (fun k => artinMultiplicativeHaarShell_measurable (π ^ k) hUm) hf hρm hQ hσ hC
    (m := ν.real U) (by positivity)
  · intro k
    rwa [artinMultiplicativeHaarShell_mass]
  · intro k
    simp only [Measure.real, artinMultiplicativeHaarShell_mass, le_refl]
  · exact fun k x hx => artinMultiplicativeHaarShell_radius ρ (by linarith) hπ hU k hx
  · exact hb

theorem artinHaarValuationFactor_integrable {f : G → ℂ} (ρ : G →* ℝ)
    (hρm : Measurable ρ) (hf : AEStronglyMeasurable f ν)
    {π : G} {U T : Set G} (hUm : MeasurableSet U) (hUfin : ν U < ⊤)
    {Q δ σ C : ℝ} (hQ : 1 < Q) (hσ : 0 < δ + σ) (hC : 0 ≤ C)
    (hπ : ρ π = Q ^ (-1 : ℝ)) (hU : ∀ u ∈ U, ρ u = 1)
    (hb : ∀ k x, x ∈ π ^ k • U → ‖f x‖ ≤ C * (ρ x) ^ δ)
    (hT : IntegrableOn (fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x) T ν)
    (hs : Function.support f ⊆ T ∪ ⋃ k : ℕ, π ^ k • U) :
    Integrable (fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x) ν := by
  apply artinWeightedValuationFactor_integrable
    (fun k => artinMultiplicativeHaarShell_measurable (π ^ k) hUm) hf hρm hQ hσ hC
    (m := ν.real U) (by positivity)
  · intro k
    rwa [artinMultiplicativeHaarShell_mass]
  · intro k
    simp only [Measure.real, artinMultiplicativeHaarShell_mass, le_refl]
  · exact fun k x hx => artinMultiplicativeHaarShell_radius ρ (by linarith) hπ hU k hx
  · exact hb
  · exact hT
  · exact hs

end HaarShells

end
end SimultaneousPrimitiveRoots
