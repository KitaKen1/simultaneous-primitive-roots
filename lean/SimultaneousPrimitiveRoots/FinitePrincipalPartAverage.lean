module

public import SimultaneousPrimitiveRoots.ComplexInverseKernel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Metric MeasureTheory Set
noncomputable section
open Classical

theorem complexPrincipalPart_norm (m : ℕ) (ρ z : ℂ) :
    ‖(m : ℂ) / (z - ρ)‖ = (m : ℝ) * complexInverseDistanceKernel ρ z := by
  rw [norm_div, Complex.norm_natCast]
  rfl

theorem complexPrincipalPart_integrableOn {S : Set ℂ}
    (hS : MeasurableSet S) (hvol : volume S ≠ ⊤) (m : ℕ) (ρ : ℂ) :
    IntegrableOn (fun z : ℂ => (m : ℂ) / (z - ρ)) S := by
  have hm : AEStronglyMeasurable (fun z : ℂ => (m : ℂ) / (z - ρ)) (volume.restrict S) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  apply (integrable_norm_iff hm).mp
  have hi := (complexInverseDistanceKernel_integral_le hS hvol ρ).1.const_mul (m : ℝ)
  exact hi.congr (Filter.Eventually.of_forall (fun z => (complexPrincipalPart_norm m ρ z).symm))

theorem finitePrincipalParts_integrableOn {S : Set ℂ}
    (hS : MeasurableSet S) (hvol : volume S ≠ ⊤)
    {ι : Type*} (F : Finset ι) (m : ι → ℕ) (c : ι → ℂ) :
    IntegrableOn (fun z : ℂ => ∑ ρ ∈ F, (m ρ : ℂ) / (z - c ρ)) S :=
  integrable_finsetSum F (fun ρ _ => complexPrincipalPart_integrableOn hS hvol (m ρ) (c ρ))

/-- Multiplicities, rather than only the number of distinct poles, control
this uniform spatial integral. Pole locations need not be separated. -/
theorem finitePrincipalParts_norm_integral_le {S : Set ℂ}
    (hS : MeasurableSet S) (hvol : volume S ≠ ⊤)
    {ι : Type*} (F : Finset ι) (m : ι → ℕ) (c : ι → ℂ) :
    (∫ z : ℂ in S, ‖∑ ρ ∈ F, (m ρ : ℂ) / (z - c ρ)‖) ≤
      (2 * Real.pi + (volume S).toReal) * ∑ ρ ∈ F, (m ρ : ℝ) := by
  have hp := (finitePrincipalParts_integrableOn hS hvol F m c).norm
  have ht : ∀ ρ ∈ F,
      IntegrableOn (fun z : ℂ => ‖(m ρ : ℂ) / (z - c ρ)‖) S :=
    fun ρ _ => (complexPrincipalPart_integrableOn hS hvol (m ρ) (c ρ)).norm
  have hu := integral_mono hp (integrable_finsetSum F ht)
    (fun z => norm_sum_le _ _)
  rw [integral_finsetSum F ht] at hu
  apply hu.trans
  calc ∑ ρ ∈ F, ∫ z : ℂ in S, ‖(m ρ : ℂ) / (z - c ρ)‖
      = ∑ ρ ∈ F, (m ρ : ℝ) * ∫ z : ℂ in S, complexInverseDistanceKernel (c ρ) z := by
        apply Finset.sum_congr rfl
        intro ρ _
        simp_rw [complexPrincipalPart_norm]
        rw [integral_const_mul]
    _ ≤ ∑ ρ ∈ F, (m ρ : ℝ) * (2 * Real.pi + (volume S).toReal) := by
      apply Finset.sum_le_sum
      intro ρ _
      exact mul_le_mul_of_nonneg_left (complexInverseDistanceKernel_integral_le hS hvol (c ρ)).2
        (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end
end SimultaneousPrimitiveRoots
