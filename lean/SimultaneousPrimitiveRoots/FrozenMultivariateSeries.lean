module

public import SimultaneousPrimitiveRoots.FrozenLocalSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section

universe u

set_option maxHeartbeats 1000000 in
/-- A finite number of independent nonnegative summable coordinates has
an actually summable product family, with the expected product as its sum. -/
theorem finite_nonnegative_product_hasSum (ι : Type u) [Fintype ι]
    (f : ι → ℕ → ℝ) (hf0 : ∀ i n, 0 ≤ f i n) (hf : ∀ i, Summable (f i)) :
    HasSum (fun e : ι → ℕ => ∏ i, f i (e i)) (∏ i, ∑' n, f i n) := by
  classical
  let P := fun (α : Type u) [Fintype α] => ∀ (g : α → ℕ → ℝ),
    (∀ i n, 0 ≤ g i n) → (∀ i, Summable (g i)) →
    HasSum (fun e : α → ℕ => ∏ i, g i (e i)) (∏ i, ∑' n, g i n)
  suffices h : P ι from h f hf0 hf
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
  · intro α β _ e ih g hg0 hg
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i n => g (e i) n) (fun i n => hg0 (e i) n) (fun i => hg (e i))
    let E : (α → ℕ) ≃ (β → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
    rw [← e.prod_comp (fun i => ∑' n, g i n)]
    apply E.hasSum_iff.mp
    convert h using 1
    funext x
    change (∏ i : β, g i (E x i)) = _
    rw [← e.prod_comp (fun i => g i (E x i))]
    simp [E, Equiv.arrowCongr_apply]
  · intro g _ _
    simpa using (hasSum_fintype (fun e : PEmpty → ℕ => ∏ i, g i (e i)))
  · intro α _ ih g hg0 hg
    have htail := ih (fun i => g (some i)) (fun i n => hg0 (some i) n)
      (fun i => hg (some i))
    have hp := (hg none).hasSum.mul htail
      ((hg none).mul_of_nonneg htail.summable (hg0 none)
        (fun e => Finset.prod_nonneg fun i _ => hg0 (some i) (e i)))
    let E : (Option α → ℕ) ≃ ℕ × (α → ℕ) := Equiv.piOptionEquivProd
    rw [Fintype.prod_option]
    apply E.symm.hasSum_iff.mp
    simpa only [Function.comp_def, Fintype.prod_option, E,
      Equiv.piOptionEquivProd_symm_apply] using hp

/-- Frozen local coefficients indexed by a full exponent vector. -/
def frozenExponentTerm {ι : Type*} [Fintype ι] (Q : ι → ℝ) (σ : ℝ)
    (e : ι → ℕ) : ℝ :=
  ∏ i, frozenLocalMajorant (Q i) (e i) * (Q i) ^ (-σ * (e i : ℝ))

theorem frozenExponentTerm_nonneg {ι : Type*} [Fintype ι]
    (Q : ι → ℝ) (hQ : ∀ i, 0 ≤ Q i) (σ : ℝ) (e : ι → ℕ) :
    0 ≤ frozenExponentTerm Q σ e := by
  exact Finset.prod_nonneg fun i _ =>
    mul_nonneg (frozenLocalMajorant_nonneg (hQ i) _) (Real.rpow_nonneg (hQ i) _)

theorem frozenExponentTerm_hasSum {ι : Type*} [Fintype ι]
    (Q : ι → ℝ) (hQ : ∀ i, 2 ≤ Q i) {σ : ℝ} (hσ : 0 ≤ σ) :
    HasSum (frozenExponentTerm Q σ) (∏ i, frozenLocalDirichlet (Q i) σ) := by
  exact finite_nonnegative_product_hasSum ι
    (fun i e => frozenLocalMajorant (Q i) e * (Q i) ^ (-σ * (e : ℝ)))
    (fun i e => mul_nonneg (frozenLocalMajorant_nonneg (by linarith [hQ i]) e)
      (Real.rpow_nonneg (by linarith [hQ i]) _))
    (fun i => frozenLocalDirichlet_summable (hQ i) hσ)

theorem frozenExponentTerm_summable {ι : Type*} [Fintype ι]
    (Q : ι → ℝ) (hQ : ∀ i, 2 ≤ Q i) {σ : ℝ} (hσ : 0 ≤ σ) :
    Summable (frozenExponentTerm Q σ) :=
  (frozenExponentTerm_hasSum Q hQ hσ).summable

theorem frozenExponentTerm_tsum {ι : Type*} [Fintype ι]
    (Q : ι → ℝ) (hQ : ∀ i, 2 ≤ Q i) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑' e : ι → ℕ, frozenExponentTerm Q σ e) =
      ∏ i, frozenLocalDirichlet (Q i) σ :=
  (frozenExponentTerm_hasSum Q hQ hσ).tsum_eq

end
end SimultaneousPrimitiveRoots
