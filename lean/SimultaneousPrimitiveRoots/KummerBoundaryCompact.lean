module

public import SimultaneousPrimitiveRoots.KummerPowerContinuation
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Set Metric
noncomputable section

/-- The compact segment on the convergence boundary, at a fixed height. -/
def zetaBoundarySegment (T : ℝ) : Set ℂ :=
  (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) '' Icc (-T) T

theorem zetaBoundarySegment_isCompact (T : ℝ) : IsCompact (zetaBoundarySegment T) :=
  isCompact_Icc.image (continuous_const.add (Complex.continuous_ofReal.mul_const _))

theorem zetaBoundarySegment_re {T : ℝ} {s : ℂ} (hs : s ∈ zetaBoundarySegment T) :
    s.re = 1 := by
  obtain ⟨t, _, rfl⟩ := hs
  simp

/-- Finite families admit a common compact tube and finite bounds. The
width and bounds depend on the family and on the compact set. -/
theorem finite_holomorphic_family_compact_tube {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) {S : Set ℂ} (hS : IsCompact S)
    (hlocal : ∀ i, ∀ x : S, ∃ U : Set ℂ, IsOpen U ∧ (x : ℂ) ∈ U ∧
      DifferentiableOn ℂ (f i) U ∧ ∀ z ∈ U, f i z ≠ 0) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧ ∀ i, ∀ z ∈ cthickening ε S,
      DifferentiableAt ℂ (f i) z ∧ f i z ≠ 0 ∧
      ‖f i z‖ ≤ M ∧ ‖(f i z)⁻¹‖ ≤ M ∧ ‖logDeriv (f i) z‖ ≤ M := by
  classical
  choose U ho hx hd hn using hlocal
  let V : Set ℂ := ⋃ x : S, ⋂ i, U i x
  have hVo : IsOpen V := isOpen_iUnion (fun x => isOpen_iInter_of_finite (fun i => ho i x))
  have hSV : S ⊆ V := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_iInter.mpr (fun i => hx i ⟨z, hz⟩)⟩
  have hVd : ∀ i, DifferentiableOn ℂ (f i) V := by
    intro i z hz
    obtain ⟨x, hzx⟩ := mem_iUnion.mp hz
    exact ((hd i x).differentiableAt ((ho i x).mem_nhds (mem_iInter.mp hzx i))).differentiableWithinAt
  have hVn : ∀ i, ∀ z ∈ V, f i z ≠ 0 := by
    intro i z hz
    obtain ⟨x, hzx⟩ := mem_iUnion.mp hz
    exact hn i x z (mem_iInter.mp hzx i)
  obtain ⟨ε, hε, hεV⟩ := hS.exists_cthickening_subset_open hVo hSV
  have hSc : IsCompact (cthickening ε S) := hS.cthickening
  have hbound : ∀ i, ∃ C : ℝ, ∀ z ∈ cthickening ε S,
      ‖f i z‖ + ‖(f i z)⁻¹‖ + ‖logDeriv (f i) z‖ ≤ C := by
    intro i
    have hc : ContinuousOn (fun z => ‖f i z‖ + ‖(f i z)⁻¹‖ + ‖logDeriv (f i) z‖) V :=
      (((hVd i).continuousOn.norm.add ((hVd i).continuousOn.inv₀ (hVn i)).norm).add
        (((hVd i).deriv hVo).continuousOn.div (hVd i).continuousOn (hVn i)).norm)
    obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hc.mono hεV)
    exact ⟨C, fun z hz => (le_abs_self _).trans (hC z hz)⟩
  choose C hC using hbound
  let M : ℝ := 1 + ∑ i, max 0 (C i)
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hCM : ∀ i, C i ≤ M := by
    intro i
    have hi : max 0 (C i) ≤ ∑ j, max 0 (C j) :=
      Finset.single_le_sum (fun j _ => le_max_left _ _) (Finset.mem_univ i)
    dsimp [M]
    linarith [le_max_right 0 (C i)]
  refine ⟨ε, M, hε, hM, fun i z hz => ?_⟩
  have hsum := (hC i z hz).trans (hCM i)
  refine ⟨(hVd i).differentiableAt (hVo.mem_nhds (hεV hz)), hVn i z (hεV hz), ?_, ?_, ?_⟩ <;>
    linarith [norm_nonneg (f i z), norm_nonneg ((f i z)⁻¹), norm_nonneg (logDeriv (f i) z)]

/-- Points in the finite-height rectangle are in the compact tube. -/
theorem zetaBoundaryRectangle_mem_cthickening {T ε : ℝ} {s : ℂ}
    (hσ : 1 - ε ≤ s.re ∧ s.re ≤ 1 + ε) (ht : |s.im| ≤ T) :
    s ∈ cthickening ε (zetaBoundarySegment T) := by
  have hy : (1 : ℂ) + (s.im : ℂ) * Complex.I ∈ zetaBoundarySegment T :=
    ⟨s.im, abs_le.mp ht, rfl⟩
  apply mem_cthickening_of_dist_le s _ ε _ hy
  have hsub : s - ((1 : ℂ) + (s.im : ℂ) * Complex.I) = ((s.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩

/-- A common nonzero holomorphic tube for any fixed finite family of
actual Kummer common powers. No growing-q quantitative bound is supplied. -/
theorem primeKummerPower_finite_boundary_tube {ι : Type*} [Fintype ι]
    (a q : ι → ℕ) [∀ i, Fact (2 ≤ a i)] [∀ i, Fact (q i).Prime]
    [∀ i, Fact (a i < q i)] (T : ℝ) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧ ∀ i, ∀ s ∈ cthickening ε (zetaBoundarySegment T),
      DifferentiableAt ℂ (primeKummerIncompletePowerContinuation (a i) (q i)) s ∧
      primeKummerIncompletePowerContinuation (a i) (q i) s ≠ 0 ∧
      ‖primeKummerIncompletePowerContinuation (a i) (q i) s‖ ≤ M ∧
      ‖(primeKummerIncompletePowerContinuation (a i) (q i) s)⁻¹‖ ≤ M ∧
      ‖logDeriv (primeKummerIncompletePowerContinuation (a i) (q i)) s‖ ≤ M := by
  apply finite_holomorphic_family_compact_tube _ (zetaBoundarySegment_isCompact T)
  intro i s
  exact primeKummerIncompletePowerContinuation_exists_neighborhood (a i) (q i)
    (by rw [zetaBoundarySegment_re s.property])
    |>.imp fun U h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The same package is stated as a rectangular finite-height strip. -/
theorem primeKummerPower_finite_boundary_rectangle {ι : Type*} [Fintype ι]
    (a q : ι → ℕ) [∀ i, Fact (2 ≤ a i)] [∀ i, Fact (q i).Prime]
    [∀ i, Fact (a i < q i)] (T : ℝ) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧ ∀ i, ∀ s : ℂ,
      1 - ε ≤ s.re → s.re ≤ 1 + ε → |s.im| ≤ T →
      DifferentiableAt ℂ (primeKummerIncompletePowerContinuation (a i) (q i)) s ∧
      primeKummerIncompletePowerContinuation (a i) (q i) s ≠ 0 ∧
      ‖primeKummerIncompletePowerContinuation (a i) (q i) s‖ ≤ M ∧
      ‖(primeKummerIncompletePowerContinuation (a i) (q i) s)⁻¹‖ ≤ M ∧
      ‖logDeriv (primeKummerIncompletePowerContinuation (a i) (q i)) s‖ ≤ M := by
  obtain ⟨ε, M, hε, hM, h⟩ := primeKummerPower_finite_boundary_tube a q T
  exact ⟨ε, M, hε, hM, fun i s hleft hright ht =>
    h i s (zetaBoundaryRectangle_mem_cthickening ⟨hleft, hright⟩ ht)⟩

/-- The actual finite family with a in A and prime a<q<=N. -/
def primeKummerParametersBelow (A : Finset ℕ) (N : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ Finset.range (N + 1)).filter (fun p => 2 ≤ p.1 ∧ p.2.Prime ∧ p.1 < p.2)

theorem mem_primeKummerParametersBelow {A : Finset ℕ} {N a q : ℕ} :
    (a, q) ∈ primeKummerParametersBelow A N ↔
      a ∈ A ∧ q ≤ N ∧ 2 ≤ a ∧ q.Prime ∧ a < q := by
  simp [primeKummerParametersBelow, Nat.lt_succ_iff, and_assoc, and_left_comm, and_comm]

/-- Uniformity over the actual bounded family. The constants may depend
on N and T, so this does not establish a fixed delta for growing q. -/
theorem primeKummerPower_bounded_family_rectangle (A : Finset ℕ) (N : ℕ) (T : ℝ) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧ ∀ a ∈ A, ∀ q : ℕ,
      ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q, q ≤ N →
      letI : Fact (2 ≤ a) := ⟨ha⟩
      letI : Fact q.Prime := ⟨hq⟩
      letI : Fact (a < q) := ⟨haq⟩
      ∀ s : ℂ, 1 - ε ≤ s.re → s.re ≤ 1 + ε → |s.im| ≤ T →
        DifferentiableAt ℂ (primeKummerIncompletePowerContinuation a q) s ∧
        primeKummerIncompletePowerContinuation a q s ≠ 0 ∧
        ‖primeKummerIncompletePowerContinuation a q s‖ ≤ M ∧
        ‖(primeKummerIncompletePowerContinuation a q s)⁻¹‖ ≤ M ∧
        ‖logDeriv (primeKummerIncompletePowerContinuation a q) s‖ ≤ M := by
  classical
  let I := {p : ℕ × ℕ // p ∈ primeKummerParametersBelow A N}
  have : ∀ i : I, Fact (2 ≤ i.val.1) :=
    fun i => ⟨(mem_primeKummerParametersBelow.mp i.property).2.2.1⟩
  have : ∀ i : I, Fact i.val.2.Prime :=
    fun i => ⟨(mem_primeKummerParametersBelow.mp i.property).2.2.2.1⟩
  have : ∀ i : I, Fact (i.val.1 < i.val.2) :=
    fun i => ⟨(mem_primeKummerParametersBelow.mp i.property).2.2.2.2⟩
  obtain ⟨ε, M, hε, hM, h⟩ :=
    primeKummerPower_finite_boundary_rectangle (fun i : I => i.val.1) (fun i : I => i.val.2) T
  refine ⟨ε, M, hε, hM, ?_⟩
  intro a haA q ha hq haq hqN
  let i : I := ⟨(a, q), mem_primeKummerParametersBelow.mpr ⟨haA, hqN, ha, hq, haq⟩⟩
  exact h i

/-- The finite bad-q height 2*q^2 is covered at once for q<=N. The
width remains dependent on N, rather than the fixed KR width. -/
theorem primeKummerPower_bounded_family_quadratic_height (A : Finset ℕ) (N : ℕ) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧ ∀ a ∈ A, ∀ q : ℕ,
      ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q, q ≤ N →
      letI : Fact (2 ≤ a) := ⟨ha⟩
      letI : Fact q.Prime := ⟨hq⟩
      letI : Fact (a < q) := ⟨haq⟩
      ∀ s : ℂ, 1 - ε ≤ s.re → s.re ≤ 1 + ε → |s.im| ≤ 2 * (q : ℝ) ^ 2 →
        DifferentiableAt ℂ (primeKummerIncompletePowerContinuation a q) s ∧
        primeKummerIncompletePowerContinuation a q s ≠ 0 ∧
        ‖primeKummerIncompletePowerContinuation a q s‖ ≤ M ∧
        ‖(primeKummerIncompletePowerContinuation a q s)⁻¹‖ ≤ M ∧
        ‖logDeriv (primeKummerIncompletePowerContinuation a q) s‖ ≤ M := by
  obtain ⟨ε, M, hε, hM, h⟩ := primeKummerPower_bounded_family_rectangle A N (2 * (N : ℝ) ^ 2)
  refine ⟨ε, M, hε, hM, ?_⟩
  intro a haA q ha hq haq hqN s hl hr ht
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  exact h a haA q ha hq haq hqN s hl hr
    (ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg q) hqNR 2) (by norm_num)))

end
end SimultaneousPrimitiveRoots
