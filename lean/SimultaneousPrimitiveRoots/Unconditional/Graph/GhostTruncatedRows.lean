module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostSectorExactRows
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cutoff-independent rows of the complete finite ghost kernel

The admissible (target degree, survivor count) lattice injects into the
deletion/birth rectangle. Every deletion cardinality is then counted by the
binomial theorem. This bounds the actual full row, rather than adding
independent sector constants.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P : Type*} {R : P → Type*}

theorem ghost_choose_degree_sum (A X : ℝ) (z n : ℕ) (hz : z ≤ n) :
    (∑ a ∈ Finset.range (n + 1), (Nat.choose z a : ℝ) * X ^ a * A ^ (z - a)) =
      (A + X) ^ z := by
  classical
  calc
    _ = ∑ a ∈ Finset.range (z + 1), (Nat.choose z a : ℝ) * X ^ a * A ^ (z - a) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hz 1))
      intro a _ ha
      have hza : z < a := by
        have h : ¬ a < z + 1 := by simpa only [Finset.mem_range] using ha
        omega
      rw [Nat.choose_eq_zero_of_lt hza, Nat.cast_zero, zero_mul, zero_mul]
    _ = (X + A) ^ z := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [add_comm X A]

/-- Each admissible sector maps to one distinct deletion/birth pair. -/
theorem ghost_degree_lattice_sum_le_rectangle (N n : ℕ) (F : ℕ → ℕ → ℝ)
    (hF : ∀ a b, 0 ≤ F a b) :
    (∑ m : Fin (N + 1), ∑ k ∈ Finset.range (min n m.val + 1), F (n - k) (m.val - k)) ≤
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (N + 1), F a b := by
  classical
  let S : Finset (Σ _ : Fin (N + 1), ℕ) :=
    Finset.univ.sigma (fun m => Finset.range (min n m.val + 1))
  let T := (Finset.range (n + 1)).product (Finset.range (N + 1))
  let e : (Σ _ : Fin (N + 1), ℕ) → ℕ × ℕ := fun i => (n - i.2, i.1.val - i.2)
  have hi (i : Σ _ : Fin (N + 1), ℕ) (h : i ∈ S) : i.2 ≤ n ∧ i.2 ≤ i.1.val := by
    have hk : i.2 < min n i.1.val + 1 := Finset.mem_range.mp (Finset.mem_sigma.mp h).2
    exact ⟨(Nat.lt_succ_iff.mp hk).trans (min_le_left _ _),
      (Nat.lt_succ_iff.mp hk).trans (min_le_right _ _)⟩
  have hinj : Set.InjOn e S := by
    intro i hsi j hsj hij
    have h0 : n - i.2 = n - j.2 := congrArg Prod.fst hij
    have h1 : i.1.val - i.2 = j.1.val - j.2 := congrArg Prod.snd hij
    have hki := hi i hsi
    have hkj := hi j hsj
    have hkk : i.2 = j.2 := by omega
    have hmm : i.1 = j.1 := Fin.ext (by omega)
    exact Sigma.ext hmm (heq_of_eq hkk)
  have hmap : S.image e ⊆ T := by
    rintro p hp
    rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by dsimp [e]; omega),
      Finset.mem_range.mpr (by dsimp [e]; have h := i.1.isLt; omega)⟩
  have h : (∑ i ∈ S, F (n - i.2) (i.1.val - i.2)) ≤ ∑ p ∈ T, F p.1 p.2 := by
    calc
      _ = ∑ p ∈ S.image e, F p.1 p.2 := by
        simpa only [e] using
          (Finset.sum_image (f := fun p : ℕ × ℕ => F p.1 p.2) hinj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hmap (fun p _ _ => hF p.1 p.2)
  change (∑ i ∈ S, F (n - i.2) (i.1.val - i.2)) ≤
    ∑ p ∈ (Finset.range (n + 1)).product (Finset.range (N + 1)), F p.1 p.2 at h
  rw [Finset.product_eq_sprod, Finset.sum_product'] at h
  simpa only [S, Finset.sum_sigma] using h

/-- The complete deletion/birth rectangle is exactly the previously proved positive row. -/
theorem ghost_choose_rectangle_eq_positive_row [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C v : ℝ) (hv : v ≠ 0) (n B : ℕ) (x : Fin n → Σ p, R p) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range B,
      (Nat.choose (ghostZeroCount x) a : ℝ) * (|D| / v) ^ a *
        A ^ (ghostZeroCount x - a) * ((|C| * v * ∑ p, ν p) ^ b / (b.factorial : ℝ))) =
    positiveGhostWeightedRow ν A D C v x B := by
  classical
  have hz : ghostZeroCount x ≤ n := by
    simpa only [ghost_zero_positions_card, Fintype.card_fin] using
      (Finset.card_le_univ (ghostZeroPositions x))
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ghost_choose_degree_sum A (|D| / v) _ n hz,
    positive_ghost_weighted_row_eq ν A D C v hv x B]

/-- The actual complete finite kernel row is a subsum of one positive ghost row. -/
theorem finite_ghost_truncated_kernel_weighted_row_le_positive [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v : ℝ)
    (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hv : 0 < v) (N : ℕ)
    (x : FiniteMemory N (Σ p, R p)) :
    (∑ y : FiniteMemory N (Σ p, R p),
      finiteGhostTruncatedKernel ν A |D| |C| N x y * v ^ y.1.val / v ^ x.1.val) ≤
      positiveGhostWeightedRow ν A D C v x.2 (N + 1) := by
  classical
  let z := ghostZeroCount x.2
  let F : ℕ → ℕ → ℝ := fun a b => (Nat.choose z a : ℝ) * (|D| / v) ^ a *
    A ^ (z - a) * ((|C| * v * ∑ p, ν p) ^ b / (b.factorial : ℝ))
  have hF : ∀ a b, 0 ≤ F a b := by
    intro a b
    dsimp [F]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (div_nonneg (abs_nonneg _) hv.le) _)) (pow_nonneg hA _))
      (div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hv.le)
        (Finset.sum_nonneg (fun p _ => hν p))) _) (Nat.cast_nonneg _))
  have hr (m : Fin (N + 1)) (k : ℕ) (hk : k ∈ Finset.range (min x.1.val m.val + 1)) :
      (∑ y : Fin m.val → Σ p, R p,
        finiteGhostDegreeKernel ν A |D| |C| k x.1.val m.val x.2 y) *
          v ^ m.val / v ^ x.1.val = F (x.1.val - k) (m.val - k) := by
    have hkn : k ≤ x.1.val := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans
      (min_le_left _ _)
    have hkm : k ≤ m.val := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans
      (min_le_right _ _)
    have h := finite_ghost_degree_kernel_reproduces ν A |D| |C| k x.1.val m.val
      (fun _ => (1 : ℝ)) (fun _ _ => rfl) x.2
    simp only [mul_one] at h
    rw [h, finite_ghost_degree_row_one_exact, if_pos ⟨hkn, hkm⟩]
    have ht := ghost_row_term_factorization A D C v (∑ p, ν p) hv.ne'
      x.1.val z (x.1.val - k) (m.val - k) (Nat.sub_le _ _)
    have hm : x.1.val - (x.1.val - k) + (m.val - k) = m.val := by omega
    rw [hm] at ht
    calc
      _ = (Nat.choose z (x.1.val - k) : ℝ) *
          ((|D| / v) ^ (x.1.val - k) * A ^ (z - (x.1.val - k)) *
            ((|C| * v * ∑ p, ν p) ^ (m.val - k) / ((m.val - k).factorial : ℝ))) := by
        rw [← ht, mul_pow]
        ring
      _ = _ := by dsimp [F]; ring
  calc
    _ = ∑ m : Fin (N + 1), ∑ k ∈ Finset.range (min x.1.val m.val + 1),
        F (x.1.val - k) (m.val - k) := by
      unfold finiteGhostTruncatedKernel
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro m _
      simp_rw [Finset.sum_mul, Finset.sum_div]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_div, ← Finset.sum_mul]
      exact hr m k hk
    _ ≤ ∑ a ∈ Finset.range (x.1.val + 1), ∑ b ∈ Finset.range (N + 1), F a b :=
      ghost_degree_lattice_sum_le_rectangle N x.1.val F hF
    _ = _ := ghost_choose_rectangle_eq_positive_row ν A D C v hv.ne' _ _ x.2

theorem finite_ghost_truncated_kernel_weighted_row_le_uniform_exp [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax Mmax : ℝ)
    (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hv : 0 < v) (hbase : A + |D| / v ≤ 1)
    (hC : |C| ≤ cmax) (hM : ∑ p, ν p ≤ Mmax) (N : ℕ)
    (x : FiniteMemory N (Σ p, R p)) :
    (∑ y : FiniteMemory N (Σ p, R p),
      finiteGhostTruncatedKernel ν A |D| |C| N x y * v ^ y.1.val / v ^ x.1.val) ≤
      Real.exp (cmax * v * Mmax) :=
  (finite_ghost_truncated_kernel_weighted_row_le_positive ν A D C v hν hA hv N x).trans
    (positive_ghost_weighted_row_le_uniform_exp ν A D C v cmax Mmax
      hν hA hv hbase hC hM x.2 (N + 1))

/-- Exact full transpose gives the full column constant without any cutoff factor. -/
theorem finite_ghost_truncated_kernel_weighted_column_le_uniform_exp [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v dmax Mmax : ℝ)
    (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hv : 0 < v) (hbase : A + |C| / v ≤ 1)
    (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax) (N : ℕ)
    (y : FiniteMemory N (Σ p, R p)) :
    (∑ x : FiniteMemory N (Σ p, R p),
      finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        finiteGhostTruncatedKernel ν A |D| |C| N x y * v ^ x.1.val / v ^ y.1.val) ≤
    finiteMemoryPointMass (fun z : Σ p, R p => ν z.1) y * Real.exp (dmax * v * Mmax) := by
  classical
  rw [← Finset.sum_div,
    finite_ghost_truncated_kernel_weighted_column ν A |D| |C| N (fun x => v ^ x.1.val),
    mul_div_assoc, Finset.sum_div]
  apply mul_le_mul_of_nonneg_left
    (finite_ghost_truncated_kernel_weighted_row_le_uniform_exp ν A C D v dmax Mmax
      hν hA hv hbase hD hM N y)
  unfold finiteMemoryPointMass factorialMemoryPointMass
  exact div_nonneg (Finset.prod_nonneg (fun i _ => hν (y.2 i).1)) (Nat.cast_nonneg _)

end SimultaneousPrimitiveRoots.Unconditional.Graph
