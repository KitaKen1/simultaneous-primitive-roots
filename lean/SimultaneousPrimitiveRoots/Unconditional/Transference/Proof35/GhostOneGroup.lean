module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.GhostCompat
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostTruncatedRows
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The absolute one-group ghost row with doubled births

Source: `verification/stage7-sources/S-02.tex`, lines 681–702 (`[S-02:0681–0702]`),
(eq:ghost-schur-ratios), (eq:ghost-absolute-bound).

For one big group `g` and one visit `i`:

* `ghostAbsG` — the absolute coefficient `2^b |ghostCoefG|` of (eq:ghost-row) "with doubled ghost
  births", for new memories of size at most `Bc`;
* `ghostAbsKernel` — the kernel `Graph.finiteGhostTruncatedKernel` with the coefficients
  `A_i, |D_i|, |2 C_i|`;
* `ghostAbs_row_eq_kernel` — on functions which are symmetric in the particle indices, the absolute
  row is the action of the kernel (the general form `ghostRowGen_eq_truncatedRow` of
  `GhostRowCompat`, and `Graph.finite_ghost_truncated_kernel_reproduces`);
* `ghostAbsKernel_row_le`, `ghostAbsKernel_col_le` — the weighted row and column ratios
  (eq:ghost-schur-ratios) for the weight `v^j`, bounded by the full exponential uniformly in the
  cutoff (`Graph.finite_ghost_truncated_kernel_weighted_row_le_uniform_exp`, `…_column_…`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- The modulus of a coefficient (eq:ghost-row) with a doubled birth coefficient. -/
theorem abs_coef_doubled (d a c P : ℝ) (m e b : ℕ) (ha : 0 ≤ a) (hP : 0 ≤ P) :
    (2 : ℝ) ^ b * |d ^ m * a ^ e * (c ^ b / (b.factorial : ℝ)) * P| =
      |d| ^ m * a ^ e * (|2 * c| ^ b / (b.factorial : ℝ)) * P := by
  have hb : (0 : ℝ) < (b.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos b)
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (pow_nonneg ha e), abs_of_nonneg hP,
    abs_div, abs_pow, abs_of_pos hb, abs_mul, abs_two, mul_pow]
  ring

section OneGroup

variable {S B : Type} {𝒢 : GroupFamily S B} {Bc : ℕ} {g : B}

/-- The new memory of a visit operation has the size `ghostNewSize` when this is at most the
cutoff. -/
theorem ghostNewMem_size (z : Mem 𝒢 Bc g) (c : Finset (Fin Bc) × Batch 𝒢 Bc g)
    (h : ghostNewSize z c ≤ Bc) : (ghostNewMem z c).1.val = ghostNewSize z c := by
  have hl : (ghostSurvivors z c.1 ++ batchParticles c.2).length = ghostNewSize z c := by
    rw [List.length_append]
    unfold batchParticles ghostNewSize
    rw [List.length_ofFn]
  unfold ghostNewMem
  rw [memOfList_size (hl.le.trans h), hl]

/-- The point masses `λ_g^{⊗j} / j!` of a memory are nonnegative. -/
theorem memPointMass_nonneg (q : ℝ) (n : ℕ)
    (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (u : Mem 𝒢 Bc g) :
    0 ≤ Graph.finiteMemoryPointMass (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) q n z.1) u := by
  unfold Graph.finiteMemoryPointMass Graph.factorialMemoryPointMass
  exact div_nonneg (Finset.prod_nonneg fun i _ => hν _ (u.2 i).1.2) (Nat.cast_nonneg _)

/-- **The absolute coefficient of the one-group ghost row with doubled births**
[S-02:0699–0702], for new memories of size at most `Bc`: `2^b |ghostCoefG|`. -/
def ghostAbsG (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B) (z : Mem 𝒢 Bc g)
    (c : Finset (Fin Bc) × Batch 𝒢 Bc g) : ℝ :=
  if ghostNewSize z c ≤ Bc then (2 : ℝ) ^ c.2.1.val * |ghostCoefG 𝒢 q ρ n i g z c| else 0

theorem ghostAbsG_nonneg (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B) (z : Mem 𝒢 Bc g)
    (c : Finset (Fin Bc) × Batch 𝒢 Bc g) : 0 ≤ ghostAbsG 𝒢 q ρ n i g z c := by
  unfold ghostAbsG
  split_ifs
  · exact mul_nonneg (pow_nonneg (by norm_num) _) (abs_nonneg _)
  · exact le_rfl

/-- **The absolute kernel of the one-group ghost row with doubled births**: the truncated ghost
kernel of `Graph/` with the coefficients `A_i`, `|D_i|`, `|2 C_i|` and the weights `μ̃_g`. -/
def ghostAbsKernel (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B) (Bc : ℕ)
    (z y : Mem 𝒢 Bc g) : ℝ :=
  Graph.finiteGhostTruncatedKernel (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
    (Graph.sourceGhostA (visitQ q n i) ρ) |Graph.sourceGhostD (visitQ q n i) ρ|
    |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ| Bc z y

theorem ghostAbsKernel_nonneg (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B)
    (hA : 0 ≤ Graph.sourceGhostA (visitQ q n i) ρ)
    (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (z y : Mem 𝒢 Bc g) :
    0 ≤ ghostAbsKernel 𝒢 q ρ n i g Bc z y := by
  unfold ghostAbsKernel
  exact Graph.finite_ghost_truncated_kernel_nonneg
    (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
    (Graph.sourceGhostA (visitQ q n i) ρ) |Graph.sourceGhostD (visitQ q n i) ρ|
    |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ|
    (fun p => hν p.1 p.2) hA (abs_nonneg _) (abs_nonneg _) Bc z y

open _root_.Classical in
/-- The absolute coefficient times a value of a test function is the term of the general row
`ghostRowGen` with the coefficients `A_i`, `|D_i|`, `|2 C_i|`. -/
theorem ghostAbsG_mul_eq_genTerm (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B)
    (hA : 0 ≤ Graph.sourceGhostA (visitQ q n i) ρ)
    (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (h : Mem 𝒢 Bc g → ℝ) (z : Mem 𝒢 Bc g)
    (A' : Finset (Fin Bc)) (β : Batch 𝒢 Bc g) :
    ghostAbsG 𝒢 q ρ n i g z (A', β) * h (ghostNewMem z (A', β)) =
      ghostGenTerm (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
        (Graph.sourceGhostA (visitQ q n i) ρ) |Graph.sourceGhostD (visitQ q n i) ρ|
        |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ|
        h z A' β := by
  have hcoef : (2 : ℝ) ^ β.1.val * |ghostCoefG 𝒢 q ρ n i g z (A', β)| =
      if GhostValid z A' then
        |Graph.sourceGhostD (visitQ q n i) ρ| ^ A'.card *
          Graph.sourceGhostA (visitQ q n i) ρ ^ (memZeroCount z - A'.card) *
          (|2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ| ^
            β.1.val / (β.1.val.factorial : ℝ)) *
          ∏ j, tiltLaw (𝒢.big g) q n (β.2 j)
      else 0 := by
    by_cases hv : GhostValid z A'
    · have h1 : ghostCoefG 𝒢 q ρ n i g z (A', β) =
          Graph.sourceGhostD (visitQ q n i) ρ ^ A'.card *
            Graph.sourceGhostA (visitQ q n i) ρ ^ (memZeroCount z - A'.card) *
            (Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ ^
              β.1.val / (β.1.val.factorial : ℝ)) *
            ∏ j, tiltLaw (𝒢.big g) q n (β.2 j) := by
        unfold ghostCoefG
        exact if_pos hv
      rw [if_pos hv, h1]
      exact abs_coef_doubled _ _ _ _ _ _ _ hA (Finset.prod_nonneg fun j _ => hν _ (β.2 j).2)
    · have h1 : ghostCoefG 𝒢 q ρ n i g z (A', β) = 0 := by
        unfold ghostCoefG
        exact if_neg hv
      rw [if_neg hv, h1, abs_zero, mul_zero]
  unfold ghostAbsG ghostGenTerm
  by_cases hsize : ghostNewSize z (A', β) ≤ Bc
  · rw [if_pos hsize, if_pos hsize]
    exact congrArg (fun t => t * h (ghostNewMem z (A', β)))
      (hcoef.trans (ite_congr_of_iff Iff.rfl rfl rfl))
  · rw [if_neg hsize, if_neg hsize, zero_mul]

/-- **The absolute one-group row is the action of the absolute kernel** on the functions which are
symmetric in the particle indices. -/
theorem ghostAbs_row_eq_kernel (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B)
    (hA : 0 ≤ Graph.sourceGhostA (visitQ q n i) ρ)
    (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (h : Mem 𝒢 Bc g → ℝ)
    (hh : ∀ (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val)) (y : Fin m.val → Particle 𝒢 g),
      h ⟨m, y ∘ σ⟩ = h ⟨m, y⟩) (z : Mem 𝒢 Bc g) :
    ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g, ghostAbsG 𝒢 q ρ n i g z c * h (ghostNewMem z c) =
      ∑ y : Mem 𝒢 Bc g, ghostAbsKernel 𝒢 q ρ n i g Bc z y * h y := by
  have h1 : ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g,
        ghostAbsG 𝒢 q ρ n i g z c * h (ghostNewMem z c) =
      ghostRowGen (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
        (Graph.sourceGhostA (visitQ q n i) ρ) |Graph.sourceGhostD (visitQ q n i) ρ|
        |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ|
        h z := by
    unfold ghostRowGen
    refine Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨A', β⟩ := c
    exact ghostAbsG_mul_eq_genTerm 𝒢 q ρ n i g hA hν h z A' β
  rw [h1, ghostRowGen_eq_truncatedRow _ _ _ _ h hh z]
  unfold ghostAbsKernel
  exact (Graph.finite_ghost_truncated_kernel_reproduces
    (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
    (Graph.sourceGhostA (visitQ q n i) ρ) |Graph.sourceGhostD (visitQ q n i) ρ|
    |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ|
    Bc h hh z).symm

/-- **The weighted row ratio of the absolute one-group kernel** (eq:ghost-schur-ratios), bounded
by the full exponential, uniformly in the cutoff. -/
theorem ghostAbsKernel_row_le (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B)
    {v cmax Mmax : ℝ} (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (hA : 0 ≤ Graph.sourceGhostA (visitQ q n i) ρ) (hv : 0 < v)
    (hbase : Graph.sourceGhostA (visitQ q n i) ρ +
      |Graph.sourceGhostD (visitQ q n i) ρ| / v ≤ 1)
    (hC : |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ| ≤
      cmax)
    (hM : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) q n p ≤ Mmax) (z : Mem 𝒢 Bc g) :
    ∑ y : Mem 𝒢 Bc g, ghostAbsKernel 𝒢 q ρ n i g Bc z y * v ^ y.1.val ≤
      Real.exp (cmax * v * Mmax) * v ^ z.1.val := by
  have h := Graph.finite_ghost_truncated_kernel_weighted_row_le_uniform_exp
    (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
    (Graph.sourceGhostA (visitQ q n i) ρ) (Graph.sourceGhostD (visitQ q n i) ρ)
    (2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ)
    v cmax Mmax (fun p => hν p.1 p.2) hA hv hbase hC hM Bc z
  have hvz : 0 < v ^ z.1.val := pow_pos hv _
  calc ∑ y : Mem 𝒢 Bc g, ghostAbsKernel 𝒢 q ρ n i g Bc z y * v ^ y.1.val
      = (∑ y : Mem 𝒢 Bc g,
          ghostAbsKernel 𝒢 q ρ n i g Bc z y * v ^ y.1.val / v ^ z.1.val) * v ^ z.1.val := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun y _ => (div_mul_cancel₀ _ hvz.ne').symm
    _ ≤ Real.exp (cmax * v * Mmax) * v ^ z.1.val := mul_le_mul_of_nonneg_right h hvz.le

/-- **The weighted column ratio of the absolute one-group kernel** (eq:ghost-schur-ratios, "its
column ratio has `C_i, D_i` interchanged"), with the factorial measure of the memories. -/
theorem ghostAbsKernel_col_le (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B)
    {v dmax Mmax : ℝ} (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (hA : 0 ≤ Graph.sourceGhostA (visitQ q n i) ρ) (hv : 0 < v)
    (hbase : Graph.sourceGhostA (visitQ q n i) ρ +
      |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ| / v ≤
        1)
    (hD : |Graph.sourceGhostD (visitQ q n i) ρ| ≤ dmax)
    (hM : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) q n p ≤ Mmax) (y : Mem 𝒢 Bc g) :
    ∑ x : Mem 𝒢 Bc g,
        (Graph.finiteMemoryPointMass (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) q n z.1) x *
          v ^ x.1.val) * ghostAbsKernel 𝒢 q ρ n i g Bc x y ≤
      Real.exp (dmax * v * Mmax) *
        (Graph.finiteMemoryPointMass (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) q n z.1) y *
          v ^ y.1.val) := by
  have h := Graph.finite_ghost_truncated_kernel_weighted_column_le_uniform_exp
    (fun p : {p : ℕ // p ∈ 𝒢.big g} => tiltLaw (𝒢.big g) q n p)
    (Graph.sourceGhostA (visitQ q n i) ρ) (Graph.sourceGhostD (visitQ q n i) ρ)
    (2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ)
    v dmax Mmax (fun p => hν p.1 p.2) hA hv hbase hD hM Bc y
  have hvy : 0 < v ^ y.1.val := pow_pos hv _
  calc ∑ x : Mem 𝒢 Bc g,
        (Graph.finiteMemoryPointMass (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) q n z.1) x *
          v ^ x.1.val) * ghostAbsKernel 𝒢 q ρ n i g Bc x y
      = (∑ x : Mem 𝒢 Bc g,
          Graph.finiteMemoryPointMass (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) q n z.1) x *
            ghostAbsKernel 𝒢 q ρ n i g Bc x y * v ^ x.1.val / v ^ y.1.val) * v ^ y.1.val := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [div_mul_cancel₀ _ hvy.ne']
        ring
    _ ≤ (Graph.finiteMemoryPointMass (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) q n z.1) y *
          Real.exp (dmax * v * Mmax)) * v ^ y.1.val := mul_le_mul_of_nonneg_right h hvy.le
    _ = Real.exp (dmax * v * Mmax) *
        (Graph.finiteMemoryPointMass (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) q n z.1) y *
          v ^ y.1.val) := by ring

end OneGroup

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
