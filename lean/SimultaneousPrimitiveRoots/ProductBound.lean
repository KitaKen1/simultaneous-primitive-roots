module

public import Mathlib.Tactic

@[expose] public section

/-! An elementary product bound avoiding the asymptotic Wallis product. -/

namespace SimultaneousPrimitiveRoots

noncomputable def wallisProduct : ℕ → ℝ
  | 0 => 1
  | n + 1 => wallisProduct n * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2))

theorem wallisProduct_pos (n : ℕ) : 0 < wallisProduct n := by
  induction n with
  | zero => norm_num [wallisProduct]
  | succ n ih =>
    simp only [wallisProduct]
    positivity

theorem wallisProduct_squared_bound {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ 4 * (n : ℝ) * wallisProduct n ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [wallisProduct]
  | succ n hn ih =>
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hd : 0 < 2 * (n : ℝ) + 2 := by positivity
    have hmono : 4 * (n : ℝ) * wallisProduct n ^ 2 ≤
        4 * ((n : ℝ) + 1) *
          (wallisProduct n * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2))) ^ 2 := by
      field_simp
      nlinarith [sq_nonneg (wallisProduct n), mul_nonneg hn0 (sq_nonneg (wallisProduct n))]
    simpa [wallisProduct, Nat.cast_add, Nat.cast_one] using ih.trans hmono

theorem wallisProduct_square_index_bound {T : ℕ} (hT : 1 ≤ T) :
    1 / (2 * (T : ℝ)) ≤ wallisProduct (T ^ 2) := by
  have ht : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hp := wallisProduct_pos (T ^ 2)
  have hb := wallisProduct_squared_bound (n := T ^ 2) (by nlinarith)
  push_cast at hb
  apply (div_le_iff₀ (by positivity : 0 < 2 * (T : ℝ))).mpr
  have hsq : (1 : ℝ) ^ 2 ≤ (wallisProduct (T ^ 2) * (2 * (T : ℝ))) ^ 2 := by
    nlinarith only [hb]
  exact (sq_le_sq₀ (by norm_num) (by positivity)).mp hsq

end SimultaneousPrimitiveRoots
