module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ModelInterchange
public import SimultaneousPrimitiveRoots.Unconditional.Classical.DirichletMeanSquare

/-!
# The Gram (dual large sieve) bound and reciprocals of well-spaced points

Tools for (cor:sparse-bound) (`[P-06:0803–0832]`): "The Gram matrix of the vectors
`(n^{it_i})_{n ≍ R_0}` consequently has absolute row sum `≪ R_0 L`. Here separation bounds the
reciprocal-difference sum by `O(log T_0)` … The Gram operator bound multiplied by `∑ |c_n|²`
proves (cor:sparse-bound)."

* `sum_sum_mul_mul_le_of_row_sum_le_gen`: the Schur test, for an arbitrary index type (the
  version for `ℕ` is in `Classical/DirichletMeanSquare.lean`).
* `sum_normSq_le_of_gram_row_sum_le`: **the Gram operator bound**. If the Gram matrix
  `G(t, t') = ∑_n φ_n(t) \overline{φ_n(t')}` has absolute row sums `≤ B` on `𝒯`, then
  `∑_{t ∈ 𝒯} |∑_n c_n φ_n(t)|² ≤ B ∑_n |c_n|²`. (With `P(t) = ∑_n c_n φ_n(t)` and
  `D_n = ∑_t \overline{P(t)} φ_n(t)`: `S = ∑_t |P(t)|² = ∑_n c_n D_n`, Cauchy–Schwarz, and
  `∑_n |D_n|² = ∑_{t,t'} \overline{P(t)} P(t') G(t,t') ≤ B S`.)
* `sum_inv_le_sum_Icc_inv_of_separated`, `sum_erase_inv_abs_sub_le`: for a finite set of reals
  with pairwise distances `≥ 1` and a member `t`, `∑_{t' ≠ t} 1/|t - t'| ≤ 2 (1 + log N)` when all
  differences are `≤ N` (the map `t' ↦ ⌊|t - t'|⌋` is injective on each side of `t`).
* `natCast_cpow_mul_conj`, `gram_natIcc_eq`: the Gram entries of the vectors
  `(n^{it})_{R_0 ≤ n ≤ R_1}` are the phase sums `∑_n n^{i(t - t')}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### The Schur test and the Gram operator bound -/

/-- The Schur test for an arbitrary index type: if the kernel `K` is nonnegative and symmetric
on `s` with row sums at most `B`, then `∑_{m,n} x_m x_n K(m,n) ≤ B ∑_m x_m²`. -/
theorem sum_sum_mul_mul_le_of_row_sum_le_gen {κ : Type*} (s : Finset κ) (x : κ → ℝ)
    (K : κ → κ → ℝ) (B : ℝ)
    (hK0 : ∀ m ∈ s, ∀ n ∈ s, 0 ≤ K m n) (hKsymm : ∀ m ∈ s, ∀ n ∈ s, K m n = K n m)
    (hrow : ∀ m ∈ s, ∑ n ∈ s, K m n ≤ B) :
    ∑ m ∈ s, ∑ n ∈ s, x m * x n * K m n ≤ B * ∑ m ∈ s, x m ^ 2 := by
  have h1 : ∀ m ∈ s, ∀ n ∈ s,
      x m * x n * K m n ≤ x m ^ 2 * K m n / 2 + x n ^ 2 * K m n / 2 := by
    intro m hm n hn
    nlinarith [mul_nonneg (sq_nonneg (x m - x n)) (hK0 m hm n hn)]
  have h2 : ∑ m ∈ s, ∑ n ∈ s, x m * x n * K m n ≤
      ∑ m ∈ s, ∑ n ∈ s, (x m ^ 2 * K m n / 2 + x n ^ 2 * K m n / 2) :=
    Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => h1 m hm n hn
  have h3 : ∑ m ∈ s, ∑ n ∈ s, (x m ^ 2 * K m n / 2 + x n ^ 2 * K m n / 2) =
      (∑ m ∈ s, ∑ n ∈ s, x m ^ 2 * K m n) / 2 + (∑ m ∈ s, ∑ n ∈ s, x n ^ 2 * K m n) / 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_div]
  have hsymm : ∑ m ∈ s, ∑ n ∈ s, x n ^ 2 * K m n = ∑ m ∈ s, ∑ n ∈ s, x m ^ 2 * K m n :=
    calc ∑ m ∈ s, ∑ n ∈ s, x n ^ 2 * K m n
        = ∑ n ∈ s, ∑ m ∈ s, x n ^ 2 * K m n := Finset.sum_comm
      _ = ∑ n ∈ s, ∑ m ∈ s, x n ^ 2 * K n m :=
          Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => by
            rw [hKsymm m hm n hn]
  have hS1 : ∑ m ∈ s, ∑ n ∈ s, x m ^ 2 * K m n ≤ B * ∑ m ∈ s, x m ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [← Finset.mul_sum, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _)
  rw [h3, hsymm] at h2
  linarith

/-- **The Gram operator bound** (the dual form of the large sieve): if the absolute row sums of
the Gram matrix `G(t, t') = ∑_{n ∈ s} φ_n(t) \overline{φ_n(t')}` over `𝒯` are at most `B`, then
`∑_{t ∈ 𝒯} |∑_{n ∈ s} c_n φ_n(t)|² ≤ B ∑_{n ∈ s} |c_n|²`. -/
theorem sum_normSq_le_of_gram_row_sum_le {ι κ : Type*} (s : Finset ι) (𝒯 : Finset κ)
    (φ : ι → κ → ℂ) (c : ι → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ t ∈ 𝒯, ∑ t' ∈ 𝒯, ‖∑ n ∈ s, φ n t * (starRingEnd ℂ) (φ n t')‖ ≤ B) :
    ∑ t ∈ 𝒯, ‖∑ n ∈ s, c n * φ n t‖ ^ 2 ≤ B * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  obtain ⟨P, hP⟩ : ∃ P : κ → ℂ, ∀ t, P t = ∑ n ∈ s, c n * φ n t :=
    ⟨fun t => ∑ n ∈ s, c n * φ n t, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ι → ℂ, ∀ n, D n = ∑ t ∈ 𝒯, (starRingEnd ℂ) (P t) * φ n t :=
    ⟨fun n => ∑ t ∈ 𝒯, (starRingEnd ℂ) (P t) * φ n t, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : κ → κ → ℂ,
      ∀ t t', G t t' = ∑ n ∈ s, φ n t * (starRingEnd ℂ) (φ n t') :=
    ⟨fun t t' => ∑ n ∈ s, φ n t * (starRingEnd ℂ) (φ n t'), fun _ _ => rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ t ∈ 𝒯, ‖P t‖ ^ 2 := ⟨_, rfl⟩
  have hgoal : ∑ t ∈ 𝒯, ‖∑ n ∈ s, c n * φ n t‖ ^ 2 = S := by
    rw [hSdef]
    exact Finset.sum_congr rfl fun t _ => by rw [hP t]
  have hrow' : ∀ t ∈ 𝒯, ∑ t' ∈ 𝒯, ‖G t t'‖ ≤ B := fun t ht =>
    le_of_eq_of_le (Finset.sum_congr rfl fun t' _ => by rw [hG t t']) (hrow t ht)
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun t _ => sq_nonneg _
  have hc0 : 0 ≤ ∑ n ∈ s, ‖c n‖ ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  -- `S = ∑_n c_n D_n`
  have hSD : ((S : ℝ) : ℂ) = ∑ n ∈ s, c n * D n := by
    rw [hSdef, Complex.ofReal_sum]
    calc ∑ t ∈ 𝒯, ((‖P t‖ ^ 2 : ℝ) : ℂ)
        = ∑ t ∈ 𝒯, ∑ n ∈ s, c n * ((starRingEnd ℂ) (P t) * φ n t) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          calc ((‖P t‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) (P t) * P t := by
                rw [Complex.ofReal_pow, Complex.conj_mul']
            _ = (starRingEnd ℂ) (P t) * ∑ n ∈ s, c n * φ n t := by rw [← hP t]
            _ = ∑ n ∈ s, (starRingEnd ℂ) (P t) * (c n * φ n t) := Finset.mul_sum _ _ _
            _ = ∑ n ∈ s, c n * ((starRingEnd ℂ) (P t) * φ n t) :=
                Finset.sum_congr rfl fun n _ => by ring
      _ = ∑ n ∈ s, ∑ t ∈ 𝒯, c n * ((starRingEnd ℂ) (P t) * φ n t) := Finset.sum_comm
      _ = ∑ n ∈ s, c n * D n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hD n, Finset.mul_sum]
  -- `∑_n |D_n|² = ∑_{t,t'} \overline{P(t)} P(t') G(t,t')`
  have hDD : ((∑ n ∈ s, ‖D n‖ ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ 𝒯, ∑ t' ∈ 𝒯, (starRingEnd ℂ) (P t) * P t' * G t t' := by
    rw [Complex.ofReal_sum]
    calc ∑ n ∈ s, ((‖D n‖ ^ 2 : ℝ) : ℂ)
        = ∑ n ∈ s, ∑ t ∈ 𝒯, ∑ t' ∈ 𝒯,
            (starRingEnd ℂ) (P t) * P t' * (φ n t * (starRingEnd ℂ) (φ n t')) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          calc ((‖D n‖ ^ 2 : ℝ) : ℂ) = D n * (starRingEnd ℂ) (D n) := by
                rw [Complex.ofReal_pow, Complex.mul_conj']
            _ = (∑ t ∈ 𝒯, (starRingEnd ℂ) (P t) * φ n t) *
                  ∑ t' ∈ 𝒯, (starRingEnd ℂ) ((starRingEnd ℂ) (P t') * φ n t') := by
                rw [hD n, map_sum]
            _ = ∑ t ∈ 𝒯, ∑ t' ∈ 𝒯, (starRingEnd ℂ) (P t) * φ n t *
                  (starRingEnd ℂ) ((starRingEnd ℂ) (P t') * φ n t') := Finset.sum_mul_sum _ _ _ _
            _ = ∑ t ∈ 𝒯, ∑ t' ∈ 𝒯,
                  (starRingEnd ℂ) (P t) * P t' * (φ n t * (starRingEnd ℂ) (φ n t')) := by
                refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
                rw [map_mul, Complex.conj_conj]
                ring
      _ = ∑ t ∈ 𝒯, ∑ n ∈ s, ∑ t' ∈ 𝒯,
            (starRingEnd ℂ) (P t) * P t' * (φ n t * (starRingEnd ℂ) (φ n t')) := Finset.sum_comm
      _ = ∑ t ∈ 𝒯, ∑ t' ∈ 𝒯, ∑ n ∈ s,
            (starRingEnd ℂ) (P t) * P t' * (φ n t * (starRingEnd ℂ) (φ n t')) :=
          Finset.sum_congr rfl fun t _ => Finset.sum_comm
      _ = ∑ t ∈ 𝒯, ∑ t' ∈ 𝒯, (starRingEnd ℂ) (P t) * P t' * G t t' := by
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
          rw [hG t t', Finset.mul_sum]
  -- the Gram matrix is Hermitian
  have hGsymm : ∀ t t', ‖G t t'‖ = ‖G t' t‖ := by
    intro t t'
    have h : G t' t = (starRingEnd ℂ) (G t t') := by
      rw [hG t' t, hG t t', map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_mul, Complex.conj_conj]
      ring
    rw [h, Complex.norm_conj]
  -- `∑_n |D_n|² ≤ B S`
  have hD2 : ∑ n ∈ s, ‖D n‖ ^ 2 ≤ B * S := by
    have h0 : 0 ≤ ∑ n ∈ s, ‖D n‖ ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
    have h1 : ∑ n ∈ s, ‖D n‖ ^ 2 ≤ ∑ t ∈ 𝒯, ∑ t' ∈ 𝒯, ‖P t‖ * ‖P t'‖ * ‖G t t'‖ := by
      rw [← Real.norm_of_nonneg h0, ← Complex.norm_real, hDD]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t' _ => ?_)
      exact le_of_eq (by rw [norm_mul, norm_mul, Complex.norm_conj])
    rw [hSdef]
    exact h1.trans (sum_sum_mul_mul_le_of_row_sum_le_gen 𝒯 (fun t => ‖P t‖)
      (fun t t' => ‖G t t'‖) B (fun t _ t' _ => norm_nonneg _) (fun t _ t' _ => hGsymm t t')
      hrow')
  -- Cauchy–Schwarz
  have h1 : S ≤ ∑ n ∈ s, ‖c n‖ * ‖D n‖ :=
    calc S = ‖((S : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hS0]
      _ = ‖∑ n ∈ s, c n * D n‖ := by rw [hSD]
      _ ≤ ∑ n ∈ s, ‖c n * D n‖ := norm_sum_le _ _
      _ = ∑ n ∈ s, ‖c n‖ * ‖D n‖ := Finset.sum_congr rfl fun n _ => norm_mul _ _
  have h3 : S * S ≤ B * (∑ n ∈ s, ‖c n‖ ^ 2) * S :=
    calc S * S = S ^ 2 := (pow_two S).symm
      _ ≤ (∑ n ∈ s, ‖c n‖ * ‖D n‖) ^ 2 := pow_le_pow_left₀ hS0 h1 2
      _ ≤ (∑ n ∈ s, ‖c n‖ ^ 2) * ∑ n ∈ s, ‖D n‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq s (fun n => ‖c n‖) (fun n => ‖D n‖)
      _ ≤ (∑ n ∈ s, ‖c n‖ ^ 2) * (B * S) := mul_le_mul_of_nonneg_left hD2 hc0
      _ = B * (∑ n ∈ s, ‖c n‖ ^ 2) * S := by ring
  rw [hgoal]
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hB hc0
  · exact le_of_mul_le_mul_right h3 hpos

/-! ### Reciprocals of well-spaced points -/

/-- Reciprocals of real numbers in `[1, N]` with pairwise distances at least `1`:
`∑_a 1/d_a ≤ ∑_{j ≤ N} 1/j`. -/
theorem sum_inv_le_sum_Icc_inv_of_separated {κ : Type*} (S : Finset κ) (d : κ → ℝ) (N : ℕ)
    (h1 : ∀ a ∈ S, 1 ≤ d a) (hN : ∀ a ∈ S, d a ≤ (N : ℝ))
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 ≤ |d a - d b|) :
    ∑ a ∈ S, (d a)⁻¹ ≤ ∑ j ∈ Finset.Icc 1 N, (j : ℝ)⁻¹ := by
  have hfl : ∀ a ∈ S, (⌊d a⌋₊ : ℝ) ≤ d a := fun a ha =>
    Nat.floor_le (zero_le_one.trans (h1 a ha))
  have hfl1 : ∀ a ∈ S, 1 ≤ ⌊d a⌋₊ := fun a ha => (Nat.one_le_floor_iff _).mpr (h1 a ha)
  have hinj : Set.InjOn (fun a => ⌊d a⌋₊) (S : Set κ) := by
    intro a ha b hb hab
    by_contra hne
    have ha' : a ∈ S := Finset.mem_coe.mp ha
    have hb' : b ∈ S := Finset.mem_coe.mp hb
    have hab' : ⌊d a⌋₊ = ⌊d b⌋₊ := hab
    have hab'' : (⌊d a⌋₊ : ℝ) = (⌊d b⌋₊ : ℝ) := by rw [hab']
    have h2 := hsep a ha' b hb' hne
    have ha1 := Nat.lt_floor_add_one (d a)
    have hb1 := Nat.lt_floor_add_one (d b)
    have ha2 := hfl a ha'
    have hb2 := hfl b hb'
    have h3 : |d a - d b| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  calc ∑ a ∈ S, (d a)⁻¹ ≤ ∑ a ∈ S, ((⌊d a⌋₊ : ℕ) : ℝ)⁻¹ := by
        refine Finset.sum_le_sum fun a ha => ?_
        have hpos : (0 : ℝ) < (⌊d a⌋₊ : ℝ) := Nat.cast_pos.mpr (hfl1 a ha)
        exact inv_anti₀ hpos (hfl a ha)
    _ = ∑ j ∈ S.image (fun a => ⌊d a⌋₊), (j : ℝ)⁻¹ :=
        (Finset.sum_image (f := fun j : ℕ => (j : ℝ)⁻¹) hinj).symm
    _ ≤ ∑ j ∈ Finset.Icc 1 N, (j : ℝ)⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun j _ _ => inv_nonneg.mpr (Nat.cast_nonneg j))
        intro j hj
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_Icc.mpr ⟨hfl1 a ha, Nat.floor_le_of_le (hN a ha)⟩

/-- **The reciprocal-difference sum of well-spaced points** (`[P-06:0828–0829]`: "separation
bounds the reciprocal-difference sum by `O(log T_0)`"): for a finite set of reals with pairwise
distances `≥ 1`, a member `t`, and `N` bounding the differences,
`∑_{t' ≠ t} 1/|t - t'| ≤ 2 (1 + log N)`. -/
theorem sum_erase_inv_abs_sub_le (𝒯 : Finset ℝ) (t : ℝ) (N : ℕ)
    (hsep : ∀ a ∈ 𝒯, ∀ b ∈ 𝒯, a ≠ b → 1 ≤ |a - b|) (ht : t ∈ 𝒯)
    (hN : ∀ a ∈ 𝒯, |t - a| ≤ (N : ℝ)) :
    ∑ a ∈ 𝒯.erase t, |t - a|⁻¹ ≤ 2 * (1 + Real.log (N : ℝ)) := by
  have hH := SimultaneousPrimitiveRoots.Unconditional.Classical.sum_Icc_inv_le_one_add_log N
  -- the points above `t`
  have h1 : ∑ a ∈ (𝒯.erase t).filter (fun a => t < a), |t - a|⁻¹ ≤
      ∑ j ∈ Finset.Icc 1 N, (j : ℝ)⁻¹ := by
    have hmem : ∀ a ∈ (𝒯.erase t).filter (fun a => t < a), a ∈ 𝒯 ∧ t < a := fun a ha =>
      ⟨Finset.mem_of_mem_erase (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩
    have heq : ∑ a ∈ (𝒯.erase t).filter (fun a => t < a), |t - a|⁻¹ =
        ∑ a ∈ (𝒯.erase t).filter (fun a => t < a), (a - t)⁻¹ :=
      Finset.sum_congr rfl fun a ha => by
        rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (hmem a ha).2)]
    rw [heq]
    refine sum_inv_le_sum_Icc_inv_of_separated _ (fun a => a - t) N ?_ ?_ ?_
    · intro a ha
      have h := hsep a (hmem a ha).1 t ht (hmem a ha).2.ne'
      rw [abs_of_pos (sub_pos.mpr (hmem a ha).2)] at h
      exact h
    · intro a ha
      have h := hN a (hmem a ha).1
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (hmem a ha).2)] at h
      exact h
    · intro a ha b hb hab
      have h := hsep a (hmem a ha).1 b (hmem b hb).1 hab
      have e : a - t - (b - t) = a - b := by ring
      show 1 ≤ |a - t - (b - t)|
      rw [e]
      exact h
  -- the points below `t`
  have h2 : ∑ a ∈ (𝒯.erase t).filter (fun a => ¬ t < a), |t - a|⁻¹ ≤
      ∑ j ∈ Finset.Icc 1 N, (j : ℝ)⁻¹ := by
    have hmem : ∀ a ∈ (𝒯.erase t).filter (fun a => ¬ t < a), a ∈ 𝒯 ∧ a < t := fun a ha => by
      have h1 := Finset.mem_filter.mp ha
      have h2 := Finset.mem_erase.mp h1.1
      exact ⟨h2.2, lt_of_le_of_ne (not_lt.mp h1.2) h2.1⟩
    have heq : ∑ a ∈ (𝒯.erase t).filter (fun a => ¬ t < a), |t - a|⁻¹ =
        ∑ a ∈ (𝒯.erase t).filter (fun a => ¬ t < a), (t - a)⁻¹ :=
      Finset.sum_congr rfl fun a ha => by
        rw [abs_of_pos (sub_pos.mpr (hmem a ha).2)]
    rw [heq]
    refine sum_inv_le_sum_Icc_inv_of_separated _ (fun a => t - a) N ?_ ?_ ?_
    · intro a ha
      have h := hsep t ht a (hmem a ha).1 (hmem a ha).2.ne'
      rw [abs_of_pos (sub_pos.mpr (hmem a ha).2)] at h
      exact h
    · intro a ha
      have h := hN a (hmem a ha).1
      rw [abs_of_pos (sub_pos.mpr (hmem a ha).2)] at h
      exact h
    · intro a ha b hb hab
      have h := hsep a (hmem a ha).1 b (hmem b hb).1 hab
      have e : t - a - (t - b) = -(a - b) := by ring
      show 1 ≤ |t - a - (t - b)|
      rw [e, abs_neg]
      exact h
  rw [← Finset.sum_filter_add_sum_filter_not (𝒯.erase t) (fun a => t < a)]
  linarith

/-! ### The Gram entries of the vectors `(n^{it})` -/

/-- `n^{it} \overline{n^{it'}} = n^{i(t - t')}` for a positive integer `n`. -/
theorem natCast_cpow_mul_conj {n : ℕ} (hn : n ≠ 0) (t t' : ℝ) :
    (n : ℂ) ^ ((t : ℂ) * Complex.I) * (starRingEnd ℂ) ((n : ℂ) ^ ((t' : ℂ) * Complex.I)) =
      (n : ℂ) ^ (((t - t' : ℝ) : ℂ) * Complex.I) := by
  have hconj : (starRingEnd ℂ) (Complex.I * (t' : ℂ) * (Real.log (n : ℝ) : ℂ)) =
      -(Complex.I * (t' : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
    ring
  rw [natCast_cpow_mul_I hn t, natCast_cpow_mul_I hn t', natCast_cpow_mul_I hn (t - t'),
    ← Complex.exp_conj, hconj, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Gram entries of the vectors `(n^{it})_{R_0 ≤ n ≤ R_1}` are the phase sums
`∑_n n^{i(t - t')}`. -/
theorem gram_natIcc_eq {R₀ R₁ : ℝ} (hR₀ : 0 < R₀) (t t' : ℝ) :
    ∑ n ∈ natIcc R₀ R₁, (n : ℂ) ^ ((t : ℂ) * Complex.I) *
        (starRingEnd ℂ) ((n : ℂ) ^ ((t' : ℂ) * Complex.I)) =
      ∑ n ∈ natIcc R₀ R₁, (n : ℂ) ^ (((t - t' : ℝ) : ℂ) * Complex.I) := by
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by
    intro h0
    have h := ((mem_natIcc_of_pos hR₀).mp hn).1
    rw [h0, Nat.cast_zero] at h
    exact absurd h (not_le.mpr hR₀)
  exact natCast_cpow_mul_conj hn0 t t'

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
