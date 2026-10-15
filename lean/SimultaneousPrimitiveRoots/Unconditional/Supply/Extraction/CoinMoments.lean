module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinModel

/-!
# The coin step: the moments of `T_g` on an equidistributed sample

`[P-07:0441–0449, 0488–0495]`: "summing the uniform residue estimates proves convergence of every
fixed joint factorial moment of the two hit counts, for any one or two groups, uniformly". Here,
from `BoxEq j P Ω u M ε` (the patterns of at most six primes of `P` have their model density on
`Ω`):

* `BoxEq.abs_tee_sub_le`: `∑_Ω T_g = M · teeMean ± ε M · teeNorm` (first moment);
* `BoxEq.abs_tee_mul_sub_le`: for disjoint groups `g, g'`,
  `∑_Ω T_g T_{g'} = M · teeMean(g) teeMean(g') ± ε M · teeNorm(g) teeNorm(g')`
  (the covariance of two groups is `O(ε)`, (ext:success-covariance));
* `BoxEq.sum_tee_sq_le`: `∑_Ω T_g² ≤ (1 + ε) M (N₀ + 2)² (2 · 9⁶ + 92160 exp(A_g + B_g))`
  (the diagonal: `T_g² ≤ (N₀ + 2)² (n⁶ + n'⁶)`, `n⁶ ≤ 9⁶ + 46080 C(n, 6)`, and the binomial
  coefficients are sums of patterns of six primes of `g`, `sixSum`);
* `BoxEq.card_le`: `#Ω ≤ (1 + ε) M`.

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

noncomputable section

variable {ι : Type*} {j : ℕ} {P : Finset ℕ} {Ω : Finset ι} {u : ι → ℕ} {M ε : ℝ}

/-! ### Sums of patterns -/

/-- A pattern occurs at most `(1 + ε) M · dens` times. -/
theorem BoxEq.sum_hit_le (hbox : BoxEq j P Ω u M ε) {A A' : Finset ℕ} (hA : A ⊆ P)
    (hA' : A' ⊆ P) (hcard : A.card + A'.card ≤ 6) :
    ∑ m ∈ Ω, hit A A' (u m) ≤ (1 + ε) * (M * dens j A A') := by
  have h := (abs_le.mp (hbox A A' hA hA' hcard)).2
  linarith

/-- `#Ω ≤ (1 + ε) M`. -/
theorem BoxEq.card_le (hbox : BoxEq j P Ω u M ε) : (Ω.card : ℝ) ≤ (1 + ε) * M := by
  have h := hbox.sum_hit_le (Finset.empty_subset P) (Finset.empty_subset P) (by simp)
  rw [dens_empty, mul_one] at h
  have e : ∑ m ∈ Ω, hit ∅ ∅ (u m) = (Ω.card : ℝ) := by
    rw [Finset.sum_congr rfl fun m _ => hit_empty (u m), Finset.sum_const, nsmul_eq_mul,
      mul_one]
  rw [e] at h
  exact h

/-- **A family of patterns**: its count on `Ω` is `M` times the sum of the densities, with
relative error `ε`. -/
theorem BoxEq.abs_sum_sub_le {κ : Type*} (hbox : BoxEq j P Ω u M ε) (s : Finset κ)
    (A A' : κ → Finset ℕ) (hA : ∀ i ∈ s, A i ⊆ P) (hA' : ∀ i ∈ s, A' i ⊆ P)
    (hcard : ∀ i ∈ s, (A i).card + (A' i).card ≤ 6) :
    |∑ m ∈ Ω, ∑ i ∈ s, hit (A i) (A' i) (u m) - M * ∑ i ∈ s, dens j (A i) (A' i)| ≤
      ε * (M * ∑ i ∈ s, dens j (A i) (A' i)) := by
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  exact hbox (A i) (A' i) (hA i hi) (hA' i hi) (hcard i hi)

/-- The monomials of one group. -/
theorem BoxEq.abs_mono_sub_le (hbox : BoxEq j P Ω u M ε) {g : Finset ℕ} (hg : g ⊆ P)
    (a : Fin 3) : |∑ m ∈ Ω, mono a g (u m) - M * mdl j a g| ≤ ε * (M * mdl j a g) := by
  unfold mono mdl
  exact hbox.abs_sum_sub_le (idx a g) (patU a) (patV a)
    (fun t ht => (patU_subset ht).trans hg) (fun t ht => (patV_subset ht).trans hg)
    (fun t _ => (pat_card_le a t).trans (by norm_num))

/-- The products of the monomials of two disjoint groups: the main terms factor exactly. -/
theorem BoxEq.abs_mono_mul_sub_le (hbox : BoxEq j P Ω u M ε) {g g' : Finset ℕ} (hg : g ⊆ P)
    (hg' : g' ⊆ P) (hdisj : Disjoint g g') (a b : Fin 3) :
    |∑ m ∈ Ω, mono a g (u m) * mono b g' (u m) - M * (mdl j a g * mdl j b g')| ≤
      ε * (M * (mdl j a g * mdl j b g')) := by
  have hpt : ∀ m ∈ Ω, mono a g (u m) * mono b g' (u m) =
      ∑ i ∈ idx a g ×ˢ idx b g',
        hit (patU a i.1 ∪ patU b i.2) (patV a i.1 ∪ patV b i.2) (u m) := by
    intro m _
    unfold mono
    rw [Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ =>
      hit_mul_hit _ _ _ _ _
  have hmd : mdl j a g * mdl j b g' =
      ∑ i ∈ idx a g ×ˢ idx b g', dens j (patU a i.1 ∪ patU b i.2) (patV a i.1 ∪ patV b i.2) := by
    unfold mdl
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun t' ht' => ?_
    refine (dens_union ?_).symm
    exact Finset.disjoint_of_subset_left
      (Finset.union_subset (patU_subset ht) (patV_subset ht))
      (Finset.disjoint_of_subset_right
        (Finset.union_subset (patU_subset ht') (patV_subset ht')) hdisj)
  rw [Finset.sum_congr rfl hpt, hmd]
  refine hbox.abs_sum_sub_le (idx a g ×ˢ idx b g') (fun i => patU a i.1 ∪ patU b i.2)
    (fun i => patV a i.1 ∪ patV b i.2) ?_ ?_ ?_
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hi
    exact Finset.union_subset ((patU_subset h1).trans hg) ((patU_subset h2).trans hg')
  · intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hi
    exact Finset.union_subset ((patV_subset h1).trans hg) ((patV_subset h2).trans hg')
  · intro i _
    have h1 := Finset.card_union_le (patU a i.1) (patU b i.2)
    have h2 := Finset.card_union_le (patV a i.1) (patV b i.2)
    have h3 := pat_card_le a i.1
    have h4 := pat_card_le b i.2
    omega

/-! ### The first moment and the mixed second moments of `T_g` -/

/-- **The first moment of `T_g`** on `Ω`. -/
theorem BoxEq.abs_tee_sub_le (hbox : BoxEq j P Ω u M ε) {g : Finset ℕ} (hg : g ⊆ P) (N₀ : ℝ) :
    |∑ m ∈ Ω, tee N₀ g (u m) - M * teeMean j N₀ g| ≤ ε * (M * teeNorm j N₀ g) := by
  have e1 : ∑ m ∈ Ω, tee N₀ g (u m) = ∑ a, gam N₀ a * ∑ m ∈ Ω, mono a g (u m) := by
    unfold tee
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
  have e2 : M * teeMean j N₀ g = ∑ a, gam N₀ a * (M * mdl j a g) := by
    unfold teeMean
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e3 : ε * (M * teeNorm j N₀ g) = ∑ a, |gam N₀ a| * (ε * (M * mdl j a g)) := by
    unfold teeNorm
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e1, e2, e3, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (hbox.abs_mono_sub_le hg a) (abs_nonneg _)

/-- **The mixed second moment of two disjoint groups** on `Ω`: the main term is the product of
the two model means (`[P-07:0488–0495]`). -/
theorem BoxEq.abs_tee_mul_sub_le (hbox : BoxEq j P Ω u M ε) {g g' : Finset ℕ} (hg : g ⊆ P)
    (hg' : g' ⊆ P) (hdisj : Disjoint g g') (N₀ : ℝ) :
    |∑ m ∈ Ω, tee N₀ g (u m) * tee N₀ g' (u m) - M * (teeMean j N₀ g * teeMean j N₀ g')| ≤
      ε * (M * (teeNorm j N₀ g * teeNorm j N₀ g')) := by
  have e1 : ∑ m ∈ Ω, tee N₀ g (u m) * tee N₀ g' (u m) =
      ∑ a, ∑ b, gam N₀ a * gam N₀ b * ∑ m ∈ Ω, mono a g (u m) * mono b g' (u m) := by
    unfold tee
    calc ∑ m ∈ Ω, (∑ a, gam N₀ a * mono a g (u m)) * (∑ b, gam N₀ b * mono b g' (u m))
        = ∑ m ∈ Ω, ∑ a, ∑ b, gam N₀ a * gam N₀ b * (mono a g (u m) * mono b g' (u m)) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ a, ∑ m ∈ Ω, ∑ b, gam N₀ a * gam N₀ b * (mono a g (u m) * mono b g' (u m)) :=
          Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ m ∈ Ω, gam N₀ a * gam N₀ b * (mono a g (u m) * mono b g' (u m)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a, ∑ b, gam N₀ a * gam N₀ b * ∑ m ∈ Ω, mono a g (u m) * mono b g' (u m) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            (Finset.mul_sum _ _ _).symm
  have e2 : M * (teeMean j N₀ g * teeMean j N₀ g') =
      ∑ a, ∑ b, gam N₀ a * gam N₀ b * (M * (mdl j a g * mdl j b g')) := by
    unfold teeMean
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e3 : ε * (M * (teeNorm j N₀ g * teeNorm j N₀ g')) =
      ∑ a, ∑ b, |gam N₀ a * gam N₀ b| * (ε * (M * (mdl j a g * mdl j b g'))) := by
    unfold teeNorm
    rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      rw [abs_mul]
      ring
  rw [e1, e2, e3, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (hbox.abs_mono_mul_sub_le hg hg' hdisj a b) (abs_nonneg _)

/-! ### The diagonal: the second moment of one `T_g` -/

/-- `∑_{D ⊆ g, |D| = 6} ∑_{A ⊆ D} 1_{A ∣ u, D ∖ A ∣ u + 1}`: the number of six-element sets of
primes of `g` all dividing `u (u + 1)`, as a sum of patterns. -/
def sixSum (g : Finset ℕ) (u : ℕ) : ℝ :=
  ∑ D ∈ Finset.powersetCard 6 g, ∑ A ∈ D.powerset, hit A (D \ A) u

theorem choose_le_sixSum_left (g : Finset ℕ) (u : ℕ) :
    ((primeHits g u).choose 6 : ℝ) ≤ sixSum g u := by
  have h1 : ∀ D ∈ Finset.powersetCard 6 (g.filter fun p => p ∣ u),
      (1 : ℝ) ≤ ∑ A ∈ D.powerset, hit A (D \ A) u := by
    intro D hD
    have hsub : D ⊆ g.filter fun p => p ∣ u := (Finset.mem_powersetCard.mp hD).1
    have hone : hit D (D \ D) u = 1 :=
      hit_of ⟨fun p hp => (Finset.mem_filter.mp (hsub hp)).2, fun p hp => by
        rw [Finset.sdiff_self] at hp
        exact absurd hp (Finset.notMem_empty p)⟩
    rw [← hone]
    exact Finset.single_le_sum (f := fun A => hit A (D \ A) u)
      (fun A _ => hit_nonneg _ _ _) (Finset.mem_powerset.mpr (Finset.Subset.refl D))
  calc ((primeHits g u).choose 6 : ℝ)
      = ((Finset.powersetCard 6 (g.filter fun p => p ∣ u)).card : ℝ) := by
        rw [Finset.card_powersetCard]
        rfl
    _ = ∑ _D ∈ Finset.powersetCard 6 (g.filter fun p => p ∣ u), (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ D ∈ Finset.powersetCard 6 (g.filter fun p => p ∣ u),
          ∑ A ∈ D.powerset, hit A (D \ A) u := Finset.sum_le_sum h1
    _ ≤ sixSum g u :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.powersetCard_mono (Finset.filter_subset _ _))
          (fun D _ _ => Finset.sum_nonneg fun A _ => hit_nonneg _ _ _)

theorem choose_le_sixSum_right (g : Finset ℕ) (u : ℕ) :
    ((primeHits g (u + 1)).choose 6 : ℝ) ≤ sixSum g u := by
  have h1 : ∀ D ∈ Finset.powersetCard 6 (g.filter fun p => p ∣ u + 1),
      (1 : ℝ) ≤ ∑ A ∈ D.powerset, hit A (D \ A) u := by
    intro D hD
    have hsub : D ⊆ g.filter fun p => p ∣ u + 1 := (Finset.mem_powersetCard.mp hD).1
    have hone : hit ∅ (D \ ∅) u = 1 :=
      hit_of ⟨fun p hp => absurd hp (Finset.notMem_empty p), fun p hp => by
        rw [Finset.sdiff_empty] at hp
        exact (Finset.mem_filter.mp (hsub hp)).2⟩
    rw [← hone]
    exact Finset.single_le_sum (f := fun A => hit A (D \ A) u)
      (fun A _ => hit_nonneg _ _ _) (Finset.empty_mem_powerset D)
  calc ((primeHits g (u + 1)).choose 6 : ℝ)
      = ((Finset.powersetCard 6 (g.filter fun p => p ∣ u + 1)).card : ℝ) := by
        rw [Finset.card_powersetCard]
        rfl
    _ = ∑ _D ∈ Finset.powersetCard 6 (g.filter fun p => p ∣ u + 1), (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ D ∈ Finset.powersetCard 6 (g.filter fun p => p ∣ u + 1),
          ∑ A ∈ D.powerset, hit A (D \ A) u := Finset.sum_le_sum h1
    _ ≤ sixSum g u :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.powersetCard_mono (Finset.filter_subset _ _))
          (fun D _ _ => Finset.sum_nonneg fun A _ => hit_nonneg _ _ _)

/-- The six-prime patterns of a group have total count `≤ (1 + ε) M exp(A_g + B_g)`. -/
theorem BoxEq.sum_sixSum_le (hbox : BoxEq j P Ω u M ε) (hj : 1 ≤ j) (hP : ∀ p ∈ P, 1 ≤ p)
    (hM : 0 ≤ M) (hε : 0 ≤ ε) {g : Finset ℕ} (hg : g ⊆ P) :
    ∑ m ∈ Ω, sixSum g (u m) ≤ (1 + ε) * M * Real.exp (sumU j g + sumV j g) := by
  have hg1 : ∀ p ∈ g, 1 ≤ p := fun p hp => hP p (hg hp)
  have hw0 : ∀ p ∈ g, 0 ≤ alphaU j p + alphaV j p := fun p hp =>
    add_nonneg (alphaU_nonneg hj (hg1 p hp)) (alphaV_nonneg (hg1 p hp))
  have hD : ∀ D ∈ Finset.powersetCard 6 g, ∑ A ∈ D.powerset, ∑ m ∈ Ω, hit A (D \ A) (u m) ≤
      (1 + ε) * M * ∏ p ∈ D, (alphaU j p + alphaV j p) := by
    intro D hD
    obtain ⟨hDg, hDcard⟩ := Finset.mem_powersetCard.mp hD
    have hterm : ∀ A ∈ D.powerset, ∑ m ∈ Ω, hit A (D \ A) (u m) ≤
        (1 + ε) * M * ((∏ p ∈ A, alphaU j p) * ∏ p ∈ D \ A, alphaV j p) := by
      intro A hA
      have hAD : A ⊆ D := Finset.mem_powerset.mp hA
      have hc : A.card + (D \ A).card ≤ 6 := by
        have := Finset.card_sdiff_add_card_eq_card hAD
        omega
      have h := hbox.sum_hit_le (hAD.trans (hDg.trans hg))
        (Finset.sdiff_subset.trans (hDg.trans hg)) hc
      rw [dens_of Finset.disjoint_sdiff] at h
      exact h.trans (le_of_eq (by ring))
    calc ∑ A ∈ D.powerset, ∑ m ∈ Ω, hit A (D \ A) (u m)
        ≤ ∑ A ∈ D.powerset,
            (1 + ε) * M * ((∏ p ∈ A, alphaU j p) * ∏ p ∈ D \ A, alphaV j p) :=
          Finset.sum_le_sum hterm
      _ = (1 + ε) * M * ∏ p ∈ D, (alphaU j p + alphaV j p) := by
          rw [← Finset.mul_sum, Finset.prod_add]
  have hall : ∑ D ∈ Finset.powersetCard 6 g, ∏ p ∈ D, (alphaU j p + alphaV j p) ≤
      Real.exp (sumU j g + sumV j g) := by
    calc ∑ D ∈ Finset.powersetCard 6 g, ∏ p ∈ D, (alphaU j p + alphaV j p)
        ≤ ∑ D ∈ g.powerset, ∏ p ∈ D, (alphaU j p + alphaV j p) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun D hD => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hD).1)
            (fun D hD _ => Finset.prod_nonneg fun p hp =>
              hw0 p (Finset.mem_powerset.mp hD hp))
      _ = ∏ p ∈ g, (1 + (alphaU j p + alphaV j p)) := (Finset.prod_one_add g).symm
      _ ≤ ∏ p ∈ g, Real.exp (alphaU j p + alphaV j p) :=
          Finset.prod_le_prod
            (fun p hp => by
              have := hw0 p hp
              linarith)
            (fun p _ => by
              have := Real.add_one_le_exp (alphaU j p + alphaV j p)
              linarith)
      _ = Real.exp (sumU j g + sumV j g) := by
          rw [← Real.exp_sum]
          unfold sumU sumV
          rw [Finset.sum_add_distrib]
  have hK : 0 ≤ (1 + ε) * M := mul_nonneg (by linarith) hM
  calc ∑ m ∈ Ω, sixSum g (u m)
      = ∑ D ∈ Finset.powersetCard 6 g, ∑ A ∈ D.powerset, ∑ m ∈ Ω, hit A (D \ A) (u m) := by
        unfold sixSum
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun D _ => Finset.sum_comm
    _ ≤ ∑ D ∈ Finset.powersetCard 6 g, (1 + ε) * M * ∏ p ∈ D, (alphaU j p + alphaV j p) :=
        Finset.sum_le_sum hD
    _ = (1 + ε) * M * ∑ D ∈ Finset.powersetCard 6 g, ∏ p ∈ D, (alphaU j p + alphaV j p) := by
        rw [Finset.mul_sum]
    _ ≤ (1 + ε) * M * Real.exp (sumU j g + sumV j g) := mul_le_mul_of_nonneg_left hall hK

/-- `n⁶ ≤ 9⁶ + 46080 C(n, 6)`. -/
theorem pow_six_le (n : ℕ) : (n : ℝ) ^ 6 ≤ 9 ^ 6 + 46080 * (n.choose 6 : ℝ) := by
  have hc0 : (0 : ℝ) ≤ (n.choose 6 : ℝ) := Nat.cast_nonneg _
  by_cases h : n < 10
  · have h9 : (n : ℝ) ≤ 9 := by
      have : n ≤ 9 := by omega
      exact_mod_cast this
    have := pow_le_pow_left₀ (Nat.cast_nonneg n) h9 6
    linarith
  · have h10 : (10 : ℝ) ≤ (n : ℝ) := by
      have : 10 ≤ n := by omega
      exact_mod_cast this
    have hc := Nat.pow_le_choose (α := ℝ) 6 n
    have h5 : ((n + 1 - 6 : ℕ) : ℝ) = (n : ℝ) - 5 := by
      rw [Nat.cast_sub (by omega : 6 ≤ n + 1)]
      push_cast
      ring
    have h720 : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
    rw [h5, h720, div_le_iff₀ (by norm_num)] at hc
    have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - 5 := by linarith
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2) hhalf 6
    have e : ((n : ℝ) / 2) ^ 6 = (n : ℝ) ^ 6 / 64 := by ring
    rw [e] at hp
    linarith

theorem poly_sq_le_aux {N₀ a b : ℝ} (hN₀ : 0 ≤ N₀) (ha : 1 ≤ a) (hab : a ≤ b) :
    (a * b * (N₀ + 2 - a - b)) ^ 2 ≤ (N₀ + 2) ^ 2 * b ^ 6 := by
  have hb : 1 ≤ b := ha.trans hab
  have hNb : 0 ≤ N₀ * b := mul_nonneg hN₀ (by linarith)
  have hNb1 : 0 ≤ (N₀ + 2) * (b - 1) := mul_nonneg (by linarith) (by linarith)
  have h1 : (N₀ + 2 - a - b) ^ 2 ≤ ((N₀ + 2) * b) ^ 2 := by
    refine sq_le_sq' ?_ ?_
    · linarith
    · linarith
  have h2 : (a * b) ^ 2 ≤ (b * b) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith))
      (mul_le_mul_of_nonneg_right hab (by linarith)) 2
  calc (a * b * (N₀ + 2 - a - b)) ^ 2 = (a * b) ^ 2 * (N₀ + 2 - a - b) ^ 2 := by ring
    _ ≤ (b * b) ^ 2 * ((N₀ + 2) * b) ^ 2 := mul_le_mul h2 h1 (sq_nonneg _) (sq_nonneg _)
    _ = (N₀ + 2) ^ 2 * b ^ 6 := by ring

/-- `(a b (N₀ + 2 - a - b))² ≤ (N₀ + 2)² (a⁶ + b⁶)` for `a, b ∈ {0} ∪ [1, ∞)`. -/
theorem poly_sq_le {N₀ a b : ℝ} (hN₀ : 0 ≤ N₀) (ha : a = 0 ∨ 1 ≤ a) (hb : b = 0 ∨ 1 ≤ b) :
    (a * b * (N₀ + 2 - a - b)) ^ 2 ≤ (N₀ + 2) ^ 2 * (a ^ 6 + b ^ 6) := by
  have ha6 : 0 ≤ a ^ 6 := by positivity
  have hb6 : 0 ≤ b ^ 6 := by positivity
  have hsq : 0 ≤ (N₀ + 2) ^ 2 := sq_nonneg _
  have hR : 0 ≤ (N₀ + 2) ^ 2 * (a ^ 6 + b ^ 6) := mul_nonneg hsq (add_nonneg ha6 hb6)
  rcases ha with ha | ha
  · have e : a * b * (N₀ + 2 - a - b) = 0 := by
      rw [ha]
      ring
    rw [e, zero_pow two_ne_zero]
    exact hR
  · rcases hb with hb | hb
    · have e : a * b * (N₀ + 2 - a - b) = 0 := by
        rw [hb]
        ring
      rw [e, zero_pow two_ne_zero]
      exact hR
    · rcases le_total a b with hab | hab
      · exact (poly_sq_le_aux hN₀ ha hab).trans
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ha6) hsq)
      · have e : a * b * (N₀ + 2 - a - b) = b * a * (N₀ + 2 - b - a) := by ring
        rw [e]
        exact (poly_sq_le_aux hN₀ hb hab).trans
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb6) hsq)

theorem natCast_eq_zero_or_one_le (n : ℕ) : (n : ℝ) = 0 ∨ 1 ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl (by rw [h, Nat.cast_zero])
  · exact Or.inr (by exact_mod_cast h)

/-- `T_g² ≤ (N₀ + 2)² (2 · 9⁶ + 46080 (C(n, 6) + C(n', 6)))`. -/
theorem tee_sq_le {N₀ : ℝ} (hN₀ : 0 ≤ N₀) (g : Finset ℕ) (u : ℕ) :
    tee N₀ g u ^ 2 ≤ (N₀ + 2) ^ 2 * (2 * 9 ^ 6 + 46080 *
      (((primeHits g u).choose 6 : ℝ) + ((primeHits g (u + 1)).choose 6 : ℝ))) := by
  rw [tee_eq]
  have h := poly_sq_le hN₀ (natCast_eq_zero_or_one_le (primeHits g u))
    (natCast_eq_zero_or_one_le (primeHits g (u + 1)))
  have h1 := pow_six_le (primeHits g u)
  have h2 := pow_six_le (primeHits g (u + 1))
  have hsq : 0 ≤ (N₀ + 2) ^ 2 := sq_nonneg _
  refine h.trans ((mul_le_mul_of_nonneg_left (add_le_add h1 h2) hsq).trans (le_of_eq ?_))
  ring

/-- **The second moment of one `T_g`** on `Ω`. -/
theorem BoxEq.sum_tee_sq_le (hbox : BoxEq j P Ω u M ε) (hj : 1 ≤ j) (hP : ∀ p ∈ P, 1 ≤ p)
    (hM : 0 ≤ M) (hε : 0 ≤ ε) {g : Finset ℕ} (hg : g ⊆ P) {N₀ : ℝ} (hN₀ : 0 ≤ N₀) :
    ∑ m ∈ Ω, tee N₀ g (u m) ^ 2 ≤
      (1 + ε) * M * ((N₀ + 2) ^ 2 * (2 * 9 ^ 6 + 92160 * Real.exp (sumU j g + sumV j g))) := by
  have hsq : 0 ≤ (N₀ + 2) ^ 2 := sq_nonneg _
  have hpt : ∀ m ∈ Ω, tee N₀ g (u m) ^ 2 ≤
      (N₀ + 2) ^ 2 * (2 * 9 ^ 6 + 92160 * sixSum g (u m)) := by
    intro m _
    have h1 := choose_le_sixSum_left g (u m)
    have h2 := choose_le_sixSum_right g (u m)
    refine (tee_sq_le hN₀ g (u m)).trans (mul_le_mul_of_nonneg_left ?_ hsq)
    linarith
  have hsix := hbox.sum_sixSum_le hj hP hM hε hg
  have hcard := hbox.card_le
  calc ∑ m ∈ Ω, tee N₀ g (u m) ^ 2
      ≤ ∑ m ∈ Ω, (N₀ + 2) ^ 2 * (2 * 9 ^ 6 + 92160 * sixSum g (u m)) := Finset.sum_le_sum hpt
    _ = (N₀ + 2) ^ 2 * (2 * 9 ^ 6 * (Ω.card : ℝ) + 92160 * ∑ m ∈ Ω, sixSum g (u m)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
        ring
    _ ≤ (N₀ + 2) ^ 2 * (2 * 9 ^ 6 * ((1 + ε) * M) +
          92160 * ((1 + ε) * M * Real.exp (sumU j g + sumV j g))) := by
        refine mul_le_mul_of_nonneg_left ?_ hsq
        have h3 := mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 2 * 9 ^ 6)
        linarith
    _ = (1 + ε) * M *
          ((N₀ + 2) ^ 2 * (2 * 9 ^ 6 + 92160 * Real.exp (sumU j g + sumV j g))) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin
