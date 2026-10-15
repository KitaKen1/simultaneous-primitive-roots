module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostSurvivorExpansion
public import SimultaneousPrimitiveRoots.Unconditional.Graph.MemoryDegreeGrouping
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostTruncatedMaps
public import SimultaneousPrimitiveRoots.Unconditional.Graph.SymmetricFockOperator

/-!
# The unrestricted original survivor/termination/birth sector pairing

The source integral is a series of finite k!t!b! factorial sectors. Absolute
memory-pair/survivor summability permits degree grouping. Symmetric endpoints
identify each admissible block with the source sector; the explicit address
bijection then identifies the unrestricted source series with the completed
Hilbert pairing. This concerns the pure ghost operator, not full transference.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ComplexInnerProductSpace

variable {Z P : Type*} {R : P → Type*}

theorem infinite_memory_degree_equiv {n m : ℕ} (h : n = m) (x : Fin n → Z) :
    (⟨m, memoryDegreeEquiv h x⟩ : InfiniteMemory Z) = ⟨n, x⟩ := by
  cases h
  rfl

theorem factorial_memory_point_mass_complex (w : Z → ℝ) {n : ℕ} (x : Fin n → Z) :
    ((factorialMemoryPointMass w x : ℝ) : ℂ) =
      factorialMemoryPointMass (fun z => (w z : ℂ)) x := by
  simp [factorialMemoryPointMass]

noncomputable def infiniteGhostSourceSector [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ)
    (f g : InfiniteMemory (Σ p, R p) → ℂ) (k t b : ℕ) : ℂ :=
  finiteGhostJointSector (k := k) (a := t) (b := b) (fun p => (ν p : ℂ))
    (A : ℂ) (D : ℂ) (C : ℂ) (fun x y => star (g ⟨k + t, x⟩) * f ⟨k + b, y⟩)

noncomputable def infiniteGhostDegreePairing [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ)
    (f g : InfiniteMemory (Σ p, R p) → ℂ) (d : ℕ × ℕ × ℕ) : ℂ :=
  memoryDegreeSurvivorSum
    (fun z => infiniteGhostSurvivorJoint ν A D C f g z.1.1 z.1.2 z.2) d

theorem infinite_ghost_degree_pairing_source [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ)
    (f g : InfiniteMemory (Σ p, R p) → ℂ)
    (hf : ∀ (x : InfiniteMemory (Σ p, R p)) (σ : Equiv.Perm (Fin x.1)),
      f ⟨x.1, x.2 ∘ σ⟩ = f x)
    (hg : ∀ (x : InfiniteMemory (Σ p, R p)) (σ : Equiv.Perm (Fin x.1)),
      g ⟨x.1, x.2 ∘ σ⟩ = g x)
    (n m k : ℕ) (hk : k ≤ n ∧ k ≤ m) :
    infiniteGhostDegreePairing ν A D C f g (n, m, k) =
      infiniteGhostSourceSector ν A D C f g k (n - k) (m - k) := by
  classical
  have hc (x : Fin n → Σ p, R p) (y : Fin m → Σ p, R p) :=
    finite_ghost_degree_kernel_map Complex.ofRealHom ν A D C k n m x y
  simp only [Function.comp_def, Complex.ofRealHom_eq_coe] at hc
  have h := finite_ghost_degree_joint_sector (fun p => (ν p : ℂ))
    (A : ℂ) (D : ℂ) (C : ℂ) k n m hk
    (fun x => star (g ⟨n, x⟩)) (fun y => f ⟨m, y⟩)
    (fun σ x => by rw [hg ⟨n, x⟩ σ]) (fun σ y => hf ⟨m, y⟩ σ)
  calc
    _ = ∑ x : Fin n → Σ p, R p, ∑ y : Fin m → Σ p, R p,
        factorialMemoryPointMass (fun z : Σ p, R p => (ν z.1 : ℂ)) x * star (g ⟨n, x⟩) *
          finiteGhostDegreeKernel (fun p => (ν p : ℂ)) (A : ℂ) (D : ℂ) (C : ℂ)
            k n m x y * f ⟨m, y⟩ := by
      unfold infiniteGhostDegreePairing memoryDegreeSurvivorSum infiniteGhostSurvivorJoint
      simp only [infiniteMemoryPointMass, factorial_memory_point_mass_complex, hc]
    _ = _ := by
      rw [h]
      unfold infiniteGhostSourceSector
      congr 1
      funext x y
      rw [infinite_memory_degree_equiv, infinite_memory_degree_equiv]

theorem infinite_ghost_degree_pairing_outside [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ)
    (f g : InfiniteMemory (Σ p, R p) → ℂ) (d : ℕ × ℕ × ℕ)
    (hk : ¬ (d.2.2 ≤ d.1 ∧ d.2.2 ≤ d.2.1)) :
    infiniteGhostDegreePairing ν A D C f g d = 0 := by
  classical
  have ho : d.2.2 ∉ Finset.range (min d.1 d.2.1 + 1) := by
    intro h
    have he := Nat.lt_succ_iff.mp (Finset.mem_range.mp h)
    exact hk ⟨he.trans (min_le_left _ _), he.trans (min_le_right _ _)⟩
  unfold infiniteGhostDegreePairing memoryDegreeSurvivorSum
  have hz (x : Fin d.1 → Σ p, R p) (y : Fin d.2.1 → Σ p, R p) :=
    infinite_ghost_survivor_joint_outside ν A D C f g ⟨d.1, x⟩ ⟨d.2.1, y⟩ d.2.2 ho
  simp only [hz, Finset.sum_const_zero]

theorem infinite_ghost_degree_pairing_source_address [Fintype P] [∀ p, Fintype (R p)]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ)
    (f g : InfiniteMemory (Σ p, R p) → ℂ)
    (hf : ∀ (x : InfiniteMemory (Σ p, R p)) (σ : Equiv.Perm (Fin x.1)),
      f ⟨x.1, x.2 ∘ σ⟩ = f x)
    (hg : ∀ (x : InfiniteMemory (Σ p, R p)) (σ : Equiv.Perm (Fin x.1)),
      g ⟨x.1, x.2 ∘ σ⟩ = g x) (z : ℕ × ℕ × ℕ) :
    infiniteGhostDegreePairing ν A D C f g (ghostSectorDegreeEquiv z).val =
      infiniteGhostSourceSector ν A D C f g z.1 z.2.1 z.2.2 := by
  rcases z with ⟨k, t, b⟩
  change infiniteGhostDegreePairing ν A D C f g (k + t, k + b, k) =
    infiniteGhostSourceSector ν A D C f g k t b
  rw [infinite_ghost_degree_pairing_source ν A D C f g hf hg _ _ _
    ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩]
  simp only [Nat.add_sub_cancel_left]

theorem symmetric_fock_unweighted_coordinates (w : Z → ℝ) (f : symmetricMemoryFock Z)
    (x : InfiniteMemory Z) (σ : Equiv.Perm (Fin x.1)) :
    unweightedMemoryCoordinates w f.val ⟨x.1, x.2 ∘ σ⟩ =
      unweightedMemoryCoordinates w f.val x := by
  unfold unweightedMemoryCoordinates
  rw [infinite_memory_point_mass_invariant, f.property x σ]

section Bounded

variable [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)

include v cmax dmax Mmax hν hA hv hbaseD hbaseC hC hD hM

theorem infinite_ghost_source_sector_norm_summable
    (f g : symmetricMemoryFock (Σ p, R p)) :
    Summable (fun z : ℕ × ℕ × ℕ =>
      ‖infiniteGhostSourceSector ν A D C
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f.val)
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g.val)
        z.1 z.2.1 z.2.2‖) := by
  have hb := memory_degree_survivor_sum_norm_summable _
    (infinite_ghost_expanded_joint_norm_summable ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f.val g.val)
  have hs := (ghostSectorDegreeEquiv.summable_iff).mpr
    (hb.subtype (fun z : ℕ × ℕ × ℕ => z.2.2 ≤ z.1 ∧ z.2.2 ≤ z.2.1))
  change Summable (fun z : ℕ × ℕ × ℕ =>
    ‖infiniteGhostDegreePairing ν A D C
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f.val)
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g.val)
      (ghostSectorDegreeEquiv z).val‖) at hs
  simpa only [infinite_ghost_degree_pairing_source_address ν A D C _ _
    (symmetric_fock_unweighted_coordinates _ f) (symmetric_fock_unweighted_coordinates _ g)]
    using hs

theorem infinite_ghost_source_sector_pairing
    (f g : symmetricMemoryFock (Σ p, R p)) :
    (∑' z : ℕ × ℕ × ℕ, infiniteGhostSourceSector ν A D C
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f.val)
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g.val)
      z.1 z.2.1 z.2.2) =
    inner ℂ g.val (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f.val) := by
  let f0 := unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f.val
  let g0 := unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g.val
  let B := infiniteGhostDegreePairing ν A D C f0 g0
  have he (z : ℕ × ℕ × ℕ) : B (ghostSectorDegreeEquiv z).val =
      infiniteGhostSourceSector ν A D C f0 g0 z.1 z.2.1 z.2.2 :=
    infinite_ghost_degree_pairing_source_address ν A D C f0 g0
      (symmetric_fock_unweighted_coordinates _ f) (symmetric_fock_unweighted_coordinates _ g) z
  calc
    _ = ∑' z : ℕ × ℕ × ℕ, B (ghostSectorDegreeEquiv z).val := by
      exact tsum_congr (fun z => (he z).symm)
    _ = ∑' z : GhostSurvivorDegrees, B z.val :=
      ghostSectorDegreeEquiv.tsum_eq (fun z : GhostSurvivorDegrees => B z.val)
    _ = ∑' d, B d := tsum_subtype_eq_of_support_subset (by
      intro d hd
      by_contra hn
      exact hd (infinite_ghost_degree_pairing_outside ν A D C f0 g0 d hn))
    _ = ∑' z : (InfiniteMemory (Σ p, R p) × InfiniteMemory (Σ p, R p)) × ℕ,
        infiniteGhostSurvivorJoint ν A D C f0 g0 z.1.1 z.1.2 z.2 :=
      memory_degree_survivor_sum_tsum _
        (infinite_ghost_expanded_joint_norm_summable ν A D C v cmax dmax Mmax
          hν hA hv hbaseD hbaseC hC hD hM f.val g.val)
    _ = _ := infinite_ghost_expanded_flat_joint_pairing ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f.val g.val

theorem infinite_ghost_source_sector_hasSum
    (f g : symmetricMemoryFock (Σ p, R p)) :
    HasSum (fun z : ℕ × ℕ × ℕ => infiniteGhostSourceSector ν A D C
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f.val)
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g.val)
      z.1 z.2.1 z.2.2)
      (inner ℂ g.val (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
        hν hA hv hbaseD hbaseC hC hD hM f.val)) := by
  rw [← infinite_ghost_source_sector_pairing ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f g]
  exact (infinite_ghost_source_sector_norm_summable ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f g).of_norm.hasSum

theorem infinite_ghost_source_iterated_sector_pairing
    (f g : symmetricMemoryFock (Σ p, R p)) :
    (∑' k, ∑' t, ∑' b, infiniteGhostSourceSector ν A D C
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f.val)
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g.val) k t b) =
    inner ℂ g.val (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f.val) := by
  have hs := (infinite_ghost_source_sector_norm_summable ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f g).of_norm
  calc
    _ = ∑' k, ∑' tb : ℕ × ℕ, infiniteGhostSourceSector ν A D C
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f.val)
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g.val) k tb.1 tb.2 := by
      apply tsum_congr
      intro k
      exact (hs.prod_factor k).tsum_prod.symm
    _ = ∑' z : ℕ × ℕ × ℕ, infiniteGhostSourceSector ν A D C
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f.val)
        (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g.val)
        z.1 z.2.1 z.2.2 := hs.tsum_prod.symm
    _ = _ := infinite_ghost_source_sector_pairing ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f g

theorem infinite_ghost_source_sector_reversed_pairing
    (f g : symmetricMemoryFock (Σ p, R p)) :
    (∑' z : ℕ × ℕ × ℕ, infiniteGhostSourceSector ν A D C
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f.val)
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g.val)
      z.1 z.2.1 z.2.2) =
    star (∑' z : ℕ × ℕ × ℕ, infiniteGhostSourceSector ν A C D
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g.val)
      (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f.val)
      z.1 z.2.1 z.2.2) := by
  rw [infinite_ghost_source_sector_pairing ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f g,
    infinite_ghost_source_sector_pairing ν A C D v dmax cmax Mmax
      hν hA hv hbaseC hbaseD hD hC hM g f,
    infinite_ghost_continuous_reversed_pairing ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f.val g.val]
  exact (inner_conj_symm _ _).symm

end Bounded

end SimultaneousPrimitiveRoots.Unconditional.Graph
