module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.KernelCosts
public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealSanity
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.Pointwise

/-!
# The expansion of a cell kernel into cells and characters

The abstract part of the kernel expansion of [P] §6 (`[P-06:0381–0391]`): "Expand the two kernels
in (cor:comparison-kernel). Their contract supplies only a fixed log-power total cost. … The cell
and character expansion factors into separate bounded tests on the two free tuples and on each
endpoint's big marks."

* `listSum N aw E P P' κ = ∑_r aw(r) ∑_{w < N} E(r, w) ∑_{𝔭 ∈ P(r,w)} ∑_{𝔭' ∈ P'(r,w)} κ(r, 𝔭, 𝔭')`
  is linear in the coefficient `κ` (`listSum_add`, `listSum_smul`); `pairSum` is the case
  `κ(r, 𝔭, 𝔭') = s · κ₁(r, 𝔭') κ₂(r, 𝔭)`, linear in each of `κ₁`, `κ₂`.
* `cellCharD h j χ`, `cellCharX h j χ`: the tests `1_{log D ∈ I_j} conj χ(D)` and
  `1_{log X ∈ I_j} χ(X)`.
* `heavyCells`: the cells `j = logCell h (δ r)` of mass `ν_{Λ j} ≥ ξ`; there are at most `ξ⁻¹`
  of them (`card_heavyCells_mul_le`: their masses add up to at most the total mass `1`).
* `cellKernel_eq_sum_heavy`, `ite_primitiveCharSum_eq`: the exact expansion
  `𝒦_Λ(D, X) = ∑_{j heavy} ν_{Λ j}⁻¹ ∑_{χ ∈ 𝒞_Q} (1_{I_j}(D) conj χ(D)) (1_{I_j}(X) χ(X))`.
* `norm_map_cellKernel_le`: a linear functional that is at most `e` on all the products of two
  tests is at most `(∑_{j heavy} ν_{Λ j}⁻¹) · #𝒞_Q · e` on the kernel;
  `norm_pairSum_cellKernel_le` applies this to both kernels.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open scoped ComplexConjugate

noncomputable section

/-! ### Weighted sums over pairs of lists -/

section ListSum

variable {R M M' : Type} [Fintype R]

/-- `∑_r aw(r) ∑_{w < N} E(r, w) ∑_{𝔭 ∈ P(r,w)} ∑_{𝔭' ∈ P'(r,w)} κ(r, 𝔭, 𝔭')`. -/
def listSum (N : ℕ) (aw : R → ℂ) (E : R → ℕ → ℂ) (P : R → ℕ → Finset M)
    (P' : R → ℕ → Finset M') (κ : R → M → M' → ℂ) : ℂ :=
  ∑ r, aw r * ∑ w ∈ Finset.range N, E r w * ∑ 𝔭 ∈ P r w, ∑ 𝔭' ∈ P' r w, κ r 𝔭 𝔭'

theorem listSum_add (N : ℕ) (aw : R → ℂ) (E : R → ℕ → ℂ) (P : R → ℕ → Finset M)
    (P' : R → ℕ → Finset M') (κ₁ κ₂ : R → M → M' → ℂ) :
    listSum N aw E P P' (κ₁ + κ₂) = listSum N aw E P P' κ₁ + listSum N aw E P P' κ₂ := by
  simp only [listSum, Pi.add_apply, Finset.sum_add_distrib, mul_add]

theorem listSum_smul (N : ℕ) (aw : R → ℂ) (E : R → ℕ → ℂ) (P : R → ℕ → Finset M)
    (P' : R → ℕ → Finset M') (c : ℂ) (κ : R → M → M' → ℂ) :
    listSum N aw E P P' (c • κ) = c * listSum N aw E P P' κ := by
  simp only [listSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun w _ =>
    Finset.sum_congr rfl fun 𝔭 _ => Finset.sum_congr rfl fun 𝔭' _ => ?_
  ring

/-- The sum with a coefficient `s · κ₁(r, 𝔭') κ₂(r, 𝔭)` that separates the two lists. -/
def pairSum (N : ℕ) (aw : R → ℂ) (E : R → ℕ → ℂ) (P : R → ℕ → Finset M)
    (P' : R → ℕ → Finset M') (s : ℂ) (κ₁ : R → M' → ℂ) (κ₂ : R → M → ℂ) : ℂ :=
  listSum N aw E P P' fun r 𝔭 𝔭' => s * (κ₁ r 𝔭' * κ₂ r 𝔭)

theorem pairSum_isLinearMap_left (N : ℕ) (aw : R → ℂ) (E : R → ℕ → ℂ) (P : R → ℕ → Finset M)
    (P' : R → ℕ → Finset M') (s : ℂ) (κ₂ : R → M → ℂ) :
    IsLinearMap ℂ fun κ₁ : R → M' → ℂ => pairSum N aw E P P' s κ₁ κ₂ where
  map_add := fun f g => by
    have hfun : (fun (r : R) (𝔭 : M) (𝔭' : M') => s * ((f + g) r 𝔭' * κ₂ r 𝔭)) =
        (fun r 𝔭 𝔭' => s * (f r 𝔭' * κ₂ r 𝔭)) + fun r 𝔭 𝔭' => s * (g r 𝔭' * κ₂ r 𝔭) := by
      funext r 𝔭 𝔭'
      simp only [Pi.add_apply]
      ring
    show pairSum N aw E P P' s (f + g) κ₂ =
      pairSum N aw E P P' s f κ₂ + pairSum N aw E P P' s g κ₂
    unfold pairSum
    rw [hfun, listSum_add]
  map_smul := fun c f => by
    have hfun : (fun (r : R) (𝔭 : M) (𝔭' : M') => s * ((c • f) r 𝔭' * κ₂ r 𝔭)) =
        c • fun (r : R) (𝔭 : M) (𝔭' : M') => s * (f r 𝔭' * κ₂ r 𝔭) := by
      funext r 𝔭 𝔭'
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    show pairSum N aw E P P' s (c • f) κ₂ = c • pairSum N aw E P P' s f κ₂
    unfold pairSum
    rw [hfun, listSum_smul, smul_eq_mul]

theorem pairSum_isLinearMap_right (N : ℕ) (aw : R → ℂ) (E : R → ℕ → ℂ)
    (P : R → ℕ → Finset M) (P' : R → ℕ → Finset M') (s : ℂ) (κ₁ : R → M' → ℂ) :
    IsLinearMap ℂ fun κ₂ : R → M → ℂ => pairSum N aw E P P' s κ₁ κ₂ where
  map_add := fun f g => by
    have hfun : (fun (r : R) (𝔭 : M) (𝔭' : M') => s * (κ₁ r 𝔭' * (f + g) r 𝔭)) =
        (fun r 𝔭 𝔭' => s * (κ₁ r 𝔭' * f r 𝔭)) + fun r 𝔭 𝔭' => s * (κ₁ r 𝔭' * g r 𝔭) := by
      funext r 𝔭 𝔭'
      simp only [Pi.add_apply]
      ring
    show pairSum N aw E P P' s κ₁ (f + g) =
      pairSum N aw E P P' s κ₁ f + pairSum N aw E P P' s κ₁ g
    unfold pairSum
    rw [hfun, listSum_add]
  map_smul := fun c f => by
    have hfun : (fun (r : R) (𝔭 : M) (𝔭' : M') => s * (κ₁ r 𝔭' * (c • f) r 𝔭)) =
        c • fun (r : R) (𝔭 : M) (𝔭' : M') => s * (κ₁ r 𝔭' * f r 𝔭) := by
      funext r 𝔭 𝔭'
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    show pairSum N aw E P P' s κ₁ (c • f) = c • pairSum N aw E P P' s κ₁ f
    unfold pairSum
    rw [hfun, listSum_smul, smul_eq_mul]

end ListSum

/-! ### The cell tests -/

/-- `1_{log D ∈ I_j} conj χ(D)`. -/
def cellCharD (h : ℝ) (j : ℤ) {r₀ : ℕ} (χ : DirichletCharacter ℂ r₀) (D : ℕ) : ℂ :=
  (if logCell h D = j then 1 else 0) * conj (χ (D : ZMod r₀))

/-- `1_{log X ∈ I_j} χ(X)`. -/
def cellCharX (h : ℝ) (j : ℤ) {r₀ : ℕ} (χ : DirichletCharacter ℂ r₀) (X : ℕ) : ℂ :=
  (if logCell h X = j then 1 else 0) * χ (X : ZMod r₀)

theorem norm_cellCharD_le (h : ℝ) (j : ℤ) {r₀ : ℕ} (χ : DirichletCharacter ℂ r₀) (D : ℕ) :
    ‖cellCharD h j χ D‖ ≤ 1 := by
  unfold cellCharD
  by_cases hc : logCell h D = j
  · rw [if_pos hc, one_mul, Complex.norm_conj]
    exact χ.norm_le_one _
  · rw [if_neg hc, zero_mul, norm_zero]
    exact zero_le_one

theorem norm_cellCharX_le (h : ℝ) (j : ℤ) {r₀ : ℕ} (χ : DirichletCharacter ℂ r₀) (X : ℕ) :
    ‖cellCharX h j χ X‖ ≤ 1 := by
  unfold cellCharX
  by_cases hc : logCell h X = j
  · rw [if_pos hc, one_mul]
    exact χ.norm_le_one _
  · rw [if_neg hc, zero_mul, norm_zero]
    exact zero_le_one

theorem cellCharD_ne_zero {h : ℝ} {j : ℤ} {r₀ : ℕ} {χ : DirichletCharacter ℂ r₀} {D : ℕ}
    (hne : cellCharD h j χ D ≠ 0) : logCell h D = j := by
  by_contra hcon
  apply hne
  unfold cellCharD
  rw [if_neg hcon, zero_mul]

open _root_.Classical in
/-- The character sum on one cell is the sum over the primitive characters of the products of
the two cell tests. -/
theorem ite_primitiveCharSum_eq (Q h : ℝ) (j : ℤ) (D X : ℕ) :
    (if logCell h D = j ∧ logCell h X = j then primitiveCharSum Q D X else 0) =
      ∑ r₀ ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ r₀,
        (if χ.IsPrimitive then (1 : ℂ) else 0) * (cellCharD h j χ D * cellCharX h j χ X) := by
  unfold primitiveCharSum
  by_cases hc : logCell h D = j ∧ logCell h X = j
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun r₀ _ => Finset.sum_congr rfl fun χ _ => ?_
    by_cases hp : χ.IsPrimitive
    · rw [if_pos hp, if_pos hp, one_mul]
      unfold cellCharD cellCharX
      rw [if_pos hc.1, if_pos hc.2, one_mul, one_mul]
    · rw [if_neg hp, if_neg hp, zero_mul]
  · rw [if_neg hc]
    refine (Finset.sum_eq_zero fun r₀ _ => Finset.sum_eq_zero fun χ _ => ?_).symm
    unfold cellCharD cellCharX
    by_cases h1 : logCell h D = j
    · have h2 : ¬logCell h X = j := fun h2 => hc ⟨h1, h2⟩
      rw [if_neg h2, zero_mul, mul_zero, mul_zero]
    · rw [if_neg h1, zero_mul, zero_mul, mul_zero]

/-! ### The heavy cells -/

section Cells

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} {R : Type} [Fintype R]

/-- The cells `j = logCell h (δ r)` of mass `ν_{Λ j} ≥ ξ`. -/
def heavyCells (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (h ξ : ℝ) (δ : R → ℕ) :
    Finset ℤ :=
  (Finset.univ.image fun r : R => logCell h (δ r)).filter fun j => ξ ≤ cellMass big Λ h j

theorem mem_heavyCells {big : B → Finset ℕ} {Λ : B → Finset (Fin J)} {h ξ : ℝ} {δ : R → ℕ}
    {j : ℤ} :
    j ∈ heavyCells big Λ h ξ δ ↔ (∃ r, logCell h (δ r) = j) ∧ ξ ≤ cellMass big Λ h j := by
  unfold heavyCells
  rw [Finset.mem_filter, Finset.mem_image]
  simp only [Finset.mem_univ, true_and]

/-- Cells of mass at least `ξ` have total mass at most the total mass of the law. -/
theorem card_heavyCells_mul_le {big : B → Finset ℕ} {Λ : B → Finset (Fin J)} {h ξ : ℝ}
    (hw : ∀ t : AuxList big Λ, 0 ≤ auxWeight big Λ t)
    (hsum : ∑ t : AuxList big Λ, auxWeight big Λ t ≤ 1) (𝒥 : Finset ℤ)
    (h𝒥 : ∀ j ∈ 𝒥, ξ ≤ cellMass big Λ h j) : (𝒥.card : ℝ) * ξ ≤ 1 :=
  calc (𝒥.card : ℝ) * ξ = ∑ _j ∈ 𝒥, ξ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ 𝒥, cellMass big Λ h j := Finset.sum_le_sum h𝒥
    _ = ∑ t : AuxList big Λ, ∑ j ∈ 𝒥,
          (if logCell h (tupleProd Λ t) = j then auxWeight big Λ t else 0) := by
        unfold cellMass
        exact Finset.sum_comm
    _ ≤ ∑ t : AuxList big Λ, auxWeight big Λ t := Finset.sum_le_sum fun t _ => by
        rw [Finset.sum_ite_eq]
        by_cases hmem : logCell h (tupleProd Λ t) ∈ 𝒥
        · exact le_of_eq (if_pos hmem)
        · exact (le_of_eq (if_neg hmem)).trans (hw t)
    _ ≤ 1 := hsum

/-- `∑_{j heavy} ν_{Λ j}⁻¹ ≤ ξ⁻¹ · ξ⁻¹`. -/
theorem sum_inv_cellMass_heavy_le {big : B → Finset ℕ} {Λ : B → Finset (Fin J)} {h ξ : ℝ}
    (hξ : 0 < ξ) (hw : ∀ t : AuxList big Λ, 0 ≤ auxWeight big Λ t)
    (hsum : ∑ t : AuxList big Λ, auxWeight big Λ t ≤ 1) (δ : R → ℕ) :
    ∑ j ∈ heavyCells big Λ h ξ δ, (cellMass big Λ h j)⁻¹ ≤ ξ⁻¹ * ξ⁻¹ := by
  have h𝒥 : ∀ j ∈ heavyCells big Λ h ξ δ, ξ ≤ cellMass big Λ h j := fun j hj =>
    (mem_heavyCells.mp hj).2
  have hcard : ((heavyCells big Λ h ξ δ).card : ℝ) ≤ ξ⁻¹ := by
    have h1 := card_heavyCells_mul_le hw hsum _ h𝒥
    rw [← one_div, le_div_iff₀ hξ]
    exact h1
  calc ∑ j ∈ heavyCells big Λ h ξ δ, (cellMass big Λ h j)⁻¹
      ≤ ∑ _j ∈ heavyCells big Λ h ξ δ, ξ⁻¹ :=
        Finset.sum_le_sum fun j hj => inv_anti₀ hξ (h𝒥 j hj)
    _ = ((heavyCells big Λ h ξ δ).card : ℝ) * ξ⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ξ⁻¹ * ξ⁻¹ := mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hξ.le)

theorem sum_inv_cellMass_heavy_nonneg {big : B → Finset ℕ} {Λ : B → Finset (Fin J)} {h ξ : ℝ}
    (hξ : 0 < ξ) (δ : R → ℕ) :
    0 ≤ ∑ j ∈ heavyCells big Λ h ξ δ, (cellMass big Λ h j)⁻¹ :=
  Finset.sum_nonneg fun _ hj =>
    inv_nonneg.mpr ((lt_of_lt_of_le hξ (mem_heavyCells.mp hj).2).le)

/-- **The kernel on the heavy cells**: for `D = δ r`,
`𝒦_Λ(D, X) = ∑_{j heavy} ν_{Λ j}⁻¹ 1_{log D ∈ I_j} 1_{log X ∈ I_j} ∑_{χ ∈ 𝒞_Q} conj χ(D) χ(X)`. -/
theorem cellKernel_eq_sum_heavy (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ)
    (δ : R → ℕ) (r : R) (X : ℕ) :
    cellKernel big Λ Q h ξ (δ r) X =
      ∑ j ∈ heavyCells big Λ h ξ δ, ((cellMass big Λ h j : ℝ) : ℂ)⁻¹ *
        (if logCell h (δ r) = j ∧ logCell h X = j then primitiveCharSum Q (δ r) X else 0) := by
  unfold cellKernel
  by_cases hc : logCell h (δ r) = logCell h X ∧ ξ ≤ cellMass big Λ h (logCell h (δ r))
  · have hmem : logCell h (δ r) ∈ heavyCells big Λ h ξ δ :=
      mem_heavyCells.mpr ⟨⟨r, rfl⟩, hc.2⟩
    rw [if_pos hc, Finset.sum_eq_single_of_mem (logCell h (δ r)) hmem,
      if_pos ⟨rfl, hc.1.symm⟩]
    intro j _ hj
    rw [if_neg fun h' => hj h'.1.symm, mul_zero]
  · rw [if_neg hc]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    have hξj := (mem_heavyCells.mp hj).2
    have hne : ¬(logCell h (δ r) = j ∧ logCell h X = j) := by
      rintro ⟨h1, h2⟩
      refine hc ⟨h1.trans h2.symm, ?_⟩
      rw [h1]
      exact hξj
    rw [if_neg hne, mul_zero]

open _root_.Classical in
/-- A linear functional that is at most `e` on the products of the two cell tests of every
primitive character is at most `#𝒞_Q · e` on the sums over `𝒞_Q`. -/
theorem norm_map_charSum_le {V : Type} [AddCommGroup V] [Module ℂ V] (T : V →ₗ[ℂ] ℂ) (Q : ℝ)
    (f : (r₀ : ℕ) → DirichletCharacter ℂ r₀ → V) (e : ℝ)
    (he : ∀ (r₀ : ℕ) (χ : DirichletCharacter ℂ r₀), ‖T (f r₀ χ)‖ ≤ e) :
    ‖T (∑ r₀ ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ r₀,
        (if χ.IsPrimitive then (1 : ℂ) else 0) • f r₀ χ)‖ ≤ (primitiveCharCount Q : ℝ) * e := by
  rw [map_sum]
  unfold primitiveCharCount
  rw [Nat.cast_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r₀ _ => ?_)
  rw [map_sum, Finset.natCast_card_filter, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
  rw [map_smul, smul_eq_mul, norm_mul]
  by_cases hp : χ.IsPrimitive
  · rw [if_pos hp, if_pos hp, norm_one, one_mul, one_mul]
    exact he r₀ χ
  · refine le_of_eq ?_
    rw [if_neg hp, if_neg hp, norm_zero, zero_mul, zero_mul]

open _root_.Classical in
/-- **One kernel**: a linear functional on functions of `(r, y)` that is at most `e` on all the
products `(1_{I_j} conj χ)(δ r) · (1_{I_j} χ)(ρ y)` is at most
`(∑_{j heavy} ν_{Λ j}⁻¹) · #𝒞_Q · e` on `(r, y) ↦ 𝒦_Λ(δ r, ρ y)`. -/
theorem norm_map_cellKernel_le {Y : Type} (big : B → Finset ℕ) (Λ : B → Finset (Fin J))
    (Q h ξ : ℝ) (hξ : 0 < ξ) (δ : R → ℕ) (ρ : Y → ℕ) (T : (R → Y → ℂ) →ₗ[ℂ] ℂ) (e : ℝ)
    (he : ∀ (j : ℤ) (r₀ : ℕ) (χ : DirichletCharacter ℂ r₀),
      ‖T fun r y => cellCharD h j χ (δ r) * cellCharX h j χ (ρ y)‖ ≤ e) :
    ‖T fun r y => cellKernel big Λ Q h ξ (δ r) (ρ y)‖ ≤
      (∑ j ∈ heavyCells big Λ h ξ δ, (cellMass big Λ h j)⁻¹) *
        ((primitiveCharCount Q : ℝ) * e) := by
  have hfun : (fun (r : R) (y : Y) => cellKernel big Λ Q h ξ (δ r) (ρ y)) =
      ∑ j ∈ heavyCells big Λ h ξ δ, ((cellMass big Λ h j : ℝ) : ℂ)⁻¹ •
        ∑ r₀ ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ r₀,
          (if χ.IsPrimitive then (1 : ℂ) else 0) •
            fun (r : R) (y : Y) => cellCharD h j χ (δ r) * cellCharX h j χ (ρ y) := by
    funext r y
    rw [cellKernel_eq_sum_heavy big Λ Q h ξ δ r (ρ y)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ite_primitiveCharSum_eq]
  rw [hfun, map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hpos : 0 < cellMass big Λ h j := lt_of_lt_of_le hξ (mem_heavyCells.mp hj).2
  rw [map_smul, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_left
    (norm_map_charSum_le T Q
      (fun r₀ χ => fun (r : R) (y : Y) => cellCharD h j χ (δ r) * cellCharX h j χ (ρ y)) e
      fun r₀ χ => he j r₀ χ)
    (inv_nonneg.mpr hpos.le)

end Cells

/-! ### Both kernels -/

section Pair

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} {R M M' : Type} [Fintype R]

/-- **Both kernels**: if the pair sums of all the products of cell tests are at most `e`, then the
pair sum of the two kernels is at most
`(∑_{j heavy} ν_{Λ₁ j}⁻¹) · #𝒞_Q · (∑_{j heavy} ν_{Λ₂ j}⁻¹) · #𝒞_Q · e`. -/
theorem norm_pairSum_cellKernel_le (big : B → Finset ℕ) (Λ₁ Λ₂ : B → Finset (Fin J))
    (Q h ξ : ℝ) (hξ : 0 < ξ) (δ₁ δ₂ : R → ℕ) (ρ₁ : M' → ℕ) (ρ₂ : M → ℕ) (N : ℕ) (aw : R → ℂ)
    (E : R → ℕ → ℂ) (P : R → ℕ → Finset M) (P' : R → ℕ → Finset M') (s : ℂ) (e : ℝ)
    (he : ∀ (j₁ : ℤ) (r₁ : ℕ) (χ₁ : DirichletCharacter ℂ r₁) (j₂ : ℤ) (r₂ : ℕ)
      (χ₂ : DirichletCharacter ℂ r₂),
      ‖pairSum N aw E P P' s
          (fun r 𝔭' => cellCharD h j₁ χ₁ (δ₁ r) * cellCharX h j₁ χ₁ (ρ₁ 𝔭'))
          (fun r 𝔭 => cellCharD h j₂ χ₂ (δ₂ r) * cellCharX h j₂ χ₂ (ρ₂ 𝔭))‖ ≤ e) :
    ‖pairSum N aw E P P' s (fun r 𝔭' => cellKernel big Λ₁ Q h ξ (δ₁ r) (ρ₁ 𝔭'))
        (fun r 𝔭 => cellKernel big Λ₂ Q h ξ (δ₂ r) (ρ₂ 𝔭))‖ ≤
      (∑ j ∈ heavyCells big Λ₁ h ξ δ₁, (cellMass big Λ₁ h j)⁻¹) *
        ((primitiveCharCount Q : ℝ) *
          ((∑ j ∈ heavyCells big Λ₂ h ξ δ₂, (cellMass big Λ₂ h j)⁻¹) *
            ((primitiveCharCount Q : ℝ) * e))) := by
  refine norm_map_cellKernel_le big Λ₁ Q h ξ hξ δ₁ ρ₁
    (IsLinearMap.mk' _ (pairSum_isLinearMap_left N aw E P P' s
      fun r 𝔭 => cellKernel big Λ₂ Q h ξ (δ₂ r) (ρ₂ 𝔭))) _ fun j₁ r₁ χ₁ => ?_
  exact norm_map_cellKernel_le big Λ₂ Q h ξ hξ δ₂ ρ₂
    (IsLinearMap.mk' _ (pairSum_isLinearMap_right N aw E P P' s
      fun r 𝔭' => cellCharD h j₁ χ₁ (δ₁ r) * cellCharX h j₁ χ₁ (ρ₁ 𝔭'))) e
    fun j₂ r₂ χ₂ => he j₁ r₁ χ₁ j₂ r₂ χ₂

end Pair

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
