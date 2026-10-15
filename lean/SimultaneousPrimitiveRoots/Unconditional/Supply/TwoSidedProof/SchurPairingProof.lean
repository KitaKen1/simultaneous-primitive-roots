module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Auxiliary
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.PairingExpansion

/-!
# Schur's test for the pairing `⟨f, 𝒜 g⟩`

`schurPairing : SchurPairing` (`[P-06:0177–0180, 0306–0308]`: "the absolute Schur estimate and the
endpoint norms cost at most a fixed power of `L`"): if the operator with absolute coefficients and
its adjoint have row sums at most `R` at every state, then for `f = ∑_{n ∈ I} f_n u_n` and
`g ∈ ℋ_ph`,

`|⟨f, 𝒜 g⟩| ≤ R ‖f‖ ‖g‖`.

The proof is Schur's test for the row operations, before symmetrization.

* `⟨f, 𝒜 g⟩ = ∑_{n ∈ I} conj(f_n) ∑_x m(n, x) ∑_ν ∑_{r, x'} c_ν(n, x, r, x') (Sym g)(n + kD, x')`
  (`pairMarkFree_physOp_eq`): the outer symmetrization disappears against the mark-free `f`.
* Cauchy–Schwarz with the weights `m(n, x) |c_ν(n, x, r, x')|` (`nested_cs`) gives
  `|⟨f, 𝒜 g⟩|² ≤ A · B`, where `A` carries `|f_n|²` and `B` carries `|(Sym g)(n + kD, x')|²`.
* `A`: for fixed `n`, `∑_x m(n, x) · (row sum at (n, x)) ≤ R ‖u_n‖²` (`sum_absW_le`).
* `B`: the weight of a transition is the same seen from its target
  (`physWeight_mul_norm_physCoef_eq`), so `B` is at most the sum over the target states of
  `m(n', x') |(Sym g)(n', x')|² · (column sum at (n', x'))` (`sum_target_le`).
* The row and column sums of the hypothesis are the averages over the slot permutations of the
  unsymmetrized ones (`physAbsRowSum_eq_avg`, `physAbsColSum_eq_avg`). This is enough because the
  other factors (the mass, `|Sym g|²`) are invariant under slot permutations
  (`sum_mul_le_of_avg_le`), and `‖Sym g‖ ≤ ‖g‖` at every position (`fibSq_physSym_le`).

Everything except the last statement is for an arbitrary position model.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open scoped BigOperators ComplexConjugate

noncomputable section

namespace SchurTest

/-! ### Finite sums -/

/-- Cauchy–Schwarz with nonnegative weights. -/
theorem sum_weighted_mul_sq_le {ι : Type*} (T : Finset ι) (W α β : ι → ℝ)
    (hW : ∀ i ∈ T, 0 ≤ W i) :
    (∑ i ∈ T, W i * (α i * β i)) ^ 2 ≤ (∑ i ∈ T, W i * α i ^ 2) * ∑ i ∈ T, W i * β i ^ 2 := by
  have h : (∑ i ∈ T, Real.sqrt (W i) * α i * (Real.sqrt (W i) * β i)) ^ 2 ≤
      (∑ i ∈ T, (Real.sqrt (W i) * α i) ^ 2) * ∑ i ∈ T, (Real.sqrt (W i) * β i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq T _ _
  have e1 : ∀ i ∈ T, Real.sqrt (W i) * α i * (Real.sqrt (W i) * β i) = W i * (α i * β i) := by
    intro i hi
    calc Real.sqrt (W i) * α i * (Real.sqrt (W i) * β i)
        = Real.sqrt (W i) * Real.sqrt (W i) * (α i * β i) := by ring
      _ = W i * (α i * β i) := by rw [Real.mul_self_sqrt (hW i hi)]
  have e2 : ∀ i ∈ T, (Real.sqrt (W i) * α i) ^ 2 = W i * α i ^ 2 := by
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hW i hi)]
  have e3 : ∀ i ∈ T, (Real.sqrt (W i) * β i) ^ 2 = W i * β i ^ 2 := by
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hW i hi)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
  exact h

/-- A fourfold sum (positions, lists, patterns, transitions) as one sum. -/
theorem sum_nested_eq {P X N M : Type} [Fintype X] [Fintype N] [AddCommMonoid M] {A : N → Type}
    [∀ ν, Fintype (A ν)] (I : Finset P) (F : P → X → (ν : N) → A ν → M) :
    ∑ n ∈ I, ∑ x, ∑ ν, ∑ ξ, F n x ν ξ =
      ∑ p ∈ I ×ˢ (Finset.univ : Finset (X × (Σ ν, A ν))), F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  symm
  calc ∑ p ∈ I ×ˢ (Finset.univ : Finset (X × (Σ ν, A ν))), F p.1 p.2.1 p.2.2.1 p.2.2.2
      = ∑ n ∈ I, ∑ j : X × (Σ ν, A ν), F n j.1 j.2.1 j.2.2 :=
        Finset.sum_product' I Finset.univ (fun n (j : X × (Σ ν, A ν)) => F n j.1 j.2.1 j.2.2)
    _ = ∑ n ∈ I, ∑ x, ∑ σ : (Σ ν, A ν), F n x σ.1 σ.2 :=
        Finset.sum_congr rfl fun n _ =>
          Fintype.sum_prod_type' (fun x (σ : Σ ν, A ν) => F n x σ.1 σ.2)
    _ = ∑ n ∈ I, ∑ x, ∑ ν, ∑ ξ, F n x ν ξ :=
        Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun x _ =>
          Fintype.sum_sigma' (fun ν ξ => F n x ν ξ)

/-- Cauchy–Schwarz with nonnegative weights, for a fourfold sum. -/
theorem nested_cs {P X N : Type} [Fintype X] [Fintype N] {A : N → Type} [∀ ν, Fintype (A ν)]
    (I : Finset P) (W α β : P → X → (ν : N) → A ν → ℝ) (hW : ∀ n x ν ξ, 0 ≤ W n x ν ξ) :
    (∑ n ∈ I, ∑ x, ∑ ν, ∑ ξ, W n x ν ξ * (α n x ν ξ * β n x ν ξ)) ^ 2 ≤
      (∑ n ∈ I, ∑ x, ∑ ν, ∑ ξ, W n x ν ξ * α n x ν ξ ^ 2) *
        ∑ n ∈ I, ∑ x, ∑ ν, ∑ ξ, W n x ν ξ * β n x ν ξ ^ 2 := by
  rw [sum_nested_eq I (fun n x ν ξ => W n x ν ξ * (α n x ν ξ * β n x ν ξ)),
    sum_nested_eq I (fun n x ν ξ => W n x ν ξ * α n x ν ξ ^ 2),
    sum_nested_eq I (fun n x ν ξ => W n x ν ξ * β n x ν ξ ^ 2)]
  exact sum_weighted_mul_sq_le _
    (fun p : P × (X × (Σ ν, A ν)) => W p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p : P × (X × (Σ ν, A ν)) => α p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p : P × (X × (Σ ν, A ν)) => β p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p _ => hW _ _ _ _)

/-- The sum over the positions can be taken last. -/
theorem sum_comm_inner {P X N : Type} [Fintype X] [Fintype N] {A : N → Type}
    [∀ ν, Fintype (A ν)] (T : Finset P) (F : P → X → (ν : N) → A ν → ℝ) :
    ∑ n ∈ T, ∑ x, ∑ ν, ∑ ξ, F n x ν ξ = ∑ x, ∑ ν, ∑ ξ, ∑ n ∈ T, F n x ν ξ :=
  calc ∑ n ∈ T, ∑ x, ∑ ν, ∑ ξ, F n x ν ξ
      = ∑ x, ∑ n ∈ T, ∑ ν, ∑ ξ, F n x ν ξ := Finset.sum_comm
    _ = ∑ x, ∑ ν, ∑ n ∈ T, ∑ ξ, F n x ν ξ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x, ∑ ν, ∑ ξ, ∑ n ∈ T, F n x ν ξ :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Exchange of the source list and the target list in a sum over the transitions. -/
theorem sum_swap_lists {X N : Type} [Fintype X] [Fintype N] {A : N → Type} [∀ ν, Fintype (A ν)]
    (F : X → (ν : N) → A ν → X → ℝ) :
    ∑ x, ∑ ν, ∑ ξ : A ν × X, F x ν ξ.1 ξ.2 = ∑ x', ∑ ν, ∑ ξ : A ν × X, F ξ.2 ν ξ.1 x' := by
  have h1 : ∀ (x : X) (ν : N), ∑ ξ : A ν × X, F x ν ξ.1 ξ.2 = ∑ r, ∑ x', F x ν r x' :=
    fun x ν => Fintype.sum_prod_type' (fun r x' => F x ν r x')
  have h2 : ∀ (x' : X) (ν : N), ∑ ξ : A ν × X, F ξ.2 ν ξ.1 x' = ∑ r, ∑ x, F x ν r x' :=
    fun x' ν => Fintype.sum_prod_type' (fun r x => F x ν r x')
  calc ∑ x, ∑ ν, ∑ ξ : A ν × X, F x ν ξ.1 ξ.2
      = ∑ x, ∑ ν, ∑ r, ∑ x', F x ν r x' :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun ν _ => h1 x ν
    _ = ∑ ν, ∑ x, ∑ r, ∑ x', F x ν r x' := Finset.sum_comm
    _ = ∑ ν, ∑ r, ∑ x, ∑ x', F x ν r x' := Finset.sum_congr rfl fun ν _ => Finset.sum_comm
    _ = ∑ ν, ∑ r, ∑ x', ∑ x, F x ν r x' :=
        Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = ∑ ν, ∑ x', ∑ r, ∑ x, F x ν r x' := Finset.sum_congr rfl fun ν _ => Finset.sum_comm
    _ = ∑ x', ∑ ν, ∑ r, ∑ x, F x ν r x' := Finset.sum_comm
    _ = ∑ x', ∑ ν, ∑ ξ : A ν × X, F ξ.2 ν ξ.1 x' :=
        Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun ν _ => (h2 x' ν).symm

/-! ### Slot permutations -/

section Perm

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- A slot permutation as a bijection of the lists. -/
def permEquiv {𝒢 : GroupFamily S B} {J ℓ : ℕ} (π : SlotPerms S J ℓ × SlotPerms B J ℓ) :
    Lists 𝒢 J ℓ ≃ Lists 𝒢 J ℓ where
  toFun := permuteLists π
  invFun := permuteLists π⁻¹
  left_inv x := (permuteLists_eq_iff π x (permuteLists π x)).mp rfl
  right_inv y := (permuteLists_eq_iff π (permuteLists π⁻¹ y) y).mpr rfl

/-- **Averages over the slot permutations**: if `φ ≥ 0` is invariant under the slot permutations
and the average of `ψ` over the orbit of every list is at most `R`, then
`∑_x φ(x) ψ(x) ≤ R ∑_x φ(x)`. -/
theorem sum_mul_le_of_avg_le {𝒢 : GroupFamily S B} {J ℓ : ℕ} (φ ψ : Lists 𝒢 J ℓ → ℝ)
    (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ : ∀ (π : SlotPerms S J ℓ × SlotPerms B J ℓ) (x : Lists 𝒢 J ℓ),
      φ (permuteLists π x) = φ x) {R : ℝ}
    (hψ : ∀ x : Lists 𝒢 J ℓ, ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
      (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ * ψ (permuteLists π x) ≤ R) :
    ∑ x : Lists 𝒢 J ℓ, φ x * ψ x ≤ R * ∑ x : Lists 𝒢 J ℓ, φ x := by
  have hcard : (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hre : ∀ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
      ∑ x : Lists 𝒢 J ℓ, φ x * ψ (permuteLists π x) = ∑ x : Lists 𝒢 J ℓ, φ x * ψ x := by
    intro π
    refine Fintype.sum_equiv (permEquiv π) _ _ fun x => ?_
    show φ x * ψ (permuteLists π x) = φ (permuteLists π x) * ψ (permuteLists π x)
    rw [hφ π x]
  have h1 : ∑ x : Lists 𝒢 J ℓ, φ x * ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
        (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ * ψ (permuteLists π x) =
      ∑ x : Lists 𝒢 J ℓ, φ x * ψ x :=
    calc ∑ x : Lists 𝒢 J ℓ, φ x * ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
          (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ * ψ (permuteLists π x)
        = ∑ x : Lists 𝒢 J ℓ, ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
            (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
              (φ x * ψ (permuteLists π x)) :=
          Finset.sum_congr rfl fun x _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun π _ => by ring
      _ = ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ, ∑ x : Lists 𝒢 J ℓ,
            (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
              (φ x * ψ (permuteLists π x)) := Finset.sum_comm
      _ = ∑ _π : SlotPerms S J ℓ × SlotPerms B J ℓ,
            (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
              ∑ x : Lists 𝒢 J ℓ, φ x * ψ x :=
          Finset.sum_congr rfl fun π _ => by rw [← Finset.mul_sum, hre π]
      _ = ∑ x : Lists 𝒢 J ℓ, φ x * ψ x := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
            mul_inv_cancel₀ hcard, one_mul]
  calc ∑ x : Lists 𝒢 J ℓ, φ x * ψ x
      = ∑ x : Lists 𝒢 J ℓ, φ x * ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
          (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ * ψ (permuteLists π x) :=
        h1.symm
    _ ≤ ∑ x : Lists 𝒢 J ℓ, φ x * R :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hψ x) (hφ0 x)
    _ = R * ∑ x : Lists 𝒢 J ℓ, φ x := by rw [← Finset.sum_mul, mul_comm]

/-- The symmetrization of a real function is the average over the slot permutations. -/
theorem physSym_ofReal_re (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ)
    (G : PState 𝔭 𝒢 J ℓ → ℝ) (s : PState 𝔭 𝒢 J ℓ) :
    (physSym 𝔭 𝒢 J ℓ (fun t => ((G t : ℝ) : ℂ)) s).re =
      ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
        (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
          G (s.1, permuteLists π s.2) := by
  have h1 : physSym 𝔭 𝒢 J ℓ (fun t => ((G t : ℝ) : ℂ)) s =
      ((∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
        (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
          G (s.1, permuteLists π s.2) : ℝ) : ℂ) := by
    unfold physSym
    rw [rowOp_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [h1, Complex.ofReal_re]

/-- The row sum of the operator with absolute coefficients is the average over the slot
permutations of the unsymmetrized row sums. -/
theorem physAbsRowSum_eq_avg (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type}
    [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (s : PState 𝔭 𝒢 J ℓ) :
    physAbsRowSum 𝔭 𝒢 q 𝔉 k ζ s =
      ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
        (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
          Schur.rowAbsMass 𝔭 𝒢 q 𝔉 k ζ (s.1, permuteLists π s.2) := by
  unfold physAbsRowSum physAbsOp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Schur.physSym_const 𝔭 𝒢 J ℓ 1,
    Schur.sum_physRowAbs_one]
  exact physSym_ofReal_re 𝔭 𝒢 J ℓ (Schur.rowAbsMass 𝔭 𝒢 q 𝔉 k ζ) s

/-- The column sum of the operator with absolute coefficients is the average over the slot
permutations of the unsymmetrized column sums. -/
theorem physAbsColSum_eq_avg (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type}
    [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (s : PState 𝔭 𝒢 J ℓ) :
    physAbsColSum 𝔭 𝒢 q 𝔉 k ζ s =
      ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
        (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
          Schur.colAbsMass 𝔭 𝒢 q 𝔉 k ζ (s.1, permuteLists π s.2) := by
  unfold physAbsColSum physAbsAdj
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Schur.physSym_const 𝔭 𝒢 J ℓ 1,
    Schur.sum_physRowAdjAbs_one]
  exact physSym_ofReal_re 𝔭 𝒢 J ℓ (Schur.colAbsMass 𝔭 𝒢 q 𝔉 k ζ) s

/-- The unsymmetrized row sums are nonnegative. -/
theorem rowAbsMass_nonneg (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type}
    [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (t : PState 𝔭 𝒢 J ℓ) :
    0 ≤ Schur.rowAbsMass 𝔭 𝒢 q 𝔉 k ζ t := by
  unfold Schur.rowAbsMass
  exact Finset.sum_nonneg fun ν _ => Finset.sum_nonneg fun ξ _ => norm_nonneg _

/-- The row sums of the operator with absolute coefficients are nonnegative. -/
theorem physAbsRowSum_nonneg (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type}
    [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (s : PState 𝔭 𝒢 J ℓ) :
    0 ≤ physAbsRowSum 𝔭 𝒢 q 𝔉 k ζ s := by
  rw [physAbsRowSum_eq_avg]
  exact Finset.sum_nonneg fun π _ =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (rowAbsMass_nonneg 𝔭 𝒢 q 𝔉 k ζ _)

/-- A symmetrized function is invariant under the slot permutations. -/
theorem physSym_apply_permuteLists (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ)
    (G : PState 𝔭 𝒢 J ℓ → ℂ) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ)
    (π : SlotPerms S J ℓ × SlotPerms B J ℓ) :
    physSym 𝔭 𝒢 J ℓ G (n, permuteLists π x) = physSym 𝔭 𝒢 J ℓ G (n, x) := by
  unfold physSym
  rw [rowOp_apply, rowOp_apply]
  refine Fintype.sum_equiv (Equiv.mulLeft π) _ _ fun ρ => ?_
  rfl

/-- **`‖Sym g‖ ≤ ‖g‖` at every position** (Jensen for the average over the slot
permutations). -/
theorem fibSq_physSym_le (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ) (n : 𝔭.Pos)
    (g : PState 𝔭 𝒢 J ℓ → ℂ) :
    Pairing.fibSq 𝔭 𝒢 J ℓ n (physSym 𝔭 𝒢 J ℓ g) ≤ Pairing.fibSq 𝔭 𝒢 J ℓ n g := by
  have hcard0 : (0 : ℝ) < (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  -- Jensen at one state
  have hpt : ∀ x : Lists 𝒢 J ℓ, ‖physSym 𝔭 𝒢 J ℓ g (n, x)‖ ^ 2 ≤
      ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
        (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
          ‖g (n, permuteLists π x)‖ ^ 2 := by
    intro x
    have hval : physSym 𝔭 𝒢 J ℓ g (n, x) =
        ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
          (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹ *
            g (n, permuteLists π x) := by
      unfold physSym
      rw [rowOp_apply]
    have hcs : ‖∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
          (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹ *
            g (n, permuteLists π x)‖ ^ 2 ≤
        (∑ _π : SlotPerms S J ℓ × SlotPerms B J ℓ,
          ‖(Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹‖ ^ 2) *
          ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ, ‖g (n, permuteLists π x)‖ ^ 2 :=
      Pairing.norm_sum_mul_sq_le Finset.univ _ _
    have hc : ∑ _π : SlotPerms S J ℓ × SlotPerms B J ℓ,
        ‖(Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹‖ ^ 2 =
          (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, norm_inv, Complex.norm_natCast,
        pow_two, ← mul_assoc, mul_inv_cancel₀ hcard0.ne', one_mul]
    rw [hval]
    refine hcs.trans (le_of_eq ?_)
    rw [hc, Finset.mul_sum]
  -- the sum over the lists of one permuted term
  have hre : ∀ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
      ∑ x : Lists 𝒢 J ℓ, Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖g (n, permuteLists π x)‖ ^ 2 =
        Pairing.fibSq 𝔭 𝒢 J ℓ n g := by
    intro π
    unfold Pairing.fibSq
    refine Fintype.sum_equiv (permEquiv π) _ _ fun x => ?_
    show Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖g (n, permuteLists π x)‖ ^ 2 =
      Pairing.physWeight 𝔭 𝒢 J ℓ (n, permuteLists π x) * ‖g (n, permuteLists π x)‖ ^ 2
    rw [Pairing.physWeight_permuteLists]
  calc Pairing.fibSq 𝔭 𝒢 J ℓ n (physSym 𝔭 𝒢 J ℓ g)
      = ∑ x : Lists 𝒢 J ℓ, Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) *
          ‖physSym 𝔭 𝒢 J ℓ g (n, x)‖ ^ 2 := rfl
    _ ≤ ∑ x : Lists 𝒢 J ℓ, Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) *
          ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
            (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
              ‖g (n, permuteLists π x)‖ ^ 2 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (hpt x) (Pairing.physWeight_nonneg 𝔭 𝒢 J ℓ _)
    _ = ∑ x : Lists 𝒢 J ℓ, ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
          (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
            (Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖g (n, permuteLists π x)‖ ^ 2) :=
        Finset.sum_congr rfl fun x _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun π _ => by ring
    _ = ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ, ∑ x : Lists 𝒢 J ℓ,
          (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
            (Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖g (n, permuteLists π x)‖ ^ 2) :=
        Finset.sum_comm
    _ = ∑ _π : SlotPerms S J ℓ × SlotPerms B J ℓ,
          (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
            Pairing.fibSq 𝔭 𝒢 J ℓ n g :=
        Finset.sum_congr rfl fun π _ => by rw [← Finset.mul_sum, hre π]
    _ = Pairing.fibSq 𝔭 𝒢 J ℓ n g := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ hcard0.ne', one_mul]

end Perm

/-! ### The two sides of Schur's test -/

section Test

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-- **The pairing before the second symmetrization**: for `f = ∑_{n ∈ I} f_n u_n`,
`⟨f, 𝒜 g⟩ = ∑_{n ∈ I} conj(f_n) ∑_x m(n, x) ∑_ν ∑_{(r, x')} c_ν(n, x, r, x') (Sym g)(n + kD, x')`.
-/
theorem pairMarkFree_physOp_eq (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ}
    {N : Type} [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset 𝔭.Pos)
    (fn : 𝔭.Pos → ℂ) (g : PState 𝔭 𝒢 J ℓ → ℂ) :
    pairMarkFree 𝔭 𝒢 J ℓ I fn (physOp 𝔭 𝒢 q 𝔉 k ζ g) =
      ∑ n ∈ I, conj (fn n) * ∑ x : Lists 𝒢 J ℓ, (Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) *
        ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
          physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2 *
            physSym 𝔭 𝒢 J ℓ g (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2) := by
  unfold pairMarkFree
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [Pairing.physOp_apply, pairUnit_physSym, Pairing.pairUnit_eq_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun ν _ =>
    Pairing.physRow_apply_mk (𝔉 ν) k ζ (physSym 𝔭 𝒢 J ℓ g) n x

omit [DecidableEq S] [DecidableEq B] in
/-- **The weight of a transition seen from its target**: `m(n, x) |c_ν(n, x, r, x')|` is
`m(n', x') |c_ν(n' - kD', x, r, x')|` with `n' = n + kD(x, r)` and `D' = D(x', r)`. -/
theorem physWeight_mul_norm_physCoef_eq (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ}
    (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (n : 𝔭.Pos) (x x' : Lists 𝒢 J ℓ)
    (r : AuxList 𝒢.big ν.C) :
    Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖ =
      Pairing.physWeight 𝔭 𝒢 J ℓ (𝔭.shift (k * dil ν.C x r) n, x') *
        ‖physCoef 𝔭 𝒢 q ν k ζ
          (𝔭.shift (-(k * dil ν.C x' r)) (𝔭.shift (k * dil ν.C x r) n)) x r x'‖ := by
  by_cases hD : dil ν.C x' r = dil ν.C x r
  · rw [hD, 𝔭.shift_neg_shift]
    by_cases hc : physCoef 𝔭 𝒢 q ν k ζ n x r x' = 0
    · rw [hc, norm_zero, mul_zero, mul_zero]
    · obtain ⟨h1, h2⟩ := Pairing.isPhys_of_physCoef_ne_zero hc
      rw [Pairing.physWeight_of_isPhys h1, Pairing.physWeight_of_isPhys h2]
  · have hz : ∀ m : 𝔭.Pos, physCoef 𝔭 𝒢 q ν k ζ m x r x' = 0 := by
      intro m
      by_contra hne
      exact hD (dil_eq_of_physCoef_ne_zero hne)
    rw [hz n, hz, norm_zero, mul_zero, mul_zero]

/-- **The first side of Schur's test**: at a position `n`, the transitions from `n` have total
weight at most `R ‖u_n‖²`. -/
theorem sum_absW_le (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type}
    [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {R : ℝ}
    (hrow : ∀ s : PState 𝔭 𝒢 J ℓ, physAbsRowSum 𝔭 𝒢 q 𝔉 k ζ s ≤ R) (n : 𝔭.Pos) :
    ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
        Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ ≤
      R * unitNormSq 𝔭 𝒢 J ℓ n := by
  have hdef : ∀ x : Lists 𝒢 J ℓ, Schur.rowAbsMass 𝔭 𝒢 q 𝔉 k ζ (n, x) =
      ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
        ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ := fun _ => rfl
  have h1 : ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
        Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ =
      ∑ x : Lists 𝒢 J ℓ, Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) *
        Schur.rowAbsMass 𝔭 𝒢 q 𝔉 k ζ (n, x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hdef x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => (Finset.mul_sum _ _ _).symm
  rw [h1, Pairing.unitNormSq_eq_sum 𝔭 𝒢 J ℓ n]
  refine sum_mul_le_of_avg_le (fun x : Lists 𝒢 J ℓ => Pairing.physWeight 𝔭 𝒢 J ℓ (n, x))
    (fun x : Lists 𝒢 J ℓ => Schur.rowAbsMass 𝔭 𝒢 q 𝔉 k ζ (n, x))
    (fun x => Pairing.physWeight_nonneg 𝔭 𝒢 J ℓ _)
    (fun π x => Pairing.physWeight_permuteLists n x π) fun x => ?_
  exact le_of_eq_of_le (physAbsRowSum_eq_avg 𝔭 𝒢 q 𝔉 k ζ (n, x)).symm (hrow (n, x))

/-- **The second side of Schur's test**: for a function `u` invariant under the slot
permutations, the transitions from the positions of `I`, weighted by `|u|²` at their targets, have
total weight at most `R` times the part of `‖u‖²` on any set `U` of positions containing the
targets. -/
theorem sum_target_le (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type}
    [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {R : ℝ}
    (hcol : ∀ s : PState 𝔭 𝒢 J ℓ, physAbsColSum 𝔭 𝒢 q 𝔉 k ζ s ≤ R) (I U : Finset 𝔭.Pos)
    (hU : ∀ n ∈ I, ∀ (ν : N) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big (𝔉 ν).C),
      𝔭.shift (k * dil (𝔉 ν).C x r) n ∈ U)
    (u : PState 𝔭 𝒢 J ℓ → ℂ)
    (hu : ∀ (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (π : SlotPerms S J ℓ × SlotPerms B J ℓ),
      u (n, permuteLists π x) = u (n, x)) :
    ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
        Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ *
          ‖u (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2)‖ ^ 2 ≤
      R * ∑ n' ∈ U, Pairing.fibSq 𝔭 𝒢 J ℓ n' u := by
  -- the weight of a transition as a function of its target
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Lists 𝒢 J ℓ → (ν : N) → AuxList 𝒢.big (𝔉 ν).C → Lists 𝒢 J ℓ →
      𝔭.Pos → ℝ, ∀ x ν r x' n', Φ x ν r x' n' =
        Pairing.physWeight 𝔭 𝒢 J ℓ (n', x') *
          ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ (𝔭.shift (-(k * dil (𝔉 ν).C x' r)) n') x r x'‖ *
          ‖u (n', x')‖ ^ 2 := ⟨_, fun _ _ _ _ _ => rfl⟩
  have hΦ0 : ∀ x ν r x' n', 0 ≤ Φ x ν r x' n' := by
    intro x ν r x' n'
    rw [hΦ]
    exact mul_nonneg (mul_nonneg (Pairing.physWeight_nonneg 𝔭 𝒢 J ℓ _) (norm_nonneg _))
      (sq_nonneg _)
  -- one transition type: the sources in `I` are sent injectively into `U`
  have hstep : ∀ (x : Lists 𝒢 J ℓ) (ν : N) (ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ),
      ∑ n ∈ I, Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) *
          ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ *
          ‖u (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2)‖ ^ 2 ≤
        ∑ n' ∈ U, Φ x ν ξ.1 ξ.2 n' := by
    intro x ν ξ
    have h1 : ∑ n ∈ I, Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) *
          ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ *
          ‖u (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2)‖ ^ 2 =
        ∑ n ∈ I, Φ x ν ξ.1 ξ.2 (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n) :=
      Finset.sum_congr rfl fun n _ => by
        rw [hΦ, physWeight_mul_norm_physCoef_eq 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.2 ξ.1]
    have h2 : ∑ n ∈ I, Φ x ν ξ.1 ξ.2 (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n) =
        ∑ n' ∈ I.map (Pairing.shiftEquiv 𝔭 (k * dil (𝔉 ν).C x ξ.1)).toEmbedding,
          Φ x ν ξ.1 ξ.2 n' :=
      (Finset.sum_map I (Pairing.shiftEquiv 𝔭 (k * dil (𝔉 ν).C x ξ.1)).toEmbedding
        (Φ x ν ξ.1 ξ.2)).symm
    rw [h1, h2]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n' hn' => ?_)
      fun n' _ _ => hΦ0 x ν ξ.1 ξ.2 n'
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hn'
    exact hU n hn ν x ξ.1
  -- the column sum at a target state
  have hcolsum : ∀ (n' : 𝔭.Pos) (x' : Lists 𝒢 J ℓ),
      ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, Φ ξ.2 ν ξ.1 x' n' =
        Pairing.physWeight 𝔭 𝒢 J ℓ (n', x') * ‖u (n', x')‖ ^ 2 *
          Schur.colAbsMass 𝔭 𝒢 q 𝔉 k ζ (n', x') := by
    intro n' x'
    have hdef : Schur.colAbsMass 𝔭 𝒢 q 𝔉 k ζ (n', x') =
        ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
          ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ (𝔭.shift (-(k * dil (𝔉 ν).C x' ξ.1)) n') ξ.2 ξ.1 x'‖ :=
      rfl
    rw [hdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [hΦ]
    ring
  -- Schur's bound at one target position
  have hpos : ∀ n' : 𝔭.Pos,
      ∑ x' : Lists 𝒢 J ℓ, Pairing.physWeight 𝔭 𝒢 J ℓ (n', x') * ‖u (n', x')‖ ^ 2 *
          Schur.colAbsMass 𝔭 𝒢 q 𝔉 k ζ (n', x') ≤
        R * Pairing.fibSq 𝔭 𝒢 J ℓ n' u := by
    intro n'
    refine sum_mul_le_of_avg_le
      (fun x' : Lists 𝒢 J ℓ => Pairing.physWeight 𝔭 𝒢 J ℓ (n', x') * ‖u (n', x')‖ ^ 2)
      (fun x' : Lists 𝒢 J ℓ => Schur.colAbsMass 𝔭 𝒢 q 𝔉 k ζ (n', x'))
      (fun x' => mul_nonneg (Pairing.physWeight_nonneg 𝔭 𝒢 J ℓ _) (sq_nonneg _))
      (fun π x' => ?_) fun x' => ?_
    · show Pairing.physWeight 𝔭 𝒢 J ℓ (n', permuteLists π x') *
          ‖u (n', permuteLists π x')‖ ^ 2 =
        Pairing.physWeight 𝔭 𝒢 J ℓ (n', x') * ‖u (n', x')‖ ^ 2
      rw [Pairing.physWeight_permuteLists, hu]
    · exact le_of_eq_of_le (physAbsColSum_eq_avg 𝔭 𝒢 q 𝔉 k ζ (n', x')).symm (hcol (n', x'))
  calc ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
        Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ *
          ‖u (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2)‖ ^ 2
      = ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, ∑ n ∈ I,
          Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ *
            ‖u (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2)‖ ^ 2 :=
        sum_comm_inner I (fun n (x : Lists 𝒢 J ℓ) (ν : N)
          (ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ) =>
            Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ *
              ‖u (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2)‖ ^ 2)
    _ ≤ ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, ∑ n' ∈ U,
          Φ x ν ξ.1 ξ.2 n' :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun ν _ =>
          Finset.sum_le_sum fun ξ _ => hstep x ν ξ
    _ = ∑ n' ∈ U, ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
          Φ x ν ξ.1 ξ.2 n' :=
        (sum_comm_inner U (fun n' (x : Lists 𝒢 J ℓ) (ν : N)
          (ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ) => Φ x ν ξ.1 ξ.2 n')).symm
    _ = ∑ n' ∈ U, ∑ x' : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
          Φ ξ.2 ν ξ.1 x' n' :=
        Finset.sum_congr rfl fun n' _ =>
          sum_swap_lists (fun (x : Lists 𝒢 J ℓ) (ν : N) (r : AuxList 𝒢.big (𝔉 ν).C)
            (x' : Lists 𝒢 J ℓ) => Φ x ν r x' n')
    _ = ∑ n' ∈ U, ∑ x' : Lists 𝒢 J ℓ, Pairing.physWeight 𝔭 𝒢 J ℓ (n', x') *
          ‖u (n', x')‖ ^ 2 * Schur.colAbsMass 𝔭 𝒢 q 𝔉 k ζ (n', x') :=
        Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun x' _ => hcolsum n' x'
    _ ≤ ∑ n' ∈ U, R * Pairing.fibSq 𝔭 𝒢 J ℓ n' u := Finset.sum_le_sum fun n' _ => hpos n'
    _ = R * ∑ n' ∈ U, Pairing.fibSq 𝔭 𝒢 J ℓ n' u := (Finset.mul_sum _ _ _).symm

/-- **Schur's test for the pairing**, for a nonnegative bound `R` of the row and column sums and
an arbitrary position model. -/
theorem norm_pairMarkFree_physOp_le (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ}
    {N : Type} [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ s : PState 𝔭 𝒢 J ℓ, physAbsRowSum 𝔭 𝒢 q 𝔉 k ζ s ≤ R)
    (hcol : ∀ s : PState 𝔭 𝒢 J ℓ, physAbsColSum 𝔭 𝒢 q 𝔉 k ζ s ≤ R) (I : Finset 𝔭.Pos)
    (fn : 𝔭.Pos → ℂ) {g : PState 𝔭 𝒢 J ℓ → ℂ} (hg : MemPhysL2 𝔭 𝒢 J ℓ g) :
    ‖pairMarkFree 𝔭 𝒢 J ℓ I fn (physOp 𝔭 𝒢 q 𝔉 k ζ g)‖ ≤
      R * (Real.sqrt (markFreeNormSq 𝔭 𝒢 J ℓ I fn) *
        Real.sqrt (physNormSq 𝔭 𝒢 J ℓ g)) := by
  -- the weights and the two factors
  obtain ⟨W, hW⟩ : ∃ W : 𝔭.Pos → Lists 𝒢 J ℓ → (ν : N) →
      AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ → ℝ, ∀ n x ν ξ, W n x ν ξ =
        Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ :=
    ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : 𝔭.Pos → Lists 𝒢 J ℓ → (ν : N) →
      AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ → ℝ, ∀ n x ν ξ, β n x ν ξ =
        ‖physSym 𝔭 𝒢 J ℓ g (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2)‖ :=
    ⟨_, fun _ _ _ _ => rfl⟩
  have hW0 : ∀ n x ν ξ, 0 ≤ W n x ν ξ := by
    intro n x ν ξ
    rw [hW]
    exact mul_nonneg (Pairing.physWeight_nonneg 𝔭 𝒢 J ℓ _) (norm_nonneg _)
  have hβ0 : ∀ n x ν ξ, 0 ≤ β n x ν ξ := by
    intro n x ν ξ
    rw [hβ]
    exact norm_nonneg _
  -- the triangle inequality
  have hinner : ∀ (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ),
      ‖∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
          physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2 *
            physSym 𝔭 𝒢 J ℓ g (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2)‖ ≤
        ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
          ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ * β n x ν ξ := by
    intro n x
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun ξ _ => ?_))
    rw [norm_mul, hβ]
  have hmid : ∀ n : 𝔭.Pos,
      ‖∑ x : Lists 𝒢 J ℓ, (Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) *
          ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
            physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2 *
              physSym 𝔭 𝒢 J ℓ g (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2)‖ ≤
        ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
          W n x ν ξ * β n x ν ξ := by
    intro n
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, Complex.norm_of_nonneg (Pairing.physWeight_nonneg 𝔭 𝒢 J ℓ _)]
    refine (mul_le_mul_of_nonneg_left (hinner n x)
      (Pairing.physWeight_nonneg 𝔭 𝒢 J ℓ _)).trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [hW, mul_assoc]
  have hP : ‖pairMarkFree 𝔭 𝒢 J ℓ I fn (physOp 𝔭 𝒢 q 𝔉 k ζ g)‖ ≤
      ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
        W n x ν ξ * (‖fn n‖ * β n x ν ξ) := by
    rw [pairMarkFree_physOp_eq]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, Complex.norm_conj]
    refine (mul_le_mul_of_nonneg_left (hmid n) (norm_nonneg _)).trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    ring
  have hQ0 : 0 ≤ ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν,
      ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, W n x ν ξ * (‖fn n‖ * β n x ν ξ) :=
    Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun ν _ =>
      Finset.sum_nonneg fun ξ _ =>
        mul_nonneg (hW0 n x ν ξ) (mul_nonneg (norm_nonneg _) (hβ0 n x ν ξ))
  -- Cauchy–Schwarz
  have hcs := nested_cs I W (fun n _ _ _ => ‖fn n‖) β hW0
  -- the first side
  have hFnn : 0 ≤ markFreeNormSq 𝔭 𝒢 J ℓ I fn := by
    unfold markFreeNormSq
    refine Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) ?_
    unfold unitNormSq
    exact mul_nonneg (Pairing.stateMass_nonneg 𝒢 J ℓ) (Nat.cast_nonneg _)
  have hA : ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν,
      ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, W n x ν ξ * ‖fn n‖ ^ 2 ≤
        R * markFreeNormSq 𝔭 𝒢 J ℓ I fn := by
    have hn : ∀ n : 𝔭.Pos, ∑ x : Lists 𝒢 J ℓ, ∑ ν,
        ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, W n x ν ξ * ‖fn n‖ ^ 2 ≤
          R * (‖fn n‖ ^ 2 * unitNormSq 𝔭 𝒢 J ℓ n) := by
      intro n
      have e : ∑ x : Lists 𝒢 J ℓ, ∑ ν,
          ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, W n x ν ξ * ‖fn n‖ ^ 2 =
          (∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
            Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖) *
            ‖fn n‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun ξ _ => by rw [hW]
      rw [e]
      calc (∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
            Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖) *
            ‖fn n‖ ^ 2
          ≤ R * unitNormSq 𝔭 𝒢 J ℓ n * ‖fn n‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (sum_absW_le 𝔭 𝒢 q 𝔉 k ζ hrow n) (sq_nonneg _)
        _ = R * (‖fn n‖ ^ 2 * unitNormSq 𝔭 𝒢 J ℓ n) := by ring
    calc ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν,
          ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, W n x ν ξ * ‖fn n‖ ^ 2
        ≤ ∑ n ∈ I, R * (‖fn n‖ ^ 2 * unitNormSq 𝔭 𝒢 J ℓ n) :=
          Finset.sum_le_sum fun n _ => hn n
      _ = R * markFreeNormSq 𝔭 𝒢 J ℓ I fn := by
          unfold markFreeNormSq
          rw [Finset.mul_sum]
  -- the second side
  have hUfin : (Pairing.adjReach 𝔭 𝒢 𝔉 k (↑I : Set 𝔭.Pos)).Finite :=
    Pairing.adjReach_finite 𝔉 k I.finite_toSet
  have hUmem : ∀ n ∈ I, ∀ (ν : N) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big (𝔉 ν).C),
      𝔭.shift (k * dil (𝔉 ν).C x r) n ∈ hUfin.toFinset := by
    intro n hn ν x r
    refine (Set.Finite.mem_toFinset hUfin).mpr ⟨ν, x, r, ?_⟩
    rw [𝔭.shift_neg_shift]
    exact Finset.mem_coe.mpr hn
  have hGnn : 0 ≤ physNormSq 𝔭 𝒢 J ℓ g := Pairing.physNormSq_nonneg g
  have hB : ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν,
      ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, W n x ν ξ * β n x ν ξ ^ 2 ≤
        R * physNormSq 𝔭 𝒢 J ℓ g := by
    have h1 := sum_target_le 𝔭 𝒢 q 𝔉 k ζ hcol I hUfin.toFinset hUmem (physSym 𝔭 𝒢 J ℓ g)
      (fun n x π => physSym_apply_permuteLists 𝔭 𝒢 J ℓ g n x π)
    have h2 : ∑ n' ∈ hUfin.toFinset, Pairing.fibSq 𝔭 𝒢 J ℓ n' (physSym 𝔭 𝒢 J ℓ g) ≤
        physNormSq 𝔭 𝒢 J ℓ g :=
      (Finset.sum_le_sum fun n' _ => fibSq_physSym_le 𝔭 𝒢 J ℓ n' g).trans
        (Pairing.sum_fibSq_le_physNormSq hg _)
    have e : ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν,
        ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, W n x ν ξ * β n x ν ξ ^ 2 =
        ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
          Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) * ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2‖ *
            ‖physSym 𝔭 𝒢 J ℓ g (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n, ξ.2)‖ ^ 2 :=
      Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ξ _ => by rw [hW, hβ]
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hR)
  -- the conclusion
  have hBnn : 0 ≤ ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν,
      ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ, W n x ν ξ * β n x ν ξ ^ 2 :=
    Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun ν _ =>
      Finset.sum_nonneg fun ξ _ => mul_nonneg (hW0 n x ν ξ) (sq_nonneg _)
  have hmain : ‖pairMarkFree 𝔭 𝒢 J ℓ I fn (physOp 𝔭 𝒢 q 𝔉 k ζ g)‖ ^ 2 ≤
      R * markFreeNormSq 𝔭 𝒢 J ℓ I fn * (R * physNormSq 𝔭 𝒢 J ℓ g) :=
    calc ‖pairMarkFree 𝔭 𝒢 J ℓ I fn (physOp 𝔭 𝒢 q 𝔉 k ζ g)‖ ^ 2
        ≤ (∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
            W n x ν ξ * (‖fn n‖ * β n x ν ξ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hP 2
      _ ≤ (∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
            W n x ν ξ * ‖fn n‖ ^ 2) *
          ∑ n ∈ I, ∑ x : Lists 𝒢 J ℓ, ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
            W n x ν ξ * β n x ν ξ ^ 2 := hcs
      _ ≤ R * markFreeNormSq 𝔭 𝒢 J ℓ I fn * (R * physNormSq 𝔭 𝒢 J ℓ g) :=
          mul_le_mul hA hB hBnn (mul_nonneg hR hFnn)
  have hsq : R * markFreeNormSq 𝔭 𝒢 J ℓ I fn * (R * physNormSq 𝔭 𝒢 J ℓ g) =
      (R * (Real.sqrt (markFreeNormSq 𝔭 𝒢 J ℓ I fn) *
        Real.sqrt (physNormSq 𝔭 𝒢 J ℓ g))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hFnn, Real.sq_sqrt hGnn]
    ring
  calc ‖pairMarkFree 𝔭 𝒢 J ℓ I fn (physOp 𝔭 𝒢 q 𝔉 k ζ g)‖
      = Real.sqrt (‖pairMarkFree 𝔭 𝒢 J ℓ I fn (physOp 𝔭 𝒢 q 𝔉 k ζ g)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (R * markFreeNormSq 𝔭 𝒢 J ℓ I fn * (R * physNormSq 𝔭 𝒢 J ℓ g)) :=
        Real.sqrt_le_sqrt hmain
    _ = R * (Real.sqrt (markFreeNormSq 𝔭 𝒢 J ℓ I fn) *
          Real.sqrt (physNormSq 𝔭 𝒢 J ℓ g)) := by
        rw [hsq]
        exact Real.sqrt_sq (mul_nonneg hR (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

end Test

end SchurTest

/-- **Schur's test for the pairing** (`[P-06:0177–0180, 0306–0308]`): if the operator with
absolute coefficients and its adjoint have row sums at most `R` at every state, then
`|⟨f, 𝒜 g⟩| ≤ R ‖f‖ ‖g‖` for a mark-free `f` and every `g ∈ ℋ_ph`. -/
theorem schurPairing : SchurPairing := by
  intro S B _ _ _ _ 𝒢 q J ℓ N _ 𝔉 k ζ R hrow hcol I fn g hg
  rcases isEmpty_or_nonempty (Lists 𝒢 J ℓ) with hE | ⟨⟨x₀⟩⟩
  · -- no list at all: both sides vanish
    have := hE
    have h1 : pairMarkFree intPos 𝒢 J ℓ I fn (physOp intPos 𝒢 q 𝔉 k ζ g) = 0 := by
      unfold pairMarkFree
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [Pairing.pairUnit_eq_sum intPos 𝒢 J ℓ n, Fintype.sum_empty, mul_zero]
    have h2 : markFreeNormSq intPos 𝒢 J ℓ I fn = 0 := by
      unfold markFreeNormSq
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [Pairing.unitNormSq_eq_sum intPos 𝒢 J ℓ n, Fintype.sum_empty, mul_zero]
    refine le_of_eq ?_
    rw [h1, h2, norm_zero, Real.sqrt_zero, zero_mul, mul_zero]
  · have hR : 0 ≤ R :=
      (SchurTest.physAbsRowSum_nonneg intPos 𝒢 q 𝔉 k ζ ((0 : ℤ), x₀)).trans
        (hrow ((0 : ℤ), x₀))
    exact SchurTest.norm_pairMarkFree_physOp_le intPos 𝒢 q 𝔉 k ζ hR hrow hcol I fn hg

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
