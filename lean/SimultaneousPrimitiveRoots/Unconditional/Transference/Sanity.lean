module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.PhysicalOperator
public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealOperator
import Mathlib.Tactic.Ring

/-!
# Sanity checks for the physical operator

Two proved facts which guard the definitions of `PhysicalOperator.lean`.

1. **`physAdj` is the adjoint of `physOp`** (`physAdj_adjoint_entry`): the matrix entry of `𝒜*`
   from `t` to `s` is the complex conjugate of the matrix entry of `𝒜` from `s` to `t`. All
   physical states have the same mass `∏_g V_g^{-M}`, so this is adjointness in `ℋ_ph`. The proof
   follows [S-02:0120–0130]: adjointness before symmetrization (`physRow_adjoint_entry`) and
   self-adjointness of the symmetrizing projection (its kernel `symKernel` is real and symmetric,
   `symKernel_symm`, `conj_symKernel`).

2. **The trivial case of an empty group family** (`physMoment_of_isEmpty`,
   `physMoment_eq_idealOpNorm_pow_of_isEmpty`): without groups a state is a position, `D = 1`,
   `𝒜 g (n) = (∑_ν K_ν) g (n + k)`, `𝒜* g (n) = conj(∑_ν K_ν) g (n - k)`, and
   `⟨u_n, (𝒜 𝒜*)^R u_n⟩ = |∑_ν K_ν|^{2R} = ‖𝒯(Θ)‖^{N}`, `N = 2R`. So in this case the transference
   inequality of Theorem 3.5 holds with `E_id = E`, as an identity.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators ComplexConjugate

noncomputable section

section PermuteLists

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ : ℕ}

/-- `x · π = y` if and only if `y · π⁻¹ = x`. -/
theorem permuteLists_eq_iff (π : SlotPerms S J ℓ × SlotPerms B J ℓ) (x y : Lists 𝒢 J ℓ) :
    permuteLists π x = y ↔ permuteLists π⁻¹ y = x := by
  constructor
  · rintro rfl
    exact Prod.ext (permuteSlots_inv_cancel π.1 x.1) (permuteSlots_inv_cancel π.2 x.2)
  · rintro rfl
    exact Prod.ext (permuteSlots_cancel_inv π.1 y.1) (permuteSlots_cancel_inv π.2 y.2)

end PermuteLists

section Adjoint

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝔭 : PosModel} {𝒢 : GroupFamily S B} {q : ℝ} {J ℓ : ℕ}

/-- The kernel of symmetrization in the list coordinate: `|G|⁻¹ #{π : x · π = y}` for the group
`G` of slot permutations. -/
def symKernel (x y : Lists 𝒢 J ℓ) : ℂ :=
  (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹ *
    ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ, if permuteLists π x = y then 1 else 0

/-- The symmetrization kernel is symmetric. -/
theorem symKernel_symm (x y : Lists 𝒢 J ℓ) : symKernel x y = symKernel y x := by
  unfold symKernel
  congr 1
  refine Fintype.sum_equiv (Equiv.inv (SlotPerms S J ℓ × SlotPerms B J ℓ)) _ _ fun π => ?_
  show (if permuteLists π x = y then (1 : ℂ) else 0) = if permuteLists π⁻¹ y = x then 1 else 0
  by_cases hxy : permuteLists π x = y
  · rw [if_pos hxy, if_pos ((permuteLists_eq_iff π x y).mp hxy)]
  · rw [if_neg hxy, if_neg fun h' => hxy ((permuteLists_eq_iff π x y).mpr h')]

/-- The symmetrization kernel is real. -/
theorem conj_symKernel (x y : Lists 𝒢 J ℓ) : conj (symKernel x y) = symKernel x y := by
  unfold symKernel
  rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun π _ => ?_
  split_ifs
  · exact map_one _
  · exact map_zero _

/-- Symmetrization is the kernel operator of `symKernel` in the list coordinate. -/
theorem physSym_apply_eq_sum (G : PState 𝔭 𝒢 J ℓ → ℂ) (s : PState 𝔭 𝒢 J ℓ) :
    physSym 𝔭 𝒢 J ℓ G s = ∑ y : Lists 𝒢 J ℓ, symKernel s.2 y * G (s.1, y) := by
  unfold physSym symKernel
  rw [rowOp_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_eq_single (permuteLists π s.2)]
  · rw [if_pos rfl, mul_one]
  · intro y _ hy
    rw [if_neg (Ne.symm hy), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The matrix entries of symmetrization. -/
theorem physSym_single [DecidableEq 𝔭.Pos] (t u : PState 𝔭 𝒢 J ℓ) :
    physSym 𝔭 𝒢 J ℓ (Pi.single t 1) u = if u.1 = t.1 then symKernel u.2 t.2 else 0 := by
  rw [physSym_apply_eq_sum, ← sum_ite_prod_mk_eq u.1 t (fun y => symKernel u.2 y)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Pi.single_apply]
  split_ifs <;> simp

/-- The symmetrization of a point mass is a combination of point masses at the same position. -/
theorem physSym_single_eq_sum [DecidableEq 𝔭.Pos] (t : PState 𝔭 𝒢 J ℓ) :
    physSym 𝔭 𝒢 J ℓ (Pi.single t 1) =
      ∑ y : Lists 𝒢 J ℓ, symKernel y t.2 • (Pi.single (t.1, y) 1 : PState 𝔭 𝒢 J ℓ → ℂ) := by
  funext u
  have h : ∀ y : Lists 𝒢 J ℓ,
      (symKernel y t.2 • (Pi.single (t.1, y) 1 : PState 𝔭 𝒢 J ℓ → ℂ)) u =
        if (t.1, y) = u then symKernel y t.2 else 0 := by
    intro y
    rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hu : u = (t.1, y)
    · rw [if_pos hu, if_pos hu.symm, mul_one]
    · rw [if_neg hu, if_neg fun h' => hu h'.symm, mul_zero]
  rw [physSym_single, Finset.sum_apply]
  simp only [h]
  rw [sum_ite_prod_mk_eq t.1 u (fun y => symKernel y t.2)]
  by_cases h1 : u.1 = t.1
  · rw [if_pos h1, if_pos h1.symm]
  · rw [if_neg h1, if_neg fun h' => h1 h'.symm]

/-- The matrix entries of `Sym ∘ R ∘ Sym` in terms of those of `R`. -/
theorem sym_comp_sym_single [DecidableEq 𝔭.Pos]
    (R : (PState 𝔭 𝒢 J ℓ → ℂ) →ₗ[ℂ] (PState 𝔭 𝒢 J ℓ → ℂ)) (s t : PState 𝔭 𝒢 J ℓ) :
    (physSym 𝔭 𝒢 J ℓ ∘ₗ R ∘ₗ physSym 𝔭 𝒢 J ℓ) (Pi.single t 1) s =
      ∑ y : Lists 𝒢 J ℓ, ∑ y' : Lists 𝒢 J ℓ,
        symKernel s.2 y * symKernel y' t.2 * R (Pi.single (t.1, y') 1) (s.1, y) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, physSym_apply_eq_sum, physSym_single_eq_sum,
    map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]
  ring

variable {N : Type} [Fintype N]

/-- Adjointness of the sum over patterns, before symmetrization. -/
theorem physRowSum_adjoint_entry [DecidableEq 𝔭.Pos] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ)
    (ζ : ℝ) (a b : PState 𝔭 𝒢 J ℓ) :
    (∑ ν, physRowAdj 𝔭 𝒢 q (𝔉 ν) k ζ) (Pi.single a 1) b =
      conj ((∑ ν, physRow 𝔭 𝒢 q (𝔉 ν) k ζ) (Pi.single b 1) a) := by
  simp only [LinearMap.sum_apply, Finset.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun ν _ => physRow_adjoint_entry (𝔉 ν) k ζ a b

/-- **`𝒜*` is the adjoint of `𝒜`** [S-02:0120–0130]: for all states `s`, `t`, the matrix entry of
`physAdj` from `t` to `s` is the complex conjugate of the matrix entry of `physOp` from `s` to
`t`. Since every physical state has the same mass `∏_g V_g^{-M}`, this says
`⟨δ_t, 𝒜* δ_s⟩ = conj ⟨δ_s, 𝒜 δ_t⟩` in `ℋ_ph`. -/
theorem physAdj_adjoint_entry [DecidableEq 𝔭.Pos] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s t : PState 𝔭 𝒢 J ℓ) :
    physAdj 𝔭 𝒢 q 𝔉 k ζ (Pi.single s 1) t = conj (physOp 𝔭 𝒢 q 𝔉 k ζ (Pi.single t 1) s) := by
  unfold physAdj physOp
  rw [sym_comp_sym_single, sym_comp_sym_single, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [map_mul, map_mul, conj_symKernel, conj_symKernel, symKernel_symm t.2 y',
    symKernel_symm y s.2, physRowSum_adjoint_entry]
  ring

end Adjoint

/-! ### The empty group family -/

section Empty

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  [IsEmpty S] [IsEmpty B] {𝔭 : PosModel} {𝒢 : GroupFamily S B} {q : ℝ} {J ℓ : ℕ}

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- Without groups every position carries exactly one state, and it is physical. -/
theorem isPhys_of_isEmpty (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) : IsPhys 𝔭 n x :=
  ⟨fun g => isEmptyElim g, fun g => isEmptyElim g, fun g => isEmptyElim g,
    fun g => isEmptyElim g⟩

omit [DecidableEq S] [DecidableEq B] in
/-- Without groups the dilation is the empty product `D = 1`. -/
theorem dil_of_isEmpty (C : B → Finset (Fin J)) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big C) :
    dil C x r = 1 := by
  unfold dil smallDil bigDil
  simp

/-- Without groups symmetrization is the identity. -/
theorem physSym_of_isEmpty (G : PState 𝔭 𝒢 J ℓ → ℂ) : physSym 𝔭 𝒢 J ℓ G = G := by
  funext s
  have hc : (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹ = 1 := by
    rw [Fintype.card_prod, Fintype.card_unique, Fintype.card_unique]
    norm_num
  unfold physSym
  rw [rowOp_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_unique, hc, one_mul]
  exact congrArg G
    (Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)))

omit [DecidableEq S] [DecidableEq B] in
/-- Without groups the coefficient of a row transition is `K_ν`. -/
theorem physCoef_of_isEmpty (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (n : 𝔭.Pos)
    (x x' : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C) :
    physCoef 𝔭 𝒢 q ν k ζ n x r x' = ν.K x.2 x'.2 r := by
  have hcond : IsPhys 𝔭 n x ∧ IsPhys 𝔭 (𝔭.shift (k * dil ν.C x r) n) x' ∧
      SharedSmall x.1 x'.1 ∧ SharedBig ν.C x.2 x'.2 ∧
      AuxAvoids ν.C r x ∧ AuxAvoids ν.C r x' :=
    ⟨isPhys_of_isEmpty _ _, isPhys_of_isEmpty _ _, fun g => isEmptyElim g,
      fun g => isEmptyElim g, fun g => isEmptyElim g, fun g => isEmptyElim g⟩
  have hdamp : ∀ n' : 𝔭.Pos, damping 𝔭 𝒢 J ℓ q n' = 1 := by
    intro n'
    unfold damping GroupFamily.omegaOf groupCount
    simp
  have h1 : auxWeight 𝒢.big ν.C r = 1 := by
    unfold auxWeight
    exact Fintype.prod_empty _
  have h2 : targetNorm 𝒢 ℓ ν.C = 1 := by
    unfold targetNorm
    simp
  unfold physCoef
  rw [if_pos hcond, h1, h2, hdamp, hdamp, dil_of_isEmpty]
  simp

/-- Without groups a row operation is `K_ν` times the translation by `k`. -/
theorem physRow_of_isEmpty (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (G : PState 𝔭 𝒢 J ℓ → ℂ)
    (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (y : LabelList 𝒢.big J ℓ) (r : AuxList 𝒢.big ν.C) :
    physRow 𝔭 𝒢 q ν k ζ G (n, x) = ν.K y y r * G (𝔭.shift k n, x) := by
  have key : ∀ (y₁ y₂ : LabelList 𝒢.big J ℓ) (r₁ : AuxList 𝒢.big ν.C) (z : Lists 𝒢 J ℓ),
      ν.K y₁ y₂ r₁ * G (𝔭.shift k n, z) = ν.K y y r * G (𝔭.shift k n, x) := by
    intro y₁ y₂ r₁ z
    have hz : z = x := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    rw [Subsingleton.elim y₁ y, Subsingleton.elim y₂ y, Subsingleton.elim r₁ r, hz]
  unfold physRow
  rw [rowOp_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_prod_type,
    Fintype.sum_unique, Fintype.sum_unique, physCoef_of_isEmpty, dil_of_isEmpty, Nat.cast_one,
    mul_one]
  exact key _ _ _ _

/-- Without groups an adjoint row operation is `conj K_ν` times the translation by `-k`. -/
theorem physRowAdj_of_isEmpty (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (G : PState 𝔭 𝒢 J ℓ → ℂ) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (y : LabelList 𝒢.big J ℓ)
    (r : AuxList 𝒢.big ν.C) :
    physRowAdj 𝔭 𝒢 q ν k ζ G (n, x) = conj (ν.K y y r) * G (𝔭.shift (-k) n, x) := by
  have key : ∀ (y₁ y₂ : LabelList 𝒢.big J ℓ) (r₁ : AuxList 𝒢.big ν.C) (z : Lists 𝒢 J ℓ),
      conj (ν.K y₁ y₂ r₁) * G (𝔭.shift (-k) n, z) =
        conj (ν.K y y r) * G (𝔭.shift (-k) n, x) := by
    intro y₁ y₂ r₁ z
    have hz : z = x := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    rw [Subsingleton.elim y₁ y, Subsingleton.elim y₂ y, Subsingleton.elim r₁ r, hz]
  unfold physRowAdj
  rw [rowOp_apply, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_prod_type,
    Fintype.sum_unique, Fintype.sum_unique, physCoef_of_isEmpty, dil_of_isEmpty, Nat.cast_one,
    mul_one]
  exact key _ _ _ _

variable {N : Type} [Fintype N]

/-- Without groups, `𝒜 g (n) = (∑_ν K_ν) g (n + k)`. -/
theorem physOp_of_isEmpty (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (G : PState 𝔭 𝒢 J ℓ → ℂ) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) :
    physOp 𝔭 𝒢 q 𝔉 k ζ G (n, x) =
      (∑ ν, (𝔉 ν).K default default default) * G (𝔭.shift k n, x) := by
  unfold physOp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, physSym_of_isEmpty, physSym_of_isEmpty,
    LinearMap.sum_apply, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ν _ => physRow_of_isEmpty (𝔉 ν) k ζ G n x default default

/-- Without groups, `𝒜* g (n) = conj(∑_ν K_ν) g (n - k)`. -/
theorem physAdj_of_isEmpty (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (G : PState 𝔭 𝒢 J ℓ → ℂ) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) :
    physAdj 𝔭 𝒢 q 𝔉 k ζ G (n, x) =
      conj (∑ ν, (𝔉 ν).K default default default) * G (𝔭.shift (-k) n, x) := by
  unfold physAdj
  rw [LinearMap.comp_apply, LinearMap.comp_apply, physSym_of_isEmpty, physSym_of_isEmpty,
    LinearMap.sum_apply, Finset.sum_apply, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ν _ => physRowAdj_of_isEmpty (𝔉 ν) k ζ G n x default default

/-- Without groups, `𝒜 𝒜*` is multiplication by `|∑_ν K_ν|²`. -/
theorem physOp_mul_physAdj_of_isEmpty (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (G : PState 𝔭 𝒢 J ℓ → ℂ) :
    (physOp 𝔭 𝒢 q 𝔉 k ζ * physAdj 𝔭 𝒢 q 𝔉 k ζ) G =
      ((∑ ν, (𝔉 ν).K default default default) *
        conj (∑ ν, (𝔉 ν).K default default default)) • G := by
  funext s
  obtain ⟨n, x⟩ := s
  rw [Module.End.mul_apply, physOp_of_isEmpty, physAdj_of_isEmpty, 𝔭.shift_neg_shift,
    Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- **The trivial case of the moment**: without groups,
`⟨u_n, (𝒜 𝒜*)^R u_n⟩ = |∑_ν K_ν|^{2R}`. -/
theorem physMoment_of_isEmpty (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (R : ℕ)
    (n : 𝔭.Pos) :
    physMoment 𝔭 𝒢 q 𝔉 k ζ R n = ‖∑ ν, (𝔉 ν).K default default default‖ ^ (2 * R) := by
  have hpow : ∀ (R : ℕ) (G : PState 𝔭 𝒢 J ℓ → ℂ),
      ((physOp 𝔭 𝒢 q 𝔉 k ζ * physAdj 𝔭 𝒢 q 𝔉 k ζ) ^ R) G =
        ((∑ ν, (𝔉 ν).K default default default) *
          conj (∑ ν, (𝔉 ν).K default default default)) ^ R • G := by
    intro R
    induction R with
    | zero =>
      intro G
      rw [pow_zero, pow_zero, one_smul]
      rfl
    | succ R ih =>
      intro G
      rw [pow_succ, Module.End.mul_apply, physOp_mul_physAdj_of_isEmpty, ih, smul_smul,
        ← pow_succ]
  have hmass : stateMass 𝒢 J ℓ = 1 := by
    unfold stateMass
    simp
  have hunit : ∀ x : Lists 𝒢 J ℓ, physUnit 𝔭 𝒢 J ℓ n (n, x) = 1 := by
    intro x
    unfold physUnit
    exact if_pos ⟨rfl, isPhys_of_isEmpty _ _⟩
  unfold physMoment pairUnit
  rw [hpow, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_unique,
    if_pos (isPhys_of_isEmpty _ _), hmass, Pi.smul_apply, hunit, smul_eq_mul,
    Complex.ofReal_one, one_mul, mul_one, Complex.mul_conj', ← pow_mul, ← Complex.ofReal_pow,
    Complex.ofReal_re]

/-- **Transference in the trivial case**: without groups the moment of (eq:transference-moment)
equals `‖𝒯(Θ)‖^{2R}` for every `Θ`. In particular `sup_Θ ‖𝒯(Θ)‖ ≤ L^{-E}` gives the bound
`L^{-EN}`, `N = 2R`, of Theorem 3.5. -/
theorem physMoment_eq_idealOpNorm_pow_of_isEmpty (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ)
    (ζ Θ : ℝ) (R : ℕ) (n : 𝔭.Pos) :
    physMoment 𝔭 𝒢 q 𝔉 k ζ R n = idealOpNorm 𝔉 ζ Θ ^ (2 * R) := by
  rw [physMoment_of_isEmpty, idealOpNorm_of_isEmpty]

end Empty

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
