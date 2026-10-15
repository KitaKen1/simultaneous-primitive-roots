module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Leaves
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Ring

/-!
# Characters modulo `r`: the rational phase expansion and primitive induction

Source: `verification/stage7-sources/S-03.tex`, lines 340–351 (`[S-03:0340–0351]`).

Two of the general inputs of [S] Lemma 4.3 (`Comparison/Leaves.lean`).

* `rationalPhaseExpansion : RationalPhaseExpansion` — (eq:ideal-rational-expansion):
  `e(uv/r) = ∑_{ψ mod r} c_ψ ψ(v)` for `v` prime to `r`, with `∑_ψ |c_ψ| ≤ √φ(r)`. The coefficient
  is `c_ψ = φ(r)⁻¹ ∑_w e(uw/r) ψ(w⁻¹)` (`UnitCharacters.phaseCoeff`; `ψ(w⁻¹)` is the conjugate of
  `ψ(w)`). The expansion is the orthogonality relation
  `DirichletCharacter.sum_char_inv_mul_char_eq`; Parseval
  (`UnitCharacters.sum_norm_sq_phaseCoeff`: `∑_ψ |c_ψ|² = 1`) is the same relation applied to the
  product of two coefficients, and Cauchy–Schwarz over the `φ(r)` characters gives the bound.
* `primitiveInduction : PrimitiveInduction` — "the unique primitive character inducing `ψ` has
  conductor at most `r`": `DirichletCharacter.primitiveCharacter`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace UnitCharacters

/-! ### The phase `e(t)` -/

/-- `e(t + m) = e(t)` for an integer `m`. -/
theorem expUnit_add_intCast (t : ℝ) (m : ℤ) : expUnit (t + (m : ℝ)) = expUnit t := by
  unfold expUnit
  have h : (2 * Real.pi * Complex.I * ((t + (m : ℝ) : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * (t : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### Orthogonality on the units modulo `r` -/

theorem sum_char_inv_mul_char_self {r : ℕ} [NeZero r] (w : (ZMod r)ˣ) :
    ∑ ψ : DirichletCharacter ℂ r, ψ ((w : ZMod r)⁻¹) * ψ (w : ZMod r) = (r.totient : ℂ) := by
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ w.isUnit]
  exact if_pos rfl

theorem sum_char_inv_mul_char_of_ne {r : ℕ} [NeZero r] {w w' : (ZMod r)ˣ} (h : w ≠ w') :
    ∑ ψ : DirichletCharacter ℂ r, ψ ((w : ZMod r)⁻¹) * ψ (w' : ZMod r) = 0 := by
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ w.isUnit]
  exact if_neg fun h' => h (Units.ext h')

/-- There are `φ(r)` characters modulo `r`. -/
theorem card_dirichletCharacter (r : ℕ) [NeZero r] :
    Fintype.card (DirichletCharacter ℂ r) = r.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r

/-- `ψ(w⁻¹)` is the conjugate of `ψ(w)` for a unit `w`. -/
theorem conj_char_inv {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r) (w : (ZMod r)ˣ) :
    conj (ψ ((w : ZMod r)⁻¹)) = ψ (w : ZMod r) := by
  have h1 : ψ ((w : ZMod r)⁻¹) * ψ (w : ZMod r) = 1 := by
    rw [← map_mul ψ, ZMod.inv_mul_of_unit _ w.isUnit, map_one]
  have h2 : ψ (w : ZMod r) * conj (ψ (w : ZMod r)) = 1 := by
    rw [Complex.mul_conj', DirichletCharacter.unit_norm_eq_one ψ w, Complex.ofReal_one, one_pow]
  have h3 : ψ ((w : ZMod r)⁻¹) = conj (ψ (w : ZMod r)) := by
    calc ψ ((w : ZMod r)⁻¹)
        = ψ ((w : ZMod r)⁻¹) * (ψ (w : ZMod r) * conj (ψ (w : ZMod r))) := by rw [h2, mul_one]
      _ = (ψ ((w : ZMod r)⁻¹) * ψ (w : ZMod r)) * conj (ψ (w : ZMod r)) := by ring
      _ = conj (ψ (w : ZMod r)) := by rw [h1, one_mul]
  rw [h3, starRingEnd_self_apply]

/-- The orthogonality relation, summed against two functions on the units:
`∑_ψ (∑_w F(w) ψ(w⁻¹)) (∑_w H(w) ψ(w)) = φ(r) ∑_w F(w) H(w)`. -/
theorem sum_char_bilinear {r : ℕ} [NeZero r] (F H : (ZMod r)ˣ → ℂ) :
    ∑ ψ : DirichletCharacter ℂ r,
        (∑ w : (ZMod r)ˣ, F w * ψ ((w : ZMod r)⁻¹)) *
          (∑ w' : (ZMod r)ˣ, H w' * ψ (w' : ZMod r)) =
      (r.totient : ℂ) * ∑ w : (ZMod r)ˣ, F w * H w := by
  have h1 : ∀ ψ : DirichletCharacter ℂ r,
      (∑ w : (ZMod r)ˣ, F w * ψ ((w : ZMod r)⁻¹)) *
          (∑ w' : (ZMod r)ˣ, H w' * ψ (w' : ZMod r)) =
        ∑ w : (ZMod r)ˣ, ∑ w' : (ZMod r)ˣ,
          (F w * H w') * (ψ ((w : ZMod r)⁻¹) * ψ (w' : ZMod r)) := by
    intro ψ
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => by ring
  rw [Finset.sum_congr rfl fun ψ _ => h1 ψ, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_comm, Finset.sum_eq_single w]
  · rw [← Finset.mul_sum, sum_char_inv_mul_char_self, mul_comm]
  · intro w' _ hne
    rw [← Finset.mul_sum, sum_char_inv_mul_char_of_ne (Ne.symm hne), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

/-! ### The Fourier coefficients of `v ↦ e(uv/r)` -/

/-- The phase `w ↦ e(u w / r)` on the units modulo `r` (`w` is represented by its least
nonnegative residue). -/
def unitPhase (r : ℕ) (u : ℤ) (w : (ZMod r)ˣ) : ℂ :=
  expUnit ((u : ℝ) * (((w : ZMod r).val : ℕ) : ℝ) / (r : ℝ))

theorem norm_unitPhase (r : ℕ) (u : ℤ) (w : (ZMod r)ˣ) : ‖unitPhase r u w‖ = 1 :=
  norm_expUnit _

/-- The phase at the class of a natural number `v` prime to `r` is `e(uv/r)`. -/
theorem unitPhase_natCast (r : ℕ) [NeZero r] (u : ℤ) (v : ℕ) (hv : IsUnit (v : ZMod r)) :
    unitPhase r u hv.unit = expUnit ((u : ℝ) * (v : ℝ) / (r : ℝ)) := by
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hdiv : (v : ℝ) = (r : ℝ) * ((v / r : ℕ) : ℝ) + ((v % r : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod v r).symm
  have key : (u : ℝ) * (v : ℝ) / (r : ℝ) =
      (u : ℝ) * ((v % r : ℕ) : ℝ) / (r : ℝ) + ((u * ((v / r : ℕ) : ℤ) : ℤ) : ℝ) := by
    calc (u : ℝ) * (v : ℝ) / (r : ℝ)
        = ((u : ℝ) * ((v % r : ℕ) : ℝ) + (u : ℝ) * ((v / r : ℕ) : ℝ) * (r : ℝ)) / (r : ℝ) := by
          rw [hdiv]
          ring
      _ = (u : ℝ) * ((v % r : ℕ) : ℝ) / (r : ℝ) +
            (u : ℝ) * ((v / r : ℕ) : ℝ) * (r : ℝ) / (r : ℝ) := add_div _ _ _
      _ = (u : ℝ) * ((v % r : ℕ) : ℝ) / (r : ℝ) + (u : ℝ) * ((v / r : ℕ) : ℝ) := by
          rw [mul_div_cancel_right₀ _ hr0]
      _ = (u : ℝ) * ((v % r : ℕ) : ℝ) / (r : ℝ) + ((u * ((v / r : ℕ) : ℤ) : ℤ) : ℝ) := by
          rw [Int.cast_mul, Int.cast_natCast]
  unfold unitPhase
  rw [IsUnit.unit_spec, ZMod.val_natCast, key, expUnit_add_intCast]

/-- **The Fourier coefficient** `c_ψ = φ(r)⁻¹ ∑_w e(u w / r) ψ(w⁻¹)` of the phase `v ↦ e(uv/r)` on
the units modulo `r` [S-03:0342–0345]. -/
def phaseCoeff (r : ℕ) [NeZero r] (u : ℤ) (ψ : DirichletCharacter ℂ r) : ℂ :=
  (r.totient : ℂ)⁻¹ * ∑ w : (ZMod r)ˣ, unitPhase r u w * ψ ((w : ZMod r)⁻¹)

theorem totient_cast_ne_zero (r : ℕ) [NeZero r] : (r.totient : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne r))).ne'

/-- **Fourier inversion on the units**: `∑_ψ c_ψ ψ(w₀) = e(u w₀ / r)`. -/
theorem sum_phaseCoeff_mul (r : ℕ) [NeZero r] (u : ℤ) (w₀ : (ZMod r)ˣ) :
    ∑ ψ : DirichletCharacter ℂ r, phaseCoeff r u ψ * ψ (w₀ : ZMod r) = unitPhase r u w₀ := by
  have hφ : (r.totient : ℂ) ≠ 0 := totient_cast_ne_zero r
  have h1 : ∀ ψ : DirichletCharacter ℂ r, phaseCoeff r u ψ * ψ (w₀ : ZMod r) =
      ∑ w : (ZMod r)ˣ, ((r.totient : ℂ)⁻¹ * unitPhase r u w) *
        (ψ ((w : ZMod r)⁻¹) * ψ (w₀ : ZMod r)) := by
    intro ψ
    unfold phaseCoeff
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [Finset.sum_congr rfl fun ψ _ => h1 ψ, Finset.sum_comm, Finset.sum_eq_single w₀]
  · rw [← Finset.mul_sum, sum_char_inv_mul_char_self, mul_comm, ← mul_assoc, mul_inv_cancel₀ hφ,
      one_mul]
  · intro w _ hne
    rw [← Finset.mul_sum, sum_char_inv_mul_char_of_ne hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ w₀) h

/-- **Parseval**: `∑_ψ |c_ψ|² = 1` [S-03:0346–0347] ("in normalized counting measure the left side
has squared norm `1`"). -/
theorem sum_norm_sq_phaseCoeff (r : ℕ) [NeZero r] (u : ℤ) :
    ∑ ψ : DirichletCharacter ℂ r, ‖phaseCoeff r u ψ‖ ^ 2 = 1 := by
  have hφ : (r.totient : ℂ) ≠ 0 := totient_cast_ne_zero r
  have hc : ∀ ψ : DirichletCharacter ℂ r, ((‖phaseCoeff r u ψ‖ ^ 2 : ℝ) : ℂ) =
      ((r.totient : ℂ)⁻¹ * (r.totient : ℂ)⁻¹) *
        ((∑ w : (ZMod r)ˣ, unitPhase r u w * ψ ((w : ZMod r)⁻¹)) *
          (∑ w' : (ZMod r)ˣ, conj (unitPhase r u w') * ψ (w' : ZMod r))) := by
    intro ψ
    have hconj : conj (phaseCoeff r u ψ) =
        (r.totient : ℂ)⁻¹ * ∑ w' : (ZMod r)ˣ, conj (unitPhase r u w') * ψ (w' : ZMod r) := by
      unfold phaseCoeff
      rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun w' _ => by rw [map_mul, conj_char_inv]
    rw [Complex.ofReal_pow, ← Complex.mul_conj', hconj]
    unfold phaseCoeff
    ring
  have hG : ∀ w : (ZMod r)ˣ, unitPhase r u w * conj (unitPhase r u w) = 1 := by
    intro w
    rw [Complex.mul_conj', norm_unitPhase, Complex.ofReal_one, one_pow]
  have hsum : ((∑ ψ : DirichletCharacter ℂ r, ‖phaseCoeff r u ψ‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl fun ψ _ => hc ψ, ← Finset.mul_sum,
      sum_char_bilinear (unitPhase r u) (fun w' => conj (unitPhase r u w')),
      Finset.sum_congr rfl fun w _ => hG w, Finset.sum_const, Finset.card_univ,
      ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]
    calc ((r.totient : ℂ)⁻¹ * (r.totient : ℂ)⁻¹) * ((r.totient : ℂ) * (r.totient : ℂ))
        = ((r.totient : ℂ)⁻¹ * (r.totient : ℂ)) * ((r.totient : ℂ)⁻¹ * (r.totient : ℂ)) := by
          ring
      _ = 1 := by rw [inv_mul_cancel₀ hφ, mul_one]
  exact_mod_cast hsum

/-- **The coefficient bound** `∑_ψ |c_ψ| ≤ √φ(r)` [S-03:0344–0348]: Parseval and Cauchy–Schwarz
over the `φ(r)` characters. -/
theorem sum_norm_phaseCoeff_le (r : ℕ) [NeZero r] (u : ℤ) :
    ∑ ψ : DirichletCharacter ℂ r, ‖phaseCoeff r u ψ‖ ≤ Real.sqrt (r.totient : ℝ) := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (DirichletCharacter ℂ r)))
    (f := fun ψ => ‖phaseCoeff r u ψ‖)
  rw [Finset.card_univ, card_dirichletCharacter, sum_norm_sq_phaseCoeff, mul_one] at h1
  exact (le_abs_self _).trans (Real.abs_le_sqrt h1)

end UnitCharacters

/-! ### The two leaves -/

/-- **Fourier expansion on the units modulo `r`** (eq:ideal-rational-expansion)
[S-03:0340–0351]. -/
theorem rationalPhaseExpansion : RationalPhaseExpansion := by
  intro r u hr
  have : NeZero r := ⟨hr.ne'⟩
  refine ⟨UnitCharacters.phaseCoeff r u, UnitCharacters.sum_norm_phaseCoeff_le r u, fun v hv => ?_⟩
  have hunit : IsUnit (v : ZMod r) := (ZMod.isUnit_iff_coprime v r).mpr hv
  have h := UnitCharacters.sum_phaseCoeff_mul r u hunit.unit
  rw [IsUnit.unit_spec, UnitCharacters.unitPhase_natCast] at h
  exact h.symm

/-- **Primitive induction** [S-03:0349–0351]: the primitive character inducing `ψ`. -/
theorem primitiveInduction : PrimitiveInduction := by
  intro r ψ hr
  have : NeZero r := ⟨hr.ne'⟩
  refine ⟨DirichletCharacter.conductor ψ, DirichletCharacter.primitiveCharacter ψ,
    Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero ψ),
    DirichletCharacter.conductor_dvd_level ψ,
    DirichletCharacter.primitiveCharacter_isPrimitive ψ, fun v hv => ?_⟩
  have h := DirichletCharacter.primitiveCharacter_apply_of_isCoprime ψ (a := (v : ℤ))
    (Nat.isCoprime_iff_coprime.mpr hv)
  simp only [Int.cast_natCast] at h
  exact h.symm

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
