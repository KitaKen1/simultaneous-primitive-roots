module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.Transfer
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.Ban
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Operators
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemPerm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lemma 3.10: the fibre operators of a clean edge

Source: `verification/stage7-sources/S-02.tex`, lines 971–985 (`[S-02:0971–0985]`).

"At any fixed Fourier frequency, translation and the closure factor contribute `e(σ_i Θ D_ℬ)` for
a real `Θ` … The scalar factor `(d')^{σ_i iζ}` has modulus one. Consequently the remaining
operator, on symmetric big active tests, is `𝒯(Θ)` or its adjoint, with two changes only: the
measures of active labels and fresh target integrations are `μ̃_g` in place of `μ_g`, and the
free/active collision ban remains in force."

For a clean edge `i`, the product `d = d'` of the shared small labels being fixed, the big-list
part of a transition is described by

* `cleanKappa D i d` — its coefficient: the probability of the auxiliary labels, `μ̃_g` of the
  fresh target labels, the ban of the auxiliary labels from the source and the target list, and
  the oriented multiplier `K_ν (d D_ℬ)^{iζ}` (or its conjugate with roles interchanged);
* `cleanStep D i d` — the step `σ_i k d D_ℬ`;
* `cleanTau D` — the target list.

`cleanFibOp_eq`: the fibre operator at the frequency `Θ` is the unimodular scalar
`d^{±iζ}` (`cleanUnit`) times the sum over the patterns of the row operations with the ideal
transition law and the multipliers `[ban] [ban] ρ_ν(target) · Φ_ν`, where `Φ_ν` (`cleanPhi`) is
the multiplier of `𝒯(Θ k d)` (forward edges) or of its adjoint (backward edges) and
`ρ_ν = ∏ μ̃_g/μ_g` over the fresh target labels (`cleanRho`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

section Fibre

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type}

open _root_.Classical in
/-- **The real weight of the big-list part of a clean transition**: zero unless the target retains
the shared labels and no auxiliary label occurs in the source or in the target list; otherwise the
probability of the auxiliary labels (law `μ_g`) times `μ̃_g` of the fresh target labels. -/
def cleanBeta (D : MemData 𝒢 J ℓ N) (ν : N) (x : LabelList 𝒢.big J ℓ)
    (r : AuxList 𝒢.big (D.fam ν).C) (x' : LabelList 𝒢.big J ℓ) : ℝ :=
  if SharedBig (D.fam ν).C x x' ∧ cleanBan (D.fam ν).C r x ∧ cleanBan (D.fam ν).C r x' then
    auxWeight 𝒢.big (D.fam ν).C r *
      ∏ g, ∏ sl : Slot J ℓ,
        (if Unshared ((D.fam ν).C g) sl then tiltLaw (𝒢.big g) D.q D.n (x' g sl) else 1)
  else 0

/-- **The oriented multiplier of a clean transition** for the product `d` of the shared small
labels: `K_ν (d D_ℬ)^{iζ}` on a forward edge, its conjugate with source and target interchanged on
a backward edge. -/
def cleanMult (D : MemData 𝒢 J ℓ N) (i d : ℕ) (ν : N) (x : LabelList 𝒢.big J ℓ)
    (r : AuxList 𝒢.big (D.fam ν).C) (x' : LabelList 𝒢.big J ℓ) : ℂ :=
  if i % 2 = 0 then
    (D.fam ν).K x x' r *
      ((d * bigDil (D.fam ν).C x r : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I)
  else
    conj ((D.fam ν).K x' x r *
      ((d * bigDil (D.fam ν).C x r : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I))

/-- The big-list choices of a clean transition: the pattern, the auxiliary labels and the target
list. -/
abbrev CleanXi (D : MemData 𝒢 J ℓ N) : Type :=
  Σ ν : N, AuxList 𝒢.big (D.fam ν).C × LabelList 𝒢.big J ℓ

/-- The coefficient of the big-list part of a clean transition. -/
def cleanKappa (D : MemData 𝒢 J ℓ N) (i d : ℕ) (x : LabelList 𝒢.big J ℓ) (ξ : CleanXi D) : ℂ :=
  ((cleanBeta D ξ.1 x ξ.2.1 ξ.2.2 : ℝ) : ℂ) * cleanMult D i d ξ.1 x ξ.2.1 ξ.2.2

/-- The step `σ_i k d D_ℬ` of a clean transition. -/
def cleanStep (D : MemData 𝒢 J ℓ N) (i d : ℕ) (x : LabelList 𝒢.big J ℓ) (ξ : CleanXi D) : ℤ :=
  edgeSign i * D.k * ((d * bigDil (D.fam ξ.1).C x ξ.2.1 : ℕ) : ℤ)

/-- The target list of a clean transition. -/
def cleanTau (D : MemData 𝒢 J ℓ N) (_x : LabelList 𝒢.big J ℓ) (ξ : CleanXi D) :
    LabelList 𝒢.big J ℓ := ξ.2.2

/-- The unimodular scalar `d^{iζ}` (forward edges) or its conjugate (backward edges). -/
def cleanUnit (D : MemData 𝒢 J ℓ N) (i d : ℕ) : ℂ :=
  if i % 2 = 0 then (d : ℂ) ^ ((D.ζ : ℂ) * Complex.I)
  else conj ((d : ℂ) ^ ((D.ζ : ℂ) * Complex.I))

/-- **The multiplier of the ideal operator at the frequency `Θ k d`** (forward edges) **or of its
adjoint** (backward edges). -/
def cleanPhi (D : MemData 𝒢 J ℓ N) (i d : ℕ) (Θ : ℝ) (ν : N) (x : LabelList 𝒢.big J ℓ)
    (r : AuxList 𝒢.big (D.fam ν).C) (x' : LabelList 𝒢.big J ℓ) : ℂ :=
  if i % 2 = 0 then
    (D.fam ν).K x x' r * dilPhase D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))) (bigDil (D.fam ν).C x r)
  else
    conj ((D.fam ν).K x' x r *
      dilPhase D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))) (bigDil (D.fam ν).C x' r))

open _root_.Classical in
/-- **The density of the fresh target labels**: `∏ μ̃_g/μ_g` over the unshared target slots. -/
def cleanRho (D : MemData 𝒢 J ℓ N) (ν : N) (x' : LabelList 𝒢.big J ℓ) : ℝ :=
  ∏ g, ∏ sl : Slot J ℓ,
    (if Unshared ((D.fam ν).C g) sl then
      tiltLaw (𝒢.big g) D.q D.n (x' g sl) / Graph.primeGroupLaw (𝒢.big g) (x' g sl) else 1)

open _root_.Classical in
omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- A product over the unshared slots: the slots of `C` and the last `ℓ` slots. -/
theorem clean_prod_unshared (Cg : Finset (Fin J)) (F : Slot J ℓ → ℝ) :
    ∏ sl : Slot J ℓ, (if Unshared Cg sl then F sl else 1) =
      (∏ i : Fin J, if i ∈ Cg then F (Sum.inl i) else 1) * ∏ j : Fin ℓ, F (Sum.inr j) := by
  rw [Fintype.prod_sum_type]
  refine congrArg₂ (fun a b : ℝ => a * b)
    (Finset.prod_congr rfl fun i _ => ite_congr_of_iff Iff.rfl rfl rfl)
    (Finset.prod_congr rfl fun j _ => ?_)
  exact if_pos (show Unshared Cg (Sum.inr j) from trivial)

open _root_.Classical in
omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- The law of the unshared target labels as a product over the slots. -/
theorem clean_unsharedWeight_eq (C : B → Finset (Fin J)) (x' : LabelList 𝒢.big J ℓ) :
    unsharedWeight 𝒢.big C x' =
      ∏ g, ∏ sl : Slot J ℓ,
        (if Unshared (C g) sl then Graph.primeGroupLaw (𝒢.big g) (x' g sl) else 1) := by
  unfold unsharedWeight
  exact Finset.prod_congr rfl fun g _ =>
    (clean_prod_unshared (C g) (fun sl => Graph.primeGroupLaw (𝒢.big g) (x' g sl))).symm

open _root_.Classical in
omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- The tilted law of the fresh target labels is the untilted law times the density. -/
theorem clean_tilt_prod_eq
    (hpos : ∀ g, ∀ p ∈ 𝒢.big g, 0 < Graph.primeGroupLaw (𝒢.big g) p)
    (D : MemData 𝒢 J ℓ N) (ν : N) (x' : LabelList 𝒢.big J ℓ) :
    ∏ g, ∏ sl : Slot J ℓ,
        (if Unshared ((D.fam ν).C g) sl then tiltLaw (𝒢.big g) D.q D.n (x' g sl) else 1) =
      unsharedWeight 𝒢.big (D.fam ν).C x' * cleanRho D ν x' := by
  rw [clean_unsharedWeight_eq]
  unfold cleanRho
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun sl _ => ?_
  split_ifs with h
  · rw [mul_comm, div_mul_cancel₀ _ (hpos g _ (x' g sl).2).ne']
  · rw [mul_one]

open _root_.Classical in
omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- The real weight of a clean transition, where the shared labels are retained. -/
theorem cleanBeta_eq (hpos : ∀ g, ∀ p ∈ 𝒢.big g, 0 < Graph.primeGroupLaw (𝒢.big g) p)
    (D : MemData 𝒢 J ℓ N) (ν : N) (x : LabelList 𝒢.big J ℓ) (r : AuxList 𝒢.big (D.fam ν).C)
    (x' : LabelList 𝒢.big J ℓ) (hSh : SharedBig (D.fam ν).C x x') :
    cleanBeta D ν x r x' =
      auxWeight 𝒢.big (D.fam ν).C r * unsharedWeight 𝒢.big (D.fam ν).C x' *
        (cleanBanInd (D.fam ν).C r x * cleanBanInd (D.fam ν).C r x' * cleanRho D ν x') := by
  by_cases h1 : cleanBan (D.fam ν).C r x
  · by_cases h2 : cleanBan (D.fam ν).C r x'
    · have e1 : cleanBanInd (D.fam ν).C r x = 1 := if_pos h1
      have e2 : cleanBanInd (D.fam ν).C r x' = 1 := if_pos h2
      have e3 : cleanBeta D ν x r x' = auxWeight 𝒢.big (D.fam ν).C r *
          ∏ g, ∏ sl : Slot J ℓ,
            (if Unshared ((D.fam ν).C g) sl then tiltLaw (𝒢.big g) D.q D.n (x' g sl) else 1) :=
        if_pos ⟨hSh, h1, h2⟩
      rw [e1, e2, e3, clean_tilt_prod_eq hpos D ν x']
      ring
    · have e2 : cleanBanInd (D.fam ν).C r x' = 0 := if_neg h2
      have e3 : cleanBeta D ν x r x' = 0 := if_neg fun h => h2 h.2.2
      rw [e2, e3]
      ring
  · have e1 : cleanBanInd (D.fam ν).C r x = 0 := if_neg h1
    have e3 : cleanBeta D ν x r x' = 0 := if_neg fun h => h1 h.2.1
    rw [e1, e3]
    ring

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- **The oriented multiplier and the phase of a clean transition** are the unimodular scalar
`d^{±iζ}` times the multiplier of the ideal operator at the frequency `Θ k d` (or of its
adjoint) [S-02:0971–0982]. -/
theorem cleanMult_phase_eq (D : MemData 𝒢 J ℓ N) (i d : ℕ) (Θ : ℝ) (ν : N)
    (x : LabelList 𝒢.big J ℓ) (r : AuxList 𝒢.big (D.fam ν).C) (x' : LabelList 𝒢.big J ℓ)
    (hSh : SharedBig (D.fam ν).C x x') :
    cleanMult D i d ν x r x' *
        expUnit (Θ * ((cleanStep D i d x (⟨ν, (r, x')⟩ : CleanXi D) : ℤ) : ℝ)) =
      cleanUnit D i d * cleanPhi D i d Θ ν x r x' := by
  have hcp : ((d * bigDil (D.fam ν).C x r : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I) =
      (d : ℂ) ^ ((D.ζ : ℂ) * Complex.I) *
        ((bigDil (D.fam ν).C x r : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I) := by
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  by_cases hi : i % 2 = 0
  · have es : edgeSign i = 1 := if_pos hi
    have e1 : cleanMult D i d ν x r x' = (D.fam ν).K x x' r *
        ((d * bigDil (D.fam ν).C x r : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I) := if_pos hi
    have e2 : cleanUnit D i d = (d : ℂ) ^ ((D.ζ : ℂ) * Complex.I) := if_pos hi
    have e3 : cleanPhi D i d Θ ν x r x' = (D.fam ν).K x x' r *
        dilPhase D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))) (bigDil (D.fam ν).C x r) := if_pos hi
    have e4 : expUnit (Θ * ((cleanStep D i d x (⟨ν, (r, x')⟩ : CleanXi D) : ℤ) : ℝ)) =
        expUnit (Θ * ((D.k : ℝ) * (d : ℝ)) * ((bigDil (D.fam ν).C x r : ℕ) : ℝ)) := by
      congr 1
      show Θ * ((edgeSign i * D.k * ((d * bigDil (D.fam ν).C x r : ℕ) : ℤ) : ℤ) : ℝ) = _
      rw [es]
      push_cast
      ring
    rw [e1, e2, e3, e4, hcp]
    unfold dilPhase
    ring
  · have es : edgeSign i = -1 := if_neg hi
    have e1 : cleanMult D i d ν x r x' = conj ((D.fam ν).K x' x r *
        ((d * bigDil (D.fam ν).C x r : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I)) := if_neg hi
    have e2 : cleanUnit D i d = conj ((d : ℂ) ^ ((D.ζ : ℂ) * Complex.I)) := if_neg hi
    have e3 : cleanPhi D i d Θ ν x r x' = conj ((D.fam ν).K x' x r *
        dilPhase D.ζ (Θ * ((D.k : ℝ) * (d : ℝ))) (bigDil (D.fam ν).C x' r)) := if_neg hi
    have hD : bigDil (D.fam ν).C x' r = bigDil (D.fam ν).C x r := bigDil_eq_of_shared hSh r
    have e4 : expUnit (Θ * ((cleanStep D i d x (⟨ν, (r, x')⟩ : CleanXi D) : ℤ) : ℝ)) =
        conj (expUnit (Θ * ((D.k : ℝ) * (d : ℝ)) * ((bigDil (D.fam ν).C x r : ℕ) : ℝ))) := by
      rw [clean_conj_expUnit]
      congr 1
      show Θ * ((edgeSign i * D.k * ((d * bigDil (D.fam ν).C x r : ℕ) : ℤ) : ℤ) : ℝ) = _
      rw [es]
      push_cast
      ring
    rw [e1, e2, e3, e4, hD, hcp]
    unfold dilPhase
    simp only [map_mul]
    ring

open _root_.Classical in
omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- **One coefficient of the fibre operator** [S-02:0971–0985]. -/
theorem clean_coef_eq (hpos : ∀ g, ∀ p ∈ 𝒢.big g, 0 < Graph.primeGroupLaw (𝒢.big g) p)
    (D : MemData 𝒢 J ℓ N) (i d : ℕ) (Θ : ℝ) (ν : N) (x : LabelList 𝒢.big J ℓ)
    (r : AuxList 𝒢.big (D.fam ν).C) (x' : LabelList 𝒢.big J ℓ) :
    cleanKappa D i d x (⟨ν, (r, x')⟩ : CleanXi D) *
        expUnit (Θ * ((cleanStep D i d x (⟨ν, (r, x')⟩ : CleanXi D) : ℤ) : ℝ)) =
      cleanUnit D i d * (if SharedBig (D.fam ν).C x x' then
        ((auxWeight 𝒢.big (D.fam ν).C r * unsharedWeight 𝒢.big (D.fam ν).C x' : ℝ) : ℂ) *
          (((cleanBanInd (D.fam ν).C r x * cleanBanInd (D.fam ν).C r x' * cleanRho D ν x' : ℝ) :
            ℂ) * cleanPhi D i d Θ ν x r x') else 0) := by
  by_cases hSh : SharedBig (D.fam ν).C x x'
  · rw [if_pos hSh]
    show ((cleanBeta D ν x r x' : ℝ) : ℂ) * cleanMult D i d ν x r x' *
      expUnit (Θ * ((cleanStep D i d x (⟨ν, (r, x')⟩ : CleanXi D) : ℤ) : ℝ)) = _
    rw [mul_assoc, cleanMult_phase_eq D i d Θ ν x r x' hSh, cleanBeta_eq hpos D ν x r x' hSh]
    push_cast
    ring
  · rw [if_neg hSh, mul_zero]
    have e : cleanBeta D ν x r x' = 0 := if_neg fun h => hSh h.1
    show ((cleanBeta D ν x r x' : ℝ) : ℂ) * cleanMult D i d ν x r x' *
      expUnit (Θ * ((cleanStep D i d x (⟨ν, (r, x')⟩ : CleanXi D) : ℤ) : ℝ)) = 0
    rw [e, Complex.ofReal_zero, zero_mul, zero_mul]

variable [Fintype N]

open _root_.Classical in
omit [Fintype S] [DecidableEq S] in
/-- **The fibre operator of a clean edge at the frequency `Θ`** [S-02:0971–0985]: the unimodular
scalar `d^{±iζ}` times the sum over the patterns of the row operations with the ideal transition
law and the multipliers `[ban][ban] ρ_ν Φ_ν`. -/
theorem cleanFibOp_eq (hpos : ∀ g, ∀ p ∈ 𝒢.big g, 0 < Graph.primeGroupLaw (𝒢.big g) p)
    (D : MemData 𝒢 J ℓ N) (i d : ℕ) (Θ : ℝ) :
    cleanFibOp (cleanKappa D i d) (cleanStep D i d) (cleanTau D) Θ =
      cleanUnit D i d • ∑ ν, cleanShRow (D.fam ν).C (fun x r x' =>
        ((cleanBanInd (D.fam ν).C r x * cleanBanInd (D.fam ν).C r x' * cleanRho D ν x' : ℝ) :
          ℂ) * cleanPhi D i d Θ ν x r x') := by
  refine LinearMap.ext fun g => funext fun x => ?_
  have hL : cleanFibOp (cleanKappa D i d) (cleanStep D i d) (cleanTau D) Θ g x =
      ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ x' : LabelList 𝒢.big J ℓ,
        cleanKappa D i d x (⟨ν, (r, x')⟩ : CleanXi D) *
          expUnit (Θ * ((cleanStep D i d x (⟨ν, (r, x')⟩ : CleanXi D) : ℤ) : ℝ)) * g x' := by
    unfold cleanFibOp
    rw [rowOp_apply]
    refine (Fintype.sum_sigma _).trans (Finset.sum_congr rfl fun ν _ => ?_)
    exact Fintype.sum_prod_type _
  have hR : (cleanUnit D i d • ∑ ν, cleanShRow (D.fam ν).C (fun x r x' =>
        ((cleanBanInd (D.fam ν).C r x * cleanBanInd (D.fam ν).C r x' * cleanRho D ν x' : ℝ) :
          ℂ) * cleanPhi D i d Θ ν x r x')) g x =
      ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ x' : LabelList 𝒢.big J ℓ,
        cleanUnit D i d * ((if SharedBig (D.fam ν).C x x' then
          ((auxWeight 𝒢.big (D.fam ν).C r * unsharedWeight 𝒢.big (D.fam ν).C x' : ℝ) : ℂ) *
            (((cleanBanInd (D.fam ν).C r x * cleanBanInd (D.fam ν).C r x' * cleanRho D ν x' :
              ℝ) : ℂ) * cleanPhi D i d Θ ν x r x') else 0) * g x') := by
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, LinearMap.sum_apply, Finset.sum_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [cleanShRow_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => Finset.mul_sum _ _ _
  rw [hL, hR]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun x' _ => ?_
  rw [clean_coef_eq hpos D i d Θ ν x r x']
  ring

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- The scalar `d^{±iζ}` has modulus at most one. -/
theorem norm_cleanUnit_le (D : MemData 𝒢 J ℓ N) (i d : ℕ) : ‖cleanUnit D i d‖ ≤ 1 := by
  unfold cleanUnit
  split_ifs
  · exact Schur.norm_natCast_cpow_mul_I_le_one d D.ζ
  · rw [RCLike.norm_conj]
    exact Schur.norm_natCast_cpow_mul_I_le_one d D.ζ

/-- The phase `D^{iζ} e(Θ D)` has modulus at most one. -/
theorem clean_norm_dilPhase_le (ζ Θ : ℝ) (D₀ : ℕ) : ‖dilPhase ζ Θ D₀‖ ≤ 1 := by
  unfold dilPhase
  rw [norm_mul, norm_expUnit, mul_one]
  exact Schur.norm_natCast_cpow_mul_I_le_one D₀ ζ

omit [Fintype S] [DecidableEq S] [Fintype N] in
/-- The multiplier of the ideal operator (or of its adjoint) is bounded by `sup |K_ν|`. -/
theorem norm_cleanPhi_le (D : MemData 𝒢 J ℓ N) (i d : ℕ) (Θ : ℝ) (ν : N)
    (x : LabelList 𝒢.big J ℓ) (r : AuxList 𝒢.big (D.fam ν).C) (x' : LabelList 𝒢.big J ℓ) :
    ‖cleanPhi D i d Θ ν x r x'‖ ≤ ((D.fam ν).supNorm : ℝ) := by
  unfold cleanPhi
  split_ifs
  · rw [norm_mul]
    exact (mul_le_mul ((D.fam ν).norm_K_le x x' r) (clean_norm_dilPhase_le _ _ _) (norm_nonneg _)
      (NNReal.coe_nonneg _)).trans (le_of_eq (mul_one _))
  · rw [RCLike.norm_conj, norm_mul]
    exact (mul_le_mul ((D.fam ν).norm_K_le x' x r) (clean_norm_dilPhase_le _ _ _) (norm_nonneg _)
      (NNReal.coe_nonneg _)).trans (le_of_eq (mul_one _))

end Fibre

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
