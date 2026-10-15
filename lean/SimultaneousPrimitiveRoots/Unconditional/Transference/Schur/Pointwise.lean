module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.PhysicalOperator
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.Counting
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lemma 3.4: one row transition, summed over the lists of the other endpoint

Source: `verification/stage7-sources/S-02.tex`, lines 142–158 (`[S-02:0142–0158]`).

Fix a pattern `ν`, auxiliary free labels `r`, a position `p` and a list `a`. The lists `b` which
are physical at `p` and have the shared labels of `a` factor over the groups, and so do the
coefficient `∏_g V_g^{-t_g}` (`targetNorm`) and the damping `q^{(ω(p) - Ms)/2}`. Hence

`∑_b 1[b physical at p, shared labels of a] ∏_g V_g^{-t_g} q^{(ω(p) - Ms)/2} ≤ ∏_g C`

with the constant `C = groupConst v₋ q T` of (eq:physical-count-bound)
(`sum_sharedWeight_le`). This is used twice:

* rows (`sum_norm_physCoef_row_le`): `a` is the source list, `p = n + kD` the target position,
  `b` runs over the target lists;
* columns (`sum_norm_physCoef_col_le`): `a` is the target list, `p = n' - kD` the source
  position, `b` runs over the source lists ("the reversed normalization in
  (eq:physical-joint-measure) gives the identical argument for columns").

The other factors of the coefficient are bounded pointwise (`norm_physCoef_le`): `|D^{iζ}| ≤ 1`,
`|K_ν| ≤ sup |K_ν|`, and the damping of the endpoint which is not summed is at most one because
that endpoint is physical (`damping_le_one`: "the source damping is at most one"). The ban
conditions `AuxAvoids` are dropped ("restrictions can only decrease an absolute sum").

Everything is proved for an arbitrary position model `𝔭` and an arbitrary family of groups with
`V_g ≥ v₋ > 0`: "neither argument used any property of integer positions beyond divisibility and
translation".
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Schur

open scoped BigOperators

noncomputable section

/-! ### Signs and sizes of the factors of the coefficient -/

theorem reciprocalMass_nonneg (s : Finset ℕ) : 0 ≤ Graph.primeGroupReciprocalMass s := by
  unfold Graph.primeGroupReciprocalMass
  exact Finset.sum_nonneg fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg p)

theorem primeGroupLaw_nonneg (s : Finset ℕ) (p : ℕ) : 0 ≤ Graph.primeGroupLaw s p := by
  unfold Graph.primeGroupLaw
  exact div_nonneg zero_le_one (mul_nonneg (reciprocalMass_nonneg s) (Nat.cast_nonneg p))

theorem auxWeight_nonneg {B : Type} [Fintype B] {J : ℕ} (big : B → Finset ℕ)
    (C : B → Finset (Fin J)) (r : AuxList big C) : 0 ≤ auxWeight big C r := by
  unfold auxWeight
  exact Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => primeGroupLaw_nonneg _ _

theorem targetNorm_nonneg {S B : Type} [Fintype S] [Fintype B] (𝒢 : GroupFamily S B) {J : ℕ}
    (ℓ : ℕ) (C : B → Finset (Fin J)) : 0 ≤ targetNorm 𝒢 ℓ C := by
  unfold targetNorm
  exact mul_nonneg
    (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (reciprocalMass_nonneg _) _))
    (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (reciprocalMass_nonneg _) _))

theorem damping_pos {S B : Type} [Fintype S] [Fintype B] (𝔭 : PosModel) (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) {q : ℝ} (hq : 0 < q) (n : 𝔭.Pos) : 0 < damping 𝔭 𝒢 J ℓ q n := by
  unfold damping
  exact Real.rpow_pos_of_pos hq _

/-- The phase `D^{iζ}` has modulus at most one (it has modulus one when `D ≠ 0`). -/
theorem norm_natCast_cpow_mul_I_le_one (D : ℕ) (ζ : ℝ) :
    ‖((D : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    by_cases hζ : (ζ : ℂ) * Complex.I = 0
    · exact le_of_eq (by rw [hζ, Complex.cpow_zero, norm_one])
    · rw [Nat.cast_zero, Complex.zero_cpow hζ, norm_zero]
      exact zero_le_one
  · have hre : ((ζ : ℂ) * Complex.I).re = 0 := by simp
    exact le_of_eq (by rw [Complex.norm_natCast_cpow_of_pos hD, hre, Real.rpow_zero])

/-- The damping `q^{(ω(p) - Ms)/2}` is the product over the groups of `q^{(ω_g(p) - M)/2}`. -/
theorem damping_eq_prod {S B : Type} [Fintype S] [Fintype B] (𝔭 : PosModel)
    (𝒢 : GroupFamily S B) (J ℓ : ℕ) {q : ℝ} (hq : 0 < q) (p : 𝔭.Pos) :
    damping 𝔭 𝒢 J ℓ q p =
      (∏ g : S, q ^ ((((countHits (fun r => 𝔭.hit r p) (𝒢.small g) : ℕ) : ℝ) -
          ((J + ℓ : ℕ) : ℝ)) / 2)) *
        ∏ g : B, q ^ ((((countHits (fun r => 𝔭.hit r p) (𝒢.big g) : ℕ) : ℝ) -
          ((J + ℓ : ℕ) : ℝ)) / 2) := by
  have hS : ∑ g : S, (((countHits (fun r => 𝔭.hit r p) (𝒢.small g) : ℕ) : ℝ) -
        ((J + ℓ : ℕ) : ℝ)) / 2 =
      ((∑ g : S, ((countHits (fun r => 𝔭.hit r p) (𝒢.small g) : ℕ) : ℝ)) -
        (Fintype.card S : ℝ) * ((J + ℓ : ℕ) : ℝ)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hB : ∑ g : B, (((countHits (fun r => 𝔭.hit r p) (𝒢.big g) : ℕ) : ℝ) -
        ((J + ℓ : ℕ) : ℝ)) / 2 =
      ((∑ g : B, ((countHits (fun r => 𝔭.hit r p) (𝒢.big g) : ℕ) : ℝ)) -
        (Fintype.card B : ℝ) * ((J + ℓ : ℕ) : ℝ)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hexp : (((𝒢.omegaOf (fun r => 𝔭.hit r p) : ℕ) : ℝ) -
        ((J + ℓ : ℕ) : ℝ) * ((groupCount S B : ℕ) : ℝ)) / 2 =
      (∑ g : S, (((countHits (fun r => 𝔭.hit r p) (𝒢.small g) : ℕ) : ℝ) -
        ((J + ℓ : ℕ) : ℝ)) / 2) +
      ∑ g : B, (((countHits (fun r => 𝔭.hit r p) (𝒢.big g) : ℕ) : ℝ) -
        ((J + ℓ : ℕ) : ℝ)) / 2 := by
    rw [hS, hB]
    unfold GroupFamily.omegaOf groupCount
    push_cast
    ring
  unfold damping
  rw [hexp, Real.rpow_add hq, Real.rpow_sum_of_pos hq, Real.rpow_sum_of_pos hq]

/-- "The source damping is at most one" [S-02:0150–0151]: at a physical state every group has at
least `M` hits, so `ω ≥ Ms` and `q^{(ω - Ms)/2} ≤ 1`. -/
theorem damping_le_one {S B : Type} [Fintype S] [Fintype B] {𝔭 : PosModel}
    {𝒢 : GroupFamily S B} {J ℓ : ℕ} {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) {n : 𝔭.Pos}
    {x : Lists 𝒢 J ℓ} (h : IsPhys 𝔭 n x) : damping 𝔭 𝒢 J ℓ q n ≤ 1 := by
  have hS : Fintype.card S * (J + ℓ) ≤
      ∑ g : S, countHits (fun r => 𝔭.hit r n) (𝒢.small g) := by
    calc Fintype.card S * (J + ℓ) = ∑ _g : S, (J + ℓ) := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ g : S, countHits (fun r => 𝔭.hit r n) (𝒢.small g) :=
          Finset.sum_le_sum fun g _ =>
            slots_le_countHits (hit := fun r => 𝔭.hit r n) (x.1 g) (h.1 g) (h.2.2.1 g)
  have hB : Fintype.card B * (J + ℓ) ≤
      ∑ g : B, countHits (fun r => 𝔭.hit r n) (𝒢.big g) := by
    calc Fintype.card B * (J + ℓ) = ∑ _g : B, (J + ℓ) := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ g : B, countHits (fun r => 𝔭.hit r n) (𝒢.big g) :=
          Finset.sum_le_sum fun g _ =>
            slots_le_countHits (hit := fun r => 𝔭.hit r n) (x.2 g) (h.2.1 g) (h.2.2.2 g)
  have hnat : (J + ℓ) * groupCount S B ≤ 𝒢.omegaOf (fun r => 𝔭.hit r n) := by
    unfold GroupFamily.omegaOf groupCount
    calc (J + ℓ) * (Fintype.card S + Fintype.card B)
        = Fintype.card S * (J + ℓ) + Fintype.card B * (J + ℓ) := by ring
      _ ≤ ∑ g : S, countHits (fun r => 𝔭.hit r n) (𝒢.small g) +
            ∑ g : B, countHits (fun r => 𝔭.hit r n) (𝒢.big g) := Nat.add_le_add hS hB
  have hreal : ((J + ℓ : ℕ) : ℝ) * ((groupCount S B : ℕ) : ℝ) ≤
      ((𝒢.omegaOf (fun r => 𝔭.hit r n) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  unfold damping
  exact Real.rpow_le_one hq.le hq1 (div_nonneg (sub_nonneg.mpr hreal) zero_le_two)

/-! ### The coefficient of one row transition -/

/-- The modulus of a coefficient: `|D^{iζ}| ≤ 1` and `|K_ν| ≤ sup |K_ν|`. -/
theorem norm_physCoef_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq B] (𝔭 : PosModel)
    (𝒢 : GroupFamily S B) {q : ℝ} (hq : 0 < q) {J ℓ : ℕ} (ν : Pattern 𝒢.big J ℓ) (k : ℤ)
    (ζ : ℝ) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C) (x' : Lists 𝒢 J ℓ) :
    ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖ ≤
      auxWeight 𝒢.big ν.C r * targetNorm 𝒢 ℓ ν.C *
          (damping 𝔭 𝒢 J ℓ q n * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n)) *
        (ν.supNorm : ℝ) := by
  have hA : 0 ≤ auxWeight 𝒢.big ν.C r * targetNorm 𝒢 ℓ ν.C *
      (damping 𝔭 𝒢 J ℓ q n * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n)) :=
    mul_nonneg (mul_nonneg (auxWeight_nonneg 𝒢.big ν.C r) (targetNorm_nonneg 𝒢 ℓ ν.C))
      (mul_nonneg (damping_pos 𝔭 𝒢 J ℓ hq n).le (damping_pos 𝔭 𝒢 J ℓ hq _).le)
  unfold physCoef
  split_ifs with hc
  · rw [norm_mul, Complex.norm_of_nonneg hA, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ hA
    calc ‖ν.K x.2 x'.2 r‖ * ‖((dil ν.C x r : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I)‖
        ≤ (ν.supNorm : ℝ) * 1 :=
          mul_le_mul (ν.norm_K_le x.2 x'.2 r) (norm_natCast_cpow_mul_I_le_one _ ζ)
            (norm_nonneg _) (NNReal.coe_nonneg _)
      _ = (ν.supNorm : ℝ) := mul_one _
  · rw [norm_zero]
    exact mul_nonneg hA (NNReal.coe_nonneg _)

theorem physCoef_eq_zero_of_not {S B : Type} [Fintype S] [Fintype B] {𝔭 : PosModel}
    {𝒢 : GroupFamily S B} {q : ℝ} {J ℓ : ℕ} {ν : Pattern 𝒢.big J ℓ} {k : ℤ} {ζ : ℝ}
    {n : 𝔭.Pos} {x : Lists 𝒢 J ℓ} {r : AuxList 𝒢.big ν.C} {x' : Lists 𝒢 J ℓ}
    (h : ¬(IsPhys 𝔭 n x ∧ IsPhys 𝔭 (𝔭.shift (k * dil ν.C x r) n) x' ∧
      SharedSmall x.1 x'.1 ∧ SharedBig ν.C x.2 x'.2 ∧
      AuxAvoids ν.C r x ∧ AuxAvoids ν.C r x')) :
    physCoef 𝔭 𝒢 q ν k ζ n x r x' = 0 := by
  unfold physCoef
  exact if_neg h

open Classical in
/-- The weight of a list `b` at the position `p`, relative to a list `a`: the coefficient
`∏_g V_g^{-t_g}` times the damping at `p` if `b` is physical at `p` and has the shared labels of
`a`, and zero otherwise. The condition is symmetric in `a` and `b` up to the equalities of the
shared labels. -/
def sharedWeight {S B : Type} [Fintype S] [Fintype B] (𝔭 : PosModel) (𝒢 : GroupFamily S B)
    (q : ℝ) {J ℓ : ℕ} (C : B → Finset (Fin J)) (p : 𝔭.Pos) (a b : Lists 𝒢 J ℓ) : ℝ :=
  if IsPhys 𝔭 p b ∧ SharedSmall a.1 b.1 ∧ SharedBig C a.2 b.2 then
    targetNorm 𝒢 ℓ C * damping 𝔭 𝒢 J ℓ q p
  else 0

theorem sharedWeight_nonneg {S B : Type} [Fintype S] [Fintype B] (𝔭 : PosModel)
    (𝒢 : GroupFamily S B) {q : ℝ} (hq : 0 < q) {J ℓ : ℕ} (C : B → Finset (Fin J)) (p : 𝔭.Pos)
    (a b : Lists 𝒢 J ℓ) : 0 ≤ sharedWeight 𝔭 𝒢 q C p a b := by
  unfold sharedWeight
  split_ifs
  · exact mul_nonneg (targetNorm_nonneg 𝒢 ℓ C) (damping_pos 𝔭 𝒢 J ℓ hq p).le
  · exact le_rfl

/-- **Rows**: the coefficient of the transition `(n, x) → (n + kD, x')` is at most the
probability of the auxiliary labels, times `sup |K_ν|`, times the weight of the target list `x'`
at the target position relative to the source list `x`. -/
theorem norm_physCoef_le_row {S B : Type} [Fintype S] [Fintype B] [DecidableEq B]
    (𝔭 : PosModel) (𝒢 : GroupFamily S B) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) {J ℓ : ℕ}
    (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ)
    (r : AuxList 𝒢.big ν.C) (x' : Lists 𝒢 J ℓ) :
    ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖ ≤
      auxWeight 𝒢.big ν.C r * (ν.supNorm : ℝ) *
        sharedWeight 𝔭 𝒢 q ν.C (𝔭.shift (k * dil ν.C x r) n) x x' := by
  have haux : 0 ≤ auxWeight 𝒢.big ν.C r := auxWeight_nonneg 𝒢.big ν.C r
  have hsup : (0 : ℝ) ≤ (ν.supNorm : ℝ) := NNReal.coe_nonneg _
  have htn : 0 ≤ targetNorm 𝒢 ℓ ν.C := targetNorm_nonneg 𝒢 ℓ ν.C
  by_cases hc : IsPhys 𝔭 n x ∧ IsPhys 𝔭 (𝔭.shift (k * dil ν.C x r) n) x' ∧
      SharedSmall x.1 x'.1 ∧ SharedBig ν.C x.2 x'.2 ∧
      AuxAvoids ν.C r x ∧ AuxAvoids ν.C r x'
  · have hsw : sharedWeight 𝔭 𝒢 q ν.C (𝔭.shift (k * dil ν.C x r) n) x x' =
        targetNorm 𝒢 ℓ ν.C * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n) := by
      unfold sharedWeight
      exact if_pos ⟨hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
    have hd : 0 < damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n) :=
      damping_pos 𝔭 𝒢 J ℓ hq _
    have h1 : damping 𝔭 𝒢 J ℓ q n * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n) ≤
        damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n) := by
      calc damping 𝔭 𝒢 J ℓ q n * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n)
          ≤ 1 * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n) :=
            mul_le_mul_of_nonneg_right (damping_le_one hq hq1 hc.1) hd.le
        _ = damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n) := one_mul _
    rw [hsw]
    calc ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖
        ≤ auxWeight 𝒢.big ν.C r * targetNorm 𝒢 ℓ ν.C *
              (damping 𝔭 𝒢 J ℓ q n * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n)) *
            (ν.supNorm : ℝ) := norm_physCoef_le 𝔭 𝒢 hq ν k ζ n x r x'
      _ ≤ auxWeight 𝒢.big ν.C r * targetNorm 𝒢 ℓ ν.C *
              damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n) * (ν.supNorm : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (mul_nonneg haux htn)) hsup
      _ = auxWeight 𝒢.big ν.C r * (ν.supNorm : ℝ) *
            (targetNorm 𝒢 ℓ ν.C * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n)) := by
          ring
  · rw [physCoef_eq_zero_of_not hc, norm_zero]
    exact mul_nonneg (mul_nonneg haux hsup) (sharedWeight_nonneg 𝔭 𝒢 hq ν.C _ x x')

/-- **Columns**: the same coefficient is at most the probability of the auxiliary labels, times
`sup |K_ν|`, times the weight of the source list `x` at the source position relative to the
target list `x'`. -/
theorem norm_physCoef_le_col {S B : Type} [Fintype S] [Fintype B] [DecidableEq B]
    (𝔭 : PosModel) (𝒢 : GroupFamily S B) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) {J ℓ : ℕ}
    (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ)
    (r : AuxList 𝒢.big ν.C) (x' : Lists 𝒢 J ℓ) :
    ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖ ≤
      auxWeight 𝒢.big ν.C r * (ν.supNorm : ℝ) * sharedWeight 𝔭 𝒢 q ν.C n x' x := by
  have haux : 0 ≤ auxWeight 𝒢.big ν.C r := auxWeight_nonneg 𝒢.big ν.C r
  have hsup : (0 : ℝ) ≤ (ν.supNorm : ℝ) := NNReal.coe_nonneg _
  have htn : 0 ≤ targetNorm 𝒢 ℓ ν.C := targetNorm_nonneg 𝒢 ℓ ν.C
  by_cases hc : IsPhys 𝔭 n x ∧ IsPhys 𝔭 (𝔭.shift (k * dil ν.C x r) n) x' ∧
      SharedSmall x.1 x'.1 ∧ SharedBig ν.C x.2 x'.2 ∧
      AuxAvoids ν.C r x ∧ AuxAvoids ν.C r x'
  · have hsw : sharedWeight 𝔭 𝒢 q ν.C n x' x =
        targetNorm 𝒢 ℓ ν.C * damping 𝔭 𝒢 J ℓ q n := by
      unfold sharedWeight
      exact if_pos ⟨hc.1, fun g i => (hc.2.2.1 g i).symm,
        fun g i hi => (hc.2.2.2.1 g i hi).symm⟩
    have hd : 0 < damping 𝔭 𝒢 J ℓ q n := damping_pos 𝔭 𝒢 J ℓ hq n
    have h1 : damping 𝔭 𝒢 J ℓ q n * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n) ≤
        damping 𝔭 𝒢 J ℓ q n := by
      calc damping 𝔭 𝒢 J ℓ q n * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n)
          ≤ damping 𝔭 𝒢 J ℓ q n * 1 :=
            mul_le_mul_of_nonneg_left (damping_le_one hq hq1 hc.2.1) hd.le
        _ = damping 𝔭 𝒢 J ℓ q n := mul_one _
    rw [hsw]
    calc ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖
        ≤ auxWeight 𝒢.big ν.C r * targetNorm 𝒢 ℓ ν.C *
              (damping 𝔭 𝒢 J ℓ q n * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n)) *
            (ν.supNorm : ℝ) := norm_physCoef_le 𝔭 𝒢 hq ν k ζ n x r x'
      _ ≤ auxWeight 𝒢.big ν.C r * targetNorm 𝒢 ℓ ν.C * damping 𝔭 𝒢 J ℓ q n *
            (ν.supNorm : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (mul_nonneg haux htn)) hsup
      _ = auxWeight 𝒢.big ν.C r * (ν.supNorm : ℝ) *
            (targetNorm 𝒢 ℓ ν.C * damping 𝔭 𝒢 J ℓ q n) := by
          ring
  · rw [physCoef_eq_zero_of_not hc, norm_zero]
    exact mul_nonneg (mul_nonneg haux hsup) (sharedWeight_nonneg 𝔭 𝒢 hq ν.C n x' x)

/-! ### The sum over the lists with prescribed shared labels -/

/-- **The product over the groups of (eq:physical-count-bound)** [S-02:0143–0153]: for every
position `p` and every list `a`, the lists `b` which are physical at `p` and have the shared
labels of `a`, weighted by `∏_g V_g^{-t_g}` and by the damping at `p`, have total weight at most
`∏_g groupConst v₋ q T`, provided every group has mass `V_g ≥ v₋ > 0` and at most `T` unshared
slots. -/
theorem sum_sharedWeight_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (𝔭 : PosModel) (𝒢 : GroupFamily S B) {q vMinus : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hv : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g)) {J ℓ T : ℕ} (hT : 0 < T)
    (hℓT : ℓ ≤ T) (C : B → Finset (Fin J)) (hC : ∀ g, ℓ + (C g).card ≤ T) (p : 𝔭.Pos)
    (a : Lists 𝒢 J ℓ) :
    ∑ b : Lists 𝒢 J ℓ, sharedWeight 𝔭 𝒢 q C p a b ≤
      (∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T := by
  have hW : 0 ≤ targetNorm 𝒢 ℓ C * damping 𝔭 𝒢 J ℓ q p :=
    mul_nonneg (targetNorm_nonneg 𝒢 ℓ C) (damping_pos 𝔭 𝒢 J ℓ hq0 p).le
  have hmem : ∀ b : Lists 𝒢 J ℓ,
      IsPhys 𝔭 p b ∧ SharedSmall a.1 b.1 ∧ SharedBig C a.2 b.2 →
      b ∈ (Fintype.piFinset fun g : S =>
            validSet (fun r => 𝔭.hit r p) (∅ : Finset (Fin J)) (a.1 g)) ×ˢ
          (Fintype.piFinset fun g : B => validSet (fun r => 𝔭.hit r p) (C g) (a.2 g)) := by
    intro b hb
    refine Finset.mem_product.mpr
      ⟨Fintype.mem_piFinset.mpr fun g => mem_validSet.mpr ?_,
        Fintype.mem_piFinset.mpr fun g => mem_validSet.mpr ?_⟩
    · exact ⟨hb.1.1 g, fun s => hb.1.2.2.1 g s, fun i _ => hb.2.1 g i⟩
    · exact ⟨hb.1.2.1 g, fun s => hb.1.2.2.2 g s, fun i hi => hb.2.2 g i hi⟩
  have h1 : ∑ b : Lists 𝒢 J ℓ, sharedWeight 𝔭 𝒢 q C p a b =
      ∑ b ∈ (Fintype.piFinset fun g : S =>
            validSet (fun r => 𝔭.hit r p) (∅ : Finset (Fin J)) (a.1 g)) ×ˢ
          (Fintype.piFinset fun g : B => validSet (fun r => 𝔭.hit r p) (C g) (a.2 g)),
        sharedWeight 𝔭 𝒢 q C p a b := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_).symm
    unfold sharedWeight
    exact if_neg fun hc => hb (hmem b hc)
  have h2 : ∑ b ∈ (Fintype.piFinset fun g : S =>
            validSet (fun r => 𝔭.hit r p) (∅ : Finset (Fin J)) (a.1 g)) ×ˢ
          (Fintype.piFinset fun g : B => validSet (fun r => 𝔭.hit r p) (C g) (a.2 g)),
        sharedWeight 𝔭 𝒢 q C p a b ≤
      ((Fintype.piFinset fun g : S =>
            validSet (fun r => 𝔭.hit r p) (∅ : Finset (Fin J)) (a.1 g)) ×ˢ
          (Fintype.piFinset fun g : B =>
            validSet (fun r => 𝔭.hit r p) (C g) (a.2 g))).card •
        (targetNorm 𝒢 ℓ C * damping 𝔭 𝒢 J ℓ q p) := by
    refine Finset.sum_le_card_nsmul _ _ _ fun b _ => ?_
    unfold sharedWeight
    split_ifs
    · exact le_rfl
    · exact hW
  have hcard : ((Fintype.piFinset fun g : S =>
            validSet (fun r => 𝔭.hit r p) (∅ : Finset (Fin J)) (a.1 g)) ×ˢ
          (Fintype.piFinset fun g : B =>
            validSet (fun r => 𝔭.hit r p) (C g) (a.2 g))).card =
      (∏ g : S, (validSet (fun r => 𝔭.hit r p) (∅ : Finset (Fin J)) (a.1 g)).card) *
        ∏ g : B, (validSet (fun r => 𝔭.hit r p) (C g) (a.2 g)).card := by
    rw [Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset]
  have h3 : ((Fintype.piFinset fun g : S =>
            validSet (fun r => 𝔭.hit r p) (∅ : Finset (Fin J)) (a.1 g)) ×ˢ
          (Fintype.piFinset fun g : B =>
            validSet (fun r => 𝔭.hit r p) (C g) (a.2 g))).card •
        (targetNorm 𝒢 ℓ C * damping 𝔭 𝒢 J ℓ q p) =
      (∏ g : S, (((validSet (fun r => 𝔭.hit r p) (∅ : Finset (Fin J)) (a.1 g)).card : ℝ) *
          (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹ *
          q ^ ((((countHits (fun r => 𝔭.hit r p) (𝒢.small g) : ℕ) : ℝ) -
            ((J + ℓ : ℕ) : ℝ)) / 2))) *
        ∏ g : B, (((validSet (fun r => 𝔭.hit r p) (C g) (a.2 g)).card : ℝ) *
          (Graph.primeGroupReciprocalMass (𝒢.big g) ^ (ℓ + (C g).card))⁻¹ *
          q ^ ((((countHits (fun r => 𝔭.hit r p) (𝒢.big g) : ℕ) : ℝ) -
            ((J + ℓ : ℕ) : ℝ)) / 2)) := by
    rw [hcard, nsmul_eq_mul, damping_eq_prod 𝔭 𝒢 J ℓ hq0 p, Nat.cast_mul, Nat.cast_prod,
      Nat.cast_prod]
    unfold targetNorm
    simp only [Finset.prod_mul_distrib]
    ring
  refine (le_of_eq h1).trans (h2.trans ((le_of_eq h3).trans ?_))
  refine mul_le_mul (Finset.prod_le_prod (fun g _ => ?_) (fun g _ => ?_))
    (Finset.prod_le_prod (fun g _ => ?_) (fun g _ => ?_)) (Finset.prod_nonneg fun g _ => ?_)
    (Finset.prod_nonneg fun _ _ => zero_le_one.trans (one_le_groupConst vMinus q T))
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr (pow_nonneg (reciprocalMass_nonneg _) _))) (Real.rpow_nonneg hq0.le _)
  · exact group_factor_le hv (hVS g) hq0 hq1 hT (fun r => 𝔭.hit r p) (∅ : Finset (Fin J))
      (a.1 g) (by simp) hℓT
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr (pow_nonneg (reciprocalMass_nonneg _) _))) (Real.rpow_nonneg hq0.le _)
  · exact group_factor_le hv (hVB g) hq0 hq1 hT (fun r => 𝔭.hit r p) (C g) (a.2 g) rfl (hC g)
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr (pow_nonneg (reciprocalMass_nonneg _) _))) (Real.rpow_nonneg hq0.le _)

/-! ### One row transition summed over the lists of the other endpoint -/

/-- **Rows**, for fixed auxiliary labels: the sum over the target lists of the moduli of the
coefficients. -/
theorem sum_norm_physCoef_row_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (𝔭 : PosModel) (𝒢 : GroupFamily S B) {q vMinus : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hv : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g)) {J ℓ T : ℕ} (hT : 0 < T)
    (hℓT : ℓ ≤ T) (ν : Pattern 𝒢.big J ℓ) (hC : ∀ g, ℓ + (ν.C g).card ≤ T) (k : ℤ) (ζ : ℝ)
    (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C) :
    ∑ x' : Lists 𝒢 J ℓ, ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖ ≤
      auxWeight 𝒢.big ν.C r * ((ν.supNorm : ℝ) *
        ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T)) := by
  have haux : 0 ≤ auxWeight 𝒢.big ν.C r := auxWeight_nonneg 𝒢.big ν.C r
  have hsup : (0 : ℝ) ≤ (ν.supNorm : ℝ) := NNReal.coe_nonneg _
  calc ∑ x' : Lists 𝒢 J ℓ, ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖
      ≤ ∑ x' : Lists 𝒢 J ℓ, auxWeight 𝒢.big ν.C r * (ν.supNorm : ℝ) *
          sharedWeight 𝔭 𝒢 q ν.C (𝔭.shift (k * dil ν.C x r) n) x x' :=
        Finset.sum_le_sum fun x' _ => norm_physCoef_le_row 𝔭 𝒢 hq0 hq1.le ν k ζ n x r x'
    _ = auxWeight 𝒢.big ν.C r * (ν.supNorm : ℝ) *
          ∑ x' : Lists 𝒢 J ℓ, sharedWeight 𝔭 𝒢 q ν.C (𝔭.shift (k * dil ν.C x r) n) x x' :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ auxWeight 𝒢.big ν.C r * (ν.supNorm : ℝ) *
          ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T) :=
        mul_le_mul_of_nonneg_left
          (sum_sharedWeight_le 𝔭 𝒢 hq0 hq1 hv hVS hVB hT hℓT ν.C hC _ x)
          (mul_nonneg haux hsup)
    _ = auxWeight 𝒢.big ν.C r * ((ν.supNorm : ℝ) *
          ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T)) :=
        mul_assoc _ _ _

/-- **Columns**, for fixed auxiliary labels: the sum over the source lists of the moduli of the
coefficients, at an arbitrary source position `n`. -/
theorem sum_norm_physCoef_col_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (𝔭 : PosModel) (𝒢 : GroupFamily S B) {q vMinus : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hv : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g)) {J ℓ T : ℕ} (hT : 0 < T)
    (hℓT : ℓ ≤ T) (ν : Pattern 𝒢.big J ℓ) (hC : ∀ g, ℓ + (ν.C g).card ≤ T) (k : ℤ) (ζ : ℝ)
    (n : 𝔭.Pos) (x' : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C) :
    ∑ x : Lists 𝒢 J ℓ, ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖ ≤
      auxWeight 𝒢.big ν.C r * ((ν.supNorm : ℝ) *
        ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T)) := by
  have haux : 0 ≤ auxWeight 𝒢.big ν.C r := auxWeight_nonneg 𝒢.big ν.C r
  have hsup : (0 : ℝ) ≤ (ν.supNorm : ℝ) := NNReal.coe_nonneg _
  calc ∑ x : Lists 𝒢 J ℓ, ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖
      ≤ ∑ x : Lists 𝒢 J ℓ, auxWeight 𝒢.big ν.C r * (ν.supNorm : ℝ) *
          sharedWeight 𝔭 𝒢 q ν.C n x' x :=
        Finset.sum_le_sum fun x _ => norm_physCoef_le_col 𝔭 𝒢 hq0 hq1.le ν k ζ n x r x'
    _ = auxWeight 𝒢.big ν.C r * (ν.supNorm : ℝ) *
          ∑ x : Lists 𝒢 J ℓ, sharedWeight 𝔭 𝒢 q ν.C n x' x :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ auxWeight 𝒢.big ν.C r * (ν.supNorm : ℝ) *
          ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T) :=
        mul_le_mul_of_nonneg_left
          (sum_sharedWeight_le 𝔭 𝒢 hq0 hq1 hv hVS hVB hT hℓT ν.C hC n x')
          (mul_nonneg haux hsup)
    _ = auxWeight 𝒢.big ν.C r * ((ν.supNorm : ℝ) *
          ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T)) :=
        mul_assoc _ _ _

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Schur
