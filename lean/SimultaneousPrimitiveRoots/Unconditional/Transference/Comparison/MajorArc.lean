module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.MajorArcNumerics
public import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Denominators at most `Q`

Source: `verification/stage7-sources/S-03.tex`, lines 339–412 (`[S-03:0339–0412]`).

`majorArcBound_of : ScaleLowerBound → CharacterReproduction → KernelCostsLemma →
RationalPhaseExpansion → MajorArcBound`.

"Suppose `r ≤ Q`. All products under consideration are units modulo `r`. … First remove discarded
cells. … On retained cells, write the remaining scalar multiplier in the log variable as
`M(v) = exp(iζv) e(β e^v)`. … (eq:ideal-cell-costs) bounds the error after integration in
`D_A, D_B` by `O(Q⁴ h (S + L^{C₄}))`. … Applying the formula on both sides and then
(eq:ideal-rational-expansion) reproduces `e(u X_A X_B / r)` with pointwise error
`O(Q^{5/2} ξ⁻¹ L^{-D_*})`. … Together, (eq:ideal-discarded-mass), (eq:ideal-log-error),
(eq:ideal-major-character-error) establish the desired comparison on a pair of dyads."

* `Major.slow_variation_le` — the variation of `M` over a pair of matched cells.
* `Major.retained_gap_le` — the pointwise defect on a retained pair.
* `majorArcBound_of` — the estimate on one pair of dyads.

The thresholds for `x`: those of `CharacterReproduction` (with the precision
`L^{-(B₀ + q_*/2 + 1)}`), of the kernel costs and of `ScaleLowerBound` (exponent `q_* + 1`), and
`L ≥ max(1032, 32 max(C_cell, 1))`. Each of the four errors (two discarded masses, the log error
and the character error) is at most `L^{-B₀}/4`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Major

section Retained

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B] {J : ℕ}

/-- **The variation of the multiplier `M` on the support of the two kernels** [S-03:0376–0389]:
"Both matched log products differ by less than `h`, so the product-log variable differs by less
than `2h`", and the products are at most `4Z`. -/
theorem slow_variation_le (𝔊 : PrimeGroups P x S B) (A Bs : B → Finset (Fin J))
    {Q h ξ Lm Z Sr ζ β : ℝ} {r : ℕ} (hh : 0 < h) (hh1 : 2 * h ≤ 1) (hr : 0 < r)
    (hζ : |ζ| ≤ Lm) (hS : Sr ≤ Lm) (hS0 : 0 ≤ Sr) (hLm : 0 ≤ Lm)
    (hβZ : |β| * Z ≤ 2 * Sr / (r : ℝ)) {dA xA : AuxList 𝔊.big A} {dB xB : AuxList 𝔊.big Bs}
    (hXZ : ((tupleProd A xA * tupleProd Bs xB : ℕ) : ℝ) ≤ 4 * Z)
    (hKA : cellKernel 𝔊.big A Q h ξ (tupleProd A dA) (tupleProd A xA) ≠ 0)
    (hKB : cellKernel 𝔊.big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) ≠ 0) :
    ‖slowPhase ζ β (tupleProd A dA * tupleProd Bs dB) -
      slowPhase ζ β (tupleProd A xA * tupleProd Bs xB)‖ ≤ 258 * h * Lm := by
  have hcA : logCell h (tupleProd A dA) = logCell h (tupleProd A xA) := by
    by_contra hne
    exact hKA (cellKernel_eq_zero_of_logCell_ne hne)
  have hcB : logCell h (tupleProd Bs dB) = logCell h (tupleProd Bs xB) := by
    by_contra hne
    exact hKB (cellKernel_eq_zero_of_logCell_ne hne)
  obtain ⟨a1, a2⟩ := abs_lt.mp (abs_log_sub_lt hh hcA)
  obtain ⟨b1, b2⟩ := abs_lt.mp (abs_log_sub_lt hh hcB)
  have hPdA : (0 : ℝ) < ((tupleProd A dA : ℕ) : ℝ) := by
    exact_mod_cast tupleProd_pos 𝔊 A dA
  have hPdB : (0 : ℝ) < ((tupleProd Bs dB : ℕ) : ℝ) := by
    exact_mod_cast tupleProd_pos 𝔊 Bs dB
  have hPxA : (0 : ℝ) < ((tupleProd A xA : ℕ) : ℝ) := by
    exact_mod_cast tupleProd_pos 𝔊 A xA
  have hPxB : (0 : ℝ) < ((tupleProd Bs xB : ℕ) : ℝ) := by
    exact_mod_cast tupleProd_pos 𝔊 Bs xB
  have hlog : |Real.log (((tupleProd A dA * tupleProd Bs dB : ℕ)) : ℝ) -
      Real.log (((tupleProd A xA * tupleProd Bs xB : ℕ)) : ℝ)| ≤ 2 * h := by
    rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul hPdA.ne' hPdB.ne',
      Real.log_mul hPxA.ne' hPxB.ne', abs_le]
    constructor
    · linarith only [a1, b1]
    · linarith only [a2, b2]
  exact (norm_slowPhase_sub_le ζ β
    (Nat.mul_pos (tupleProd_pos 𝔊 A dA) (tupleProd_pos 𝔊 Bs dB))
    (Nat.mul_pos (tupleProd_pos 𝔊 A xA) (tupleProd_pos 𝔊 Bs xB)) hh1 hlog).trans
    (slow_bound hr hh.le hζ hS hS0 hLm hβZ hXZ)

/-- **The pointwise defect on a retained pair** [S-03:0368–0412]: the multiplier `M` is constant
up to `δ` on the support of the two kernels (eq:ideal-log-error), and the kernels reproduce the
characters modulo `r` up to `ε_r` (eq:ideal-character-reproduction), so that
(eq:ideal-rational-expansion) reproduces `e(u X_A X_B / r)` (eq:ideal-major-character-error). -/
theorem retained_gap_le (𝔊 : PrimeGroups P x S B) (A Bs : B → Finset (Fin J)) (Q h ξ : ℝ)
    {α β : ℝ} {u : ℤ} {r : ℕ} (hα : α = (u : ℝ) / (r : ℝ) + β) (ζ : ℝ)
    (hcopA : ∀ d : AuxList 𝔊.big A, Nat.Coprime (tupleProd A d) r)
    (hcopB : ∀ d : AuxList 𝔊.big Bs, Nat.Coprime (tupleProd Bs d) r)
    (c : DirichletCharacter ℂ r → ℂ) {C₁ N δ εr : ℝ}
    (hc : ∑ ψ : DirichletCharacter ℂ r, ‖c ψ‖ ≤ C₁)
    (hexpand : ∀ v : ℕ, Nat.Coprime v r →
      expUnit ((u : ℝ) * (v : ℝ) / (r : ℝ)) =
        ∑ ψ : DirichletCharacter ℂ r, c ψ * ψ (v : ZMod r))
    (hεr0 : 0 ≤ εr) (hεr1 : εr ≤ 1) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (xA : AuxList 𝔊.big A) (xB : AuxList 𝔊.big Bs)
    (hcostA : ∑ t : AuxList 𝔊.big A, auxWeight 𝔊.big A t *
      ‖cellKernel 𝔊.big A Q h ξ (tupleProd A t) (tupleProd A xA)‖ ≤ N)
    (hcostB : ∑ t : AuxList 𝔊.big Bs, auxWeight 𝔊.big Bs t *
      ‖cellKernel 𝔊.big Bs Q h ξ (tupleProd Bs t) (tupleProd Bs xB)‖ ≤ N)
    (hM : ∀ (dA : AuxList 𝔊.big A) (dB : AuxList 𝔊.big Bs),
      cellKernel 𝔊.big A Q h ξ (tupleProd A dA) (tupleProd A xA) ≠ 0 →
      cellKernel 𝔊.big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) ≠ 0 →
      ‖slowPhase ζ β (tupleProd A dA * tupleProd Bs dB) -
        slowPhase ζ β (tupleProd A xA * tupleProd Bs xB)‖ ≤ δ)
    (hrepA : ∀ ψ : DirichletCharacter ℂ r,
      ‖(∑ d : AuxList 𝔊.big A, (auxWeight 𝔊.big A d : ℂ) *
          (cellKernel 𝔊.big A Q h ξ (tupleProd A d) (tupleProd A xA) *
            ψ ((tupleProd A d : ℕ) : ZMod r))) - ψ ((tupleProd A xA : ℕ) : ZMod r)‖ ≤ εr)
    (hrepB : ∀ ψ : DirichletCharacter ℂ r,
      ‖(∑ d : AuxList 𝔊.big Bs, (auxWeight 𝔊.big Bs d : ℂ) *
          (cellKernel 𝔊.big Bs Q h ξ (tupleProd Bs d) (tupleProd Bs xB) *
            ψ ((tupleProd Bs d : ℕ) : ZMod r))) - ψ ((tupleProd Bs xB : ℕ) : ZMod r)‖ ≤ εr) :
    ‖gap 𝔊.big A Bs Q h ξ α ζ xA xB‖ ≤ δ * (N * N) + C₁ * (3 * εr) := by
  -- (eq:ideal-rational-expansion) on the products, which are units modulo `r`
  have he : ∀ (dA : AuxList 𝔊.big A) (dB : AuxList 𝔊.big Bs),
      expUnit ((u : ℝ) * ((tupleProd A dA * tupleProd Bs dB : ℕ) : ℝ) / (r : ℝ)) =
        ∑ ψ : DirichletCharacter ℂ r, c ψ * (ψ ((tupleProd A dA : ℕ) : ZMod r) *
          ψ ((tupleProd Bs dB : ℕ) : ZMod r)) := by
    intro dA dB
    rw [hexpand _ (Nat.Coprime.mul_left (hcopA dA) (hcopB dB))]
    exact Finset.sum_congr rfl fun ψ _ => by rw [Nat.cast_mul, map_mul]
  have hab := abstract_gap (auxWeight 𝔊.big A) (auxWeight 𝔊.big Bs) (tupleWeight_nonneg 𝔊 A)
    (tupleWeight_nonneg 𝔊 Bs)
    (fun dA : AuxList 𝔊.big A => cellKernel 𝔊.big A Q h ξ (tupleProd A dA) (tupleProd A xA))
    (fun dB : AuxList 𝔊.big Bs =>
      cellKernel 𝔊.big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB))
    (fun (dA : AuxList 𝔊.big A) (dB : AuxList 𝔊.big Bs) =>
      slowPhase ζ β (tupleProd A dA * tupleProd Bs dB))
    (slowPhase ζ β (tupleProd A xA * tupleProd Bs xB))
    (fun (dA : AuxList 𝔊.big A) (dB : AuxList 𝔊.big Bs) =>
      expUnit ((u : ℝ) * ((tupleProd A dA * tupleProd Bs dB : ℕ) : ℝ) / (r : ℝ)))
    (expUnit ((u : ℝ) * ((tupleProd A xA * tupleProd Bs xB : ℕ) : ℝ) / (r : ℝ))) c
    (fun (ψ : DirichletCharacter ℂ r) (dA : AuxList 𝔊.big A) =>
      ψ ((tupleProd A dA : ℕ) : ZMod r))
    (fun (ψ : DirichletCharacter ℂ r) (dB : AuxList 𝔊.big Bs) =>
      ψ ((tupleProd Bs dB : ℕ) : ZMod r))
    (fun ψ : DirichletCharacter ℂ r => ψ ((tupleProd A xA : ℕ) : ZMod r))
    (fun ψ : DirichletCharacter ℂ r => ψ ((tupleProd Bs xB : ℕ) : ZMod r))
    he (he xA xB) (fun _ _ => le_of_eq (norm_expUnit _)) (norm_slowPhase_le ζ β _) hc
    (fun ψ => ψ.norm_le_one _) (fun ψ => ψ.norm_le_one _) hεr0 hεr1 hδ hN hcostA hcostB hM
    hrepA hrepB
  have hgap : gap 𝔊.big A Bs Q h ξ α ζ xA xB =
      slowPhase ζ β (tupleProd A xA * tupleProd Bs xB) *
          expUnit ((u : ℝ) * ((tupleProd A xA * tupleProd Bs xB : ℕ) : ℝ) / (r : ℝ)) -
        ∑ dA : AuxList 𝔊.big A, ∑ dB : AuxList 𝔊.big Bs,
          ((auxWeight 𝔊.big A dA * auxWeight 𝔊.big Bs dB : ℝ) : ℂ) *
            (cellKernel 𝔊.big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
              cellKernel 𝔊.big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
              (slowPhase ζ β (tupleProd A dA * tupleProd Bs dB) *
                expUnit ((u : ℝ) * ((tupleProd A dA * tupleProd Bs dB : ℕ) : ℝ) /
                  (r : ℝ)))) := by
    unfold gap
    rw [dilPhase_eq_slow hα ζ (tupleProd A xA * tupleProd Bs xB)]
    refine congrArg (fun z => slowPhase ζ β (tupleProd A xA * tupleProd Bs xB) *
      expUnit ((u : ℝ) * ((tupleProd A xA * tupleProd Bs xB : ℕ) : ℝ) / (r : ℝ)) - z)
      (Finset.sum_congr rfl fun dA _ => Finset.sum_congr rfl fun dB _ => ?_)
    rw [dilPhase_eq_slow hα ζ (tupleProd A dA * tupleProd Bs dB)]
  rw [hgap]
  exact hab

end Retained

end Major

/-- **Denominators at most `Q`** [S-03:0339–0412]. -/
theorem majorArcBound_of (hscale : ScaleLowerBound) (hrepS : CharacterReproduction)
    (hcosts : KernelCostsLemma) (hexp : RationalPhaseExpansion) : MajorArcBound := by
  intro P m B₀ C₄ qs ss hs xs hB₀ hC₄ hqs hhs hxs
  have hd := d_pos P
  have hmaxC : C₄ ≤ max ss C₄ := le_max_right _ _
  have hmaxS : ss ≤ max ss C₄ := le_max_left _ _
  have hs1 : 1 ≤ hs := by linarith only [hhs, hqs, hmaxC, hC₄, hB₀]
  have hs0 : 0 ≤ hs := by linarith only [hs1]
  have hxs0 : 0 ≤ xs := by linarith only [hxs, hB₀, hd, hs0]
  obtain ⟨x₁, hRep⟩ := hrepS P m qs hs xs (B₀ + qs / 2 + 1) hqs hs0 hxs0
  obtain ⟨Ccell, x₂, hCost⟩ := hcosts P m qs hs xs hqs hs0 hxs0
  obtain ⟨x₃, hSC⟩ := hscale P (qs + 1)
  refine ⟨max (max x₁ x₂) (max x₃ (Real.exp (max 1032 (32 * max Ccell 1)))), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 hint J A Bs hA hBs hAm hBm a b f g hf hg α ζ β u r hζ hdata hrQ
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx₂ : x₂ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx₃ : x₃ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxe : Real.exp (max 1032 (32 * max Ccell 1)) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hLbig : max 1032 (32 * max Ccell 1) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL1032 : 1032 ≤ Real.log x := (le_max_left _ _).trans hLbig
  have hLC : 32 * max Ccell 1 ≤ Real.log x := (le_max_right _ _).trans hLbig
  have hL0 : 0 < Real.log x := by linarith only [hL1032]
  have hL1 : 1 ≤ Real.log x := by linarith only [hL1032]
  have hL2 : 2 ≤ Real.log x := by linarith only [hL1032]
  have hQ0 : 0 < Real.log x ^ qs := Real.rpow_pos_of_pos hL0 _
  have hh0 : 0 < Real.log x ^ (-hs) := Real.rpow_pos_of_pos hL0 _
  have hξ0 : 0 < Real.log x ^ (-xs) := Real.rpow_pos_of_pos hL0 _
  have hhalf : Real.log x ^ (-hs) ≤ 1 / 2 := by
    have h1 : Real.log x ^ (-hs) ≤ Real.log x ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hs1])
    have h2 : Real.log x ^ (-(1 : ℝ)) = (Real.log x)⁻¹ := Real.rpow_neg_one _
    have h3 : (Real.log x)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hL2
    have h4 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    exact h1.trans ((le_of_eq h2).trans (h3.trans (le_of_eq h4)))
  have hh1 : 2 * Real.log x ^ (-hs) ≤ 1 := by linarith only [hhalf]
  have hLm0 : 0 ≤ Real.log x ^ (max ss C₄) := Real.rpow_nonneg hL0.le _
  have hS0 : 0 ≤ Real.log x ^ ss := Real.rpow_nonneg hL0.le _
  have hζ' : |ζ| ≤ Real.log x ^ (max ss C₄) :=
    hζ.trans (Real.rpow_le_rpow_of_exponent_le hL1 hmaxC)
  have hSm : Real.log x ^ ss ≤ Real.log x ^ (max ss C₄) :=
    Real.rpow_le_rpow_of_exponent_le hL1 hmaxS
  have hX : 0 ≤ tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g :=
    mul_nonneg (wNorm_nonneg _ _) (wNorm_nonneg _ _)
  obtain ⟨hr, -, hα, -, -, hβZ⟩ := hdata
  -- "all products under consideration are units modulo `r`"
  have hbig : ∀ (g' : B) (p : ℕ), p ∈ 𝔊.big g' → Real.log x ^ qs < (p : ℝ) := by
    intro g' p hp
    have h1 := (hSC x hx₃ S B 𝔊).1 g' p hp
    rw [Real.rpow_add_one hL0.ne'] at h1
    have h2 : Real.log x ^ qs * 2 ≤ Real.log x ^ qs * Real.log x :=
      mul_le_mul_of_nonneg_left hL2 hQ0.le
    linarith only [h1, h2, hQ0]
  have hcopP : ∀ (g' : B) (p : ℕ), p ∈ 𝔊.big g' → Nat.Coprime p r := by
    intro g' p hp
    have hlt : r < p := by
      have h1 : (r : ℝ) < (p : ℝ) := lt_of_le_of_lt hrQ (hbig g' p hp)
      exact_mod_cast h1
    exact ((𝔊.prime_big g' p hp).coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hr hlt)
  have hcopA : ∀ d : AuxList 𝔊.big A, Nat.Coprime (tupleProd A d) r := by
    intro d
    unfold tupleProd
    exact Nat.coprime_prod_left_iff.mpr fun g' _ =>
      Nat.coprime_prod_left_iff.mpr fun i _ => hcopP g' (d g' i) (d g' i).2
  have hcopB : ∀ d : AuxList 𝔊.big Bs, Nat.Coprime (tupleProd Bs d) r := by
    intro d
    unfold tupleProd
    exact Nat.coprime_prod_left_iff.mpr fun g' _ =>
      Nat.coprime_prod_left_iff.mpr fun i _ => hcopP g' (d g' i) (d g' i).2
  -- (eq:ideal-cell-costs) and (eq:ideal-rational-expansion)
  obtain ⟨-, hcntA, -, hcostA⟩ := hCost x hx₂ S B 𝔊 hint J A hA hAm
  obtain ⟨-, hcntB, -, hcostB⟩ := hCost x hx₂ S B 𝔊 hint J Bs hBs hBm
  obtain ⟨c, hc, hexpand⟩ := hexp r u hr
  have hC₁ : Real.sqrt (r.totient : ℝ) ≤ Real.log x ^ (qs / 2) := by
    have h1 : ((r.totient : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.totient_le r
    have h2 : Real.sqrt (Real.log x ^ qs) = Real.log x ^ (qs / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le]
      congr 1
      ring
    exact (Real.sqrt_le_sqrt (h1.trans hrQ)).trans (le_of_eq h2)
  -- the errors
  have hεr0 : 0 ≤ Real.log x ^ (-(B₀ + qs / 2 + 1)) := Real.rpow_nonneg hL0.le _
  have hεr1 : Real.log x ^ (-(B₀ + qs / 2 + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hB₀, hqs])
  have hN0 : 0 ≤ (Real.log x ^ qs) ^ 2 := sq_nonneg _
  have hδ0 : 0 ≤ 258 * Real.log x ^ (-hs) * Real.log x ^ (max ss C₄) :=
    mul_nonneg (mul_nonneg (by norm_num) hh0.le) hLm0
  have hε0 : 0 ≤ 258 * Real.log x ^ (-hs) * Real.log x ^ (max ss C₄) *
      ((Real.log x ^ qs) ^ 2 * (Real.log x ^ qs) ^ 2) +
      Real.log x ^ (qs / 2) * (3 * Real.log x ^ (-(B₀ + qs / 2 + 1))) :=
    add_nonneg (mul_nonneg hδ0 (mul_nonneg hN0 hN0))
      (mul_nonneg (Real.rpow_nonneg hL0.le _) (mul_nonneg (by norm_num) hεr0))
  -- the indicators of the discarded cells
  have hind : ∀ c' : ℝ, 0 ≤ (if c' < Real.log x ^ (-xs) then (1 : ℝ) else 0) ∧
      (if c' < Real.log x ^ (-xs) then (1 : ℝ) else 0) ≤ 1 := by
    intro c'
    by_cases hc' : c' < Real.log x ^ (-xs)
    · rw [if_pos hc']
      exact ⟨zero_le_one, le_rfl⟩
    · rw [if_neg hc']
      exact ⟨le_rfl, zero_le_one⟩
  -- the pointwise defect
  have hΔ : ∀ (xA : AuxList 𝔊.big A) (xB : AuxList 𝔊.big Bs), g xA ≠ 0 → f xB ≠ 0 →
      ‖Major.gap 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs)) α ζ
        xA xB‖ ≤
      (if cellMass 𝔊.big A (Real.log x ^ (-hs))
          (logCell (Real.log x ^ (-hs)) (tupleProd A xA)) < Real.log x ^ (-xs)
        then (1 : ℝ) else 0) +
      (if cellMass 𝔊.big Bs (Real.log x ^ (-hs))
          (logCell (Real.log x ^ (-hs)) (tupleProd Bs xB)) < Real.log x ^ (-xs)
        then (1 : ℝ) else 0) +
      (258 * Real.log x ^ (-hs) * Real.log x ^ (max ss C₄) *
        ((Real.log x ^ qs) ^ 2 * (Real.log x ^ qs) ^ 2) +
        Real.log x ^ (qs / 2) * (3 * Real.log x ^ (-(B₀ + qs / 2 + 1)))) := by
    intro xA xB hgx hfx
    have hiA := hind (cellMass 𝔊.big A (Real.log x ^ (-hs))
      (logCell (Real.log x ^ (-hs)) (tupleProd A xA)))
    have hiB := hind (cellMass 𝔊.big Bs (Real.log x ^ (-hs))
      (logCell (Real.log x ^ (-hs)) (tupleProd Bs xB)))
    have hone := Major.norm_dilPhase_le_one ζ α (tupleProd A xA * tupleProd Bs xB)
    by_cases hdA : cellMass 𝔊.big A (Real.log x ^ (-hs))
        (logCell (Real.log x ^ (-hs)) (tupleProd A xA)) < Real.log x ^ (-xs)
    · -- "the comparison term is zero on this event"
      rw [Major.gap_eq_of_left_zero 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs))
        (Real.log x ^ (-xs)) α ζ xA xB
        (fun dA => Major.cellKernel_eq_zero_of_discarded hdA), if_pos hdA]
      linarith only [hone, hiB.1, hε0]
    by_cases hdB : cellMass 𝔊.big Bs (Real.log x ^ (-hs))
        (logCell (Real.log x ^ (-hs)) (tupleProd Bs xB)) < Real.log x ^ (-xs)
    · rw [Major.gap_eq_of_right_zero 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs))
        (Real.log x ^ (-xs)) α ζ xA xB
        (fun dB => Major.cellKernel_eq_zero_of_discarded hdB), if_pos hdB]
      linarith only [hone, hiA.1, hε0]
    -- both cells are retained
    rw [if_neg hdA, if_neg hdB, zero_add, zero_add]
    obtain ⟨-, hxA2⟩ := Minor.dyad_bounds 𝔊 A (hg xA hgx)
    obtain ⟨-, hxB2⟩ := Minor.dyad_bounds 𝔊 Bs (hf xB hfx)
    have hPxB : (0 : ℝ) ≤ ((tupleProd Bs xB : ℕ) : ℝ) := Nat.cast_nonneg _
    have hXZ : (((tupleProd A xA * tupleProd Bs xB : ℕ)) : ℝ) ≤
        4 * ((2 : ℝ) ^ a * (2 : ℝ) ^ b) := by
      rw [Nat.cast_mul]
      exact (mul_le_mul hxA2.le hxB2.le hPxB
        (mul_nonneg zero_le_two (pow_nonneg zero_le_two a))).trans (le_of_eq (by ring))
    have hret := Major.retained_gap_le 𝔊 A Bs (Real.log x ^ qs) (Real.log x ^ (-hs))
      (Real.log x ^ (-xs)) hα ζ hcopA hcopB c hc hexpand hεr0 hεr1 hδ0 hN0 xA xB
      (hcostA (tupleProd A xA)) (hcostB (tupleProd Bs xB))
      (fun dA dB hKA hKB => Major.slow_variation_le 𝔊 A Bs hh0 hh1 hr hζ' hSm hS0 hLm0 hβZ
        hXZ hKA hKB)
      (fun ψ => hRep x hx₁ S B 𝔊 hint J A hA hAm r ψ hr hrQ xA (not_lt.mp hdA))
      (fun ψ => hRep x hx₁ S B 𝔊 hint J Bs hBs hBm r ψ hr hrQ xB (not_lt.mp hdB))
    exact hret.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hC₁ (mul_nonneg (by norm_num) hεr0)))
  -- from the pointwise defect to the bilinear estimate
  have hmainb := Major.norm_sum_le_of_pointwise (auxWeight 𝔊.big A) (auxWeight 𝔊.big Bs)
    (tupleWeight_nonneg 𝔊 A) (tupleWeight_nonneg 𝔊 Bs) (sum_tupleWeight 𝔊 A)
    (sum_tupleWeight 𝔊 Bs) f g
    (fun xA xB => Major.gap 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs))
      (Real.log x ^ (-xs)) α ζ xA xB)
    (fun xA => if cellMass 𝔊.big A (Real.log x ^ (-hs))
      (logCell (Real.log x ^ (-hs)) (tupleProd A xA)) < Real.log x ^ (-xs) then (1 : ℝ) else 0)
    (fun xB => if cellMass 𝔊.big Bs (Real.log x ^ (-hs))
      (logCell (Real.log x ^ (-hs)) (tupleProd Bs xB)) < Real.log x ^ (-xs) then (1 : ℝ) else 0)
    (fun xA => hind _) (fun xB => hind _) hε0
    (Major.discarded_mass_le 𝔊 A (Real.log x ^ (-hs)) (Real.log x ^ (-xs)) hξ0.le)
    (Major.discarded_mass_le 𝔊 Bs (Real.log x ^ (-hs)) (Real.log x ^ (-xs)) hξ0.le) hΔ
  -- the four errors
  have hT0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  have hW0 : 0 ≤ 1 + Real.log x ^ P.d * Real.log (Real.log x) / Real.log x ^ (-hs) :=
    add_nonneg zero_le_one (div_nonneg (mul_nonneg (Real.rpow_nonneg hL0.le _) hT0) hh0.le)
  have hC2 : (1 : ℝ) ≤ max Ccell 1 := le_max_right _ _
  have hpA := Major.discarded_sqrt_le (B₀ := B₀) hLC hC2 hd hs0 hxs
    (hcntA.trans (mul_le_mul_of_nonneg_right (le_max_left Ccell 1) hW0))
  have hpB := Major.discarded_sqrt_le (B₀ := B₀) hLC hC2 hd hs0 hxs
    (hcntB.trans (mul_le_mul_of_nonneg_right (le_max_left Ccell 1) hW0))
  have he1 := Major.log_error_le (L := Real.log x) (qs := qs) hL1032 hhs
  have he2 := Major.char_error_le (L := Real.log x) (qs := qs) (B₀ := B₀)
    (by linarith only [hL1032] : (12 : ℝ) ≤ Real.log x)
  rw [Major.defect_eq_gap 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs))
    (Real.log x ^ (-xs)) (sum_tupleWeight 𝔊 A) (sum_tupleWeight 𝔊 Bs) f g α ζ]
  refine hmainb.trans (mul_le_mul_of_nonneg_right ?_ hX)
  linarith only [hpA, hpB, he1, he2]

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
