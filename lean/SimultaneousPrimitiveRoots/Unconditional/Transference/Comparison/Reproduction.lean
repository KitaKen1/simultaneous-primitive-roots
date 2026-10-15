module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.KernelNorm
public import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The reproduction formula (eq:ideal-character-reproduction)

Source: `verification/stage7-sources/S-03.tex`, lines 391–403 (`[S-03:0391–0403]`).

`characterReproduction_of : CharacterCell → PrimitiveInduction → CharacterReproduction`.

"For a character `ψ` in (eq:ideal-rational-expansion), the Gram calculation also gives the
following pointwise reproduction formula for retained `X`:
`E_D 𝒦_Λ(D, X) ψ(D) = ψ(X) + O_{D_*}(Q² ξ⁻¹ L^{-D_*})`. In fact, the summand corresponding to its
inducing primitive character is exactly `ψ(X)`: the diagonal conditional expectation is `1`. Each
other summand is bounded by (eq:ideal-character-cell) divided by the retained-cell mass. There are
at most `Q²` such summands."

* `Repro.term_eq` — the kernel against `ψ`, expanded over `𝒞_Q` on the cell of `X`.
* `Repro.core` — the summand of the inducing primitive character `χ₀` is `χ₀(X)`, because
  `|χ₀(D)| = 1` (the products are units modulo `r`: "all selected primes exceed `Q`"); the other
  summands are Gram entries on the cell of `X`.
* `characterReproduction_of` — with `D_* = E + 2 q_* + x_*`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Repro

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ}

/-- The kernel against a function `ψ = χ₀(P_Λ)`, expanded over `𝒞_Q` on the cell of `X`. -/
theorem term_eq (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ) (X : AuxList big Λ)
    (hX : ξ ≤ cellMass big Λ h (logCell h (tupleProd Λ X))) (ψ : AuxList big Λ → ℂ)
    (q₀ : Σ r : ℕ, DirichletCharacter ℂ r) (hψ : ∀ d, ψ d = Family.charFun Λ q₀ d)
    (d : AuxList big Λ) :
    ((auxWeight big Λ d : ℝ) : ℂ) *
        (cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ X) * ψ d) =
      ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
        ∑ q ∈ Family.charSet Q, Family.charFun Λ q X *
          (((Frame.cellWeight (auxWeight big Λ)
              (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
              (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
            (conj (Family.charFun Λ q d) * Family.charFun Λ q₀ d)) := by
  by_cases hd : logCell h (tupleProd Λ d) = logCell h (tupleProd Λ X)
  · have hcond : logCell h (tupleProd Λ d) = logCell h (tupleProd Λ X) ∧
        ξ ≤ cellMass big Λ h (logCell h (tupleProd Λ d)) := ⟨hd, by rw [hd]; exact hX⟩
    have e1 : cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ X) =
        ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
          ∑ q ∈ Family.charSet Q, conj (Family.charFun Λ q d) * Family.charFun Λ q X := by
      unfold cellKernel
      rw [if_pos hcond, hd, Family.primitiveCharSum_eq]
      rfl
    rw [e1, Frame.cellWeight_of_eq (w := auxWeight big Λ)
      (c := fun t : AuxList big Λ => logCell h (tupleProd Λ t)) (x := d) hd, hψ d]
    calc ((auxWeight big Λ d : ℝ) : ℂ) *
          (((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
            (∑ q ∈ Family.charSet Q, conj (Family.charFun Λ q d) * Family.charFun Λ q X) *
            Family.charFun Λ q₀ d)
        = ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
            ((∑ q ∈ Family.charSet Q, conj (Family.charFun Λ q d) * Family.charFun Λ q X) *
              (((auxWeight big Λ d : ℝ) : ℂ) * Family.charFun Λ q₀ d)) := by ring
      _ = ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
            ∑ q ∈ Family.charSet Q, conj (Family.charFun Λ q d) * Family.charFun Λ q X *
              (((auxWeight big Λ d : ℝ) : ℂ) * Family.charFun Λ q₀ d) := by
          rw [Finset.sum_mul]
      _ = ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
            ∑ q ∈ Family.charSet Q, Family.charFun Λ q X *
              (((auxWeight big Λ d : ℝ) : ℂ) *
                (conj (Family.charFun Λ q d) * Family.charFun Λ q₀ d)) :=
          congrArg (fun z => ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ * z)
            (Finset.sum_congr rfl fun q _ => by ring)
  · have hcond : ¬(logCell h (tupleProd Λ d) = logCell h (tupleProd Λ X) ∧
        ξ ≤ cellMass big Λ h (logCell h (tupleProd Λ d))) := fun hc => hd hc.1
    have e1 : cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ X) = 0 := by
      unfold cellKernel
      exact if_neg hcond
    rw [e1, zero_mul, mul_zero, Frame.cellWeight_of_ne (w := auxWeight big Λ)
      (c := fun t : AuxList big Λ => logCell h (tupleProd Λ t)) (x := d) hd]
    refine (mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q _ => ?_)).symm
    rw [Complex.ofReal_zero, zero_mul, mul_zero]

open _root_.Classical in
/-- **The reproduction formula on a retained cell**, for a function `ψ = χ₀(P_Λ)` with `χ₀` in
`𝒞_Q` of modulus one on the products, when the Gram entries of `χ₀` against the other members of
`𝒞_Q` on the cell of `X` are at most `η`. -/
theorem core (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) {Q h ξ η : ℝ} (hξ : 0 < ξ)
    (hη : 0 ≤ η) (X : AuxList big Λ)
    (hX : ξ ≤ cellMass big Λ h (logCell h (tupleProd Λ X))) (ψ : AuxList big Λ → ℂ)
    {q₀ : Σ r : ℕ, DirichletCharacter ℂ r} (hq₀ : q₀ ∈ Family.charSet Q)
    (hψ : ∀ d, ψ d = Family.charFun Λ q₀ d) (hunit : ∀ d : AuxList big Λ, ‖Family.charFun Λ q₀ d‖ = 1)
    (hgram : ∀ q ∈ Family.charSet Q, q ≠ q₀ →
      ‖∑ d : AuxList big Λ,
        ((Frame.cellWeight (auxWeight big Λ)
          (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
          (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
          (conj (Family.charFun Λ q d) * Family.charFun Λ q₀ d)‖ ≤ η) :
    ‖(∑ d : AuxList big Λ, ((auxWeight big Λ d : ℝ) : ℂ) *
        (cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ X) * ψ d)) - ψ X‖ ≤
      (primitiveCharCount Q : ℝ) * (η / ξ) := by
  have hν : 0 < cellMass big Λ h (logCell h (tupleProd Λ X)) := lt_of_lt_of_le hξ hX
  have hνc : ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hν.ne'
  -- the sum over `d`, expanded over `𝒞_Q`
  have hS : ∑ d : AuxList big Λ, ((auxWeight big Λ d : ℝ) : ℂ) *
        (cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ X) * ψ d) =
      ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
        ∑ q ∈ Family.charSet Q, Family.charFun Λ q X *
          ∑ d : AuxList big Λ,
            ((Frame.cellWeight (auxWeight big Λ)
              (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
              (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
              (conj (Family.charFun Λ q d) * Family.charFun Λ q₀ d) := by
    rw [Finset.sum_congr rfl fun d _ => term_eq big Λ Q h ξ X hX ψ q₀ hψ d, ← Finset.mul_sum,
      Finset.sum_comm]
    refine congrArg
      (fun z => ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ * z)
      (Finset.sum_congr rfl fun q _ => ?_)
    rw [Finset.mul_sum]
  -- the diagonal summand
  have hG₀ : ∑ d : AuxList big Λ,
        ((Frame.cellWeight (auxWeight big Λ)
          (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
          (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
          (conj (Family.charFun Λ q₀ d) * Family.charFun Λ q₀ d) =
      ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ) := by
    have h1 : ∀ d : AuxList big Λ,
        ((Frame.cellWeight (auxWeight big Λ)
          (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
          (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
          (conj (Family.charFun Λ q₀ d) * Family.charFun Λ q₀ d) =
        ((Frame.cellWeight (auxWeight big Λ)
          (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
          (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) := fun d => by
      rw [Complex.conj_mul', hunit d, Complex.ofReal_one, one_pow, mul_one]
    rw [Finset.sum_congr rfl fun d _ => h1 d, ← Complex.ofReal_sum]
    rfl
  -- split off the diagonal summand
  have hsplit : (∑ d : AuxList big Λ, ((auxWeight big Λ d : ℝ) : ℂ) *
        (cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ X) * ψ d)) - ψ X =
      ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
        ∑ q ∈ (Family.charSet Q).erase q₀, Family.charFun Λ q X *
          ∑ d : AuxList big Λ,
            ((Frame.cellWeight (auxWeight big Λ)
              (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
              (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
              (conj (Family.charFun Λ q d) * Family.charFun Λ q₀ d) := by
    rw [hS, ← Finset.add_sum_erase _ _ hq₀, hG₀, hψ X]
    calc ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
          (Family.charFun Λ q₀ X * ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ) +
            ∑ q ∈ (Family.charSet Q).erase q₀, Family.charFun Λ q X *
              ∑ d : AuxList big Λ,
                ((Frame.cellWeight (auxWeight big Λ)
                  (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
                  (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
                  (conj (Family.charFun Λ q d) * Family.charFun Λ q₀ d)) -
          Family.charFun Λ q₀ X
        = Family.charFun Λ q₀ X *
            (((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
              ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)) +
          ((cellMass big Λ h (logCell h (tupleProd Λ X)) : ℝ) : ℂ)⁻¹ *
            (∑ q ∈ (Family.charSet Q).erase q₀, Family.charFun Λ q X *
              ∑ d : AuxList big Λ,
                ((Frame.cellWeight (auxWeight big Λ)
                  (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
                  (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
                  (conj (Family.charFun Λ q d) * Family.charFun Λ q₀ d)) -
          Family.charFun Λ q₀ X := by ring
      _ = _ := by
          rw [inv_mul_cancel₀ hνc, mul_one]
          ring
  -- the other summands
  have hR : ‖∑ q ∈ (Family.charSet Q).erase q₀, Family.charFun Λ q X *
        ∑ d : AuxList big Λ,
          ((Frame.cellWeight (auxWeight big Λ)
            (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
            (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
            (conj (Family.charFun Λ q d) * Family.charFun Λ q₀ d)‖ ≤
      (primitiveCharCount Q : ℝ) * η := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ q ∈ (Family.charSet Q).erase q₀,
        ‖Family.charFun Λ q X *
          ∑ d : AuxList big Λ,
            ((Frame.cellWeight (auxWeight big Λ)
              (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
              (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
              (conj (Family.charFun Λ q d) * Family.charFun Λ q₀ d)‖ ≤ η := by
      intro q hq
      rw [norm_mul]
      exact (mul_le_mul (Family.norm_charFun_le Λ q X)
        (hgram q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)) (norm_nonneg _)
        zero_le_one).trans (le_of_eq (one_mul η))
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hη
    rw [← Family.card_charSet]
    exact_mod_cast Finset.card_erase_le
  rw [hsplit, norm_mul, norm_inv, Complex.norm_of_nonneg hν.le]
  calc (cellMass big Λ h (logCell h (tupleProd Λ X)))⁻¹ *
        ‖∑ q ∈ (Family.charSet Q).erase q₀, Family.charFun Λ q X *
          ∑ d : AuxList big Λ,
            ((Frame.cellWeight (auxWeight big Λ)
              (fun t : AuxList big Λ => logCell h (tupleProd Λ t))
              (logCell h (tupleProd Λ X)) d : ℝ) : ℂ) *
              (conj (Family.charFun Λ q d) * Family.charFun Λ q₀ d)‖
      ≤ ξ⁻¹ * ((primitiveCharCount Q : ℝ) * η) :=
        mul_le_mul (inv_anti₀ hξ hX) hR (norm_nonneg _) (inv_nonneg.mpr hξ.le)
    _ = (primitiveCharCount Q : ℝ) * (η / ξ) := by ring

end Repro

/-! ### The formula -/

/-- **The reproduction formula (eq:ideal-character-reproduction)** [S-03:0391–0403], from
(eq:ideal-character-cell) and primitive induction. -/
theorem characterReproduction_of (hcellS : CharacterCell) (hind : PrimitiveInduction) :
    CharacterReproduction := by
  intro P m qs hs xs E hqs _ _
  obtain ⟨x₁, hcell⟩ := hcellS P m qs (E + 2 * qs + xs) hqs
  obtain ⟨x₂, hscale⟩ := scaleLowerBound P (qs + 1)
  refine ⟨max (max x₁ x₂) (Real.exp 2), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 hint J Λ hne hΛ r ψ hr hrQ X hX
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx₂ : x₂ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxe : Real.exp 2 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hL2 : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  have hQ0 : 0 < Real.log x ^ qs := Real.rpow_pos_of_pos hL0 _
  have hh0 : 0 < Real.log x ^ (-hs) := Real.rpow_pos_of_pos hL0 _
  have hξ0 : 0 < Real.log x ^ (-xs) := Real.rpow_pos_of_pos hL0 _
  have hη0 : 0 ≤ Real.log x ^ (-(E + 2 * qs + xs)) := Real.rpow_nonneg hL0.le _
  have hc := hcell x hx₁ S B 𝔊 hint J Λ hne hΛ (Real.log x ^ (-hs)) hh0
  -- the big primes exceed `Q`, so the products are units modulo `r`
  have hbig : ∀ (g : B) (p : ℕ), p ∈ 𝔊.big g → Real.log x ^ qs < (p : ℝ) := by
    intro g p hp
    have h1 := (hscale x hx₂ S B 𝔊).1 g p hp
    rw [Real.rpow_add_one hL0.ne'] at h1
    have h2 : Real.log x ^ qs * 2 ≤ Real.log x ^ qs * Real.log x :=
      mul_le_mul_of_nonneg_left hL2 hQ0.le
    linarith
  have hcopP : ∀ (g : B) (p : ℕ), p ∈ 𝔊.big g → Nat.Coprime p r := by
    intro g p hp
    have hlt : r < p := by
      have h1 : (r : ℝ) < (p : ℝ) := lt_of_le_of_lt hrQ (hbig g p hp)
      exact_mod_cast h1
    exact ((𝔊.prime_big g p hp).coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hr hlt)
  have hcop : ∀ d : AuxList 𝔊.big Λ, Nat.Coprime (tupleProd Λ d) r := by
    intro d
    unfold tupleProd
    exact Nat.coprime_prod_left_iff.mpr fun g _ =>
      Nat.coprime_prod_left_iff.mpr fun i _ => hcopP g (d g i) (d g i).2
  -- the inducing primitive character
  obtain ⟨r₀, χ₀, hr₀, hdvd, hprim, hagree⟩ := hind r ψ hr
  have hr₀le : r₀ ≤ r := Nat.le_of_dvd hr hdvd
  have hq₀ : (⟨r₀, χ₀⟩ : Σ r : ℕ, DirichletCharacter ℂ r) ∈
      Family.charSet (Real.log x ^ qs) :=
    Family.mem_charSet.mpr
      ⟨⟨hr₀, Nat.le_floor ((Nat.cast_le.mpr hr₀le).trans hrQ)⟩, hprim⟩
  have hψ : ∀ d : AuxList 𝔊.big Λ, ψ ((tupleProd Λ d : ℕ) : ZMod r) =
      Family.charFun Λ (⟨r₀, χ₀⟩ : Σ r : ℕ, DirichletCharacter ℂ r) d :=
    fun d => hagree _ (hcop d)
  have hunit : ∀ d : AuxList 𝔊.big Λ,
      ‖Family.charFun Λ (⟨r₀, χ₀⟩ : Σ r : ℕ, DirichletCharacter ℂ r) d‖ = 1 := by
    intro d
    have hu : IsUnit ((tupleProd Λ d : ℕ) : ZMod r₀) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (Nat.Coprime.coprime_dvd_right hdvd (hcop d))
    have h2 := χ₀.unit_norm_eq_one hu.unit
    rw [IsUnit.unit_spec] at h2
    exact h2
  have hcore := Repro.core 𝔊.big Λ hξ0 hη0 X hX
    (fun d : AuxList 𝔊.big Λ => ψ ((tupleProd Λ d : ℕ) : ZMod r)) hq₀ hψ hunit
    (fun q hq hne' => Family.gram_entry_le 𝔊.big Λ hQ0.le hc _ hq hq₀ hne')
  refine hcore.trans ?_
  have h1 : (primitiveCharCount (Real.log x ^ qs) : ℝ) ≤ (Real.log x ^ qs) ^ 2 :=
    primitiveCharCount_le_sq _ hQ0.le
  have h2 : (Real.log x ^ qs) ^ 2 *
      (Real.log x ^ (-(E + 2 * qs + xs)) / Real.log x ^ (-xs)) = Real.log x ^ (-E) := by
    rw [sq, ← Real.rpow_add hL0, ← Real.rpow_sub hL0, ← Real.rpow_add hL0]
    have h3 : qs + qs + (-(E + 2 * qs + xs) - -xs) = -E := by ring
    rw [h3]
  have h4 : 0 ≤ Real.log x ^ (-(E + 2 * qs + xs)) / Real.log x ^ (-xs) :=
    div_nonneg hη0 hξ0.le
  exact (mul_le_mul_of_nonneg_right h1 h4).trans (le_of_eq h2)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
