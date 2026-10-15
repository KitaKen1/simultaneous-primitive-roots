module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TypeII
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The marked Type II estimate for coefficients twisted by a character

The public paper carries the residue class `p ≡ b (mod H)` through [P] §7 by expanding it into
Dirichlet characters `λ` modulo `H` (`[PUB-tex:0503–0516]`). This file proves the step this needs,
from the two Type II statements of `TypeII.lean`:

* `passesCoefficientTest_twistFamily`: by [P] Lemma 5.2 (`PrimeMinusRoughLongCoefficient`) the
  prime-minus-rough coefficients twisted by a character modulo a fixed `H` pass the coefficient
  test (the product character has modulus `lcm(H, k) ≤ L^{A₀+1}`);
* `markedTypeII_twisted`: hence `MarkedTypeIICoefficientForm` gives the marked Type II bound for the
  coefficient `α_m λ(m)`, uniformly in `λ`, the twist, the interval, `F` and `β`, with `K₀`
  independent of the bands.

The proofs were written by the independent reviewer of the statement layer (2026-10-12) as a check
that the two statements are strong enough for this use.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply

noncomputable section

/-- `λ χ` as a character modulo `lcm(H, k)`. -/
def prodChar {H k : ℕ} (lam : DirichletCharacter ℂ H) (χ : DirichletCharacter ℂ k) :
    DirichletCharacter ℂ (Nat.lcm H k) :=
  DirichletCharacter.changeLevel (Nat.dvd_lcm_left H k) lam *
    DirichletCharacter.changeLevel (Nat.dvd_lcm_right H k) χ

theorem prodChar_apply {H k : ℕ} (lam : DirichletCharacter ℂ H) (χ : DirichletCharacter ℂ k)
    (m : ℕ) :
    prodChar lam χ (m : ZMod (Nat.lcm H k)) = lam (m : ZMod H) * χ (m : ZMod k) := by
  unfold prodChar
  rw [MulChar.mul_apply]
  by_cases hm : m.Coprime (Nat.lcm H k)
  · have hu : ((ZMod.unitOfCoprime m hm : (ZMod (Nat.lcm H k))ˣ) : ZMod (Nat.lcm H k)) = m :=
      ZMod.coe_unitOfCoprime m hm
    rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
      ZMod.cast_natCast (Nat.dvd_lcm_left H k), ZMod.cast_natCast (Nat.dvd_lcm_right H k)]
  · have hnu : ¬ IsUnit ((m : ℕ) : ZMod (Nat.lcm H k)) := fun h =>
      hm ((ZMod.isUnit_iff_coprime m (Nat.lcm H k)).mp h)
    rw [MulChar.map_nonunit _ hnu, zero_mul]
    by_cases hmH : m.Coprime H
    · have hmk : ¬ m.Coprime k := fun h =>
        hm (Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul H k) (hmH.mul_right h))
      have hk' : ¬ IsUnit ((m : ℕ) : ZMod k) := fun h =>
        hmk ((ZMod.isUnit_iff_coprime m k).mp h)
      rw [MulChar.map_nonunit χ hk', mul_zero]
    · have hH' : ¬ IsUnit ((m : ℕ) : ZMod H) := fun h =>
        hmH ((ZMod.isUnit_iff_coprime m H).mp h)
      rw [MulChar.map_nonunit lam hH', zero_mul]

theorem twistedSum_twist (Hm : ℝ) (α : ℕ → ℂ) {H k : ℕ} (lam : DirichletCharacter ℂ H)
    (χ : DirichletCharacter ℂ k) (t : ℝ) :
    twistedSum Hm (fun m => α m * lam (m : ZMod H)) χ t =
      twistedSum Hm α (prodChar lam χ) t := by
  unfold twistedSum
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [prodChar_apply]
  ring

/-- The family of prime-minus-rough coefficients twisted by the characters modulo `H`. -/
def twistFamily (H : ℕ) (C : ℝ) : ℝ → ℝ → ℝ → Set (ℕ → ℂ) := fun x Hm _ =>
  {α | ∃ (v lo hi : ℝ) (lam : DirichletCharacter ℂ H), |v| ≤ Real.log x ^ C ∧ Hm ≤ lo ∧
    hi ≤ 2 * Hm ∧ α = fun m => primeMinusRough x v lo hi m * lam (m : ZMod H)}

/-- [P] Lemma 5.2 at the modulus exponent `A₀ + 1` gives the coefficient test for the twisted
family (`[PUB-tex:0509–0514]`). -/
theorem passesCoefficientTest_twistFamily (h52 : PrimeMinusRoughLongCoefficient) {H : ℕ}
    (hH : 0 < H) {δ C κ : ℝ} (hδ : 0 < δ) (hC : 0 < C) (hκ : 1 ≤ κ) :
    PassesCoefficientTest δ κ (twistFamily H C) := by
  intro A₀ B A hA₀ hB hA
  obtain ⟨M, x₀, hM⟩ := h52 δ C κ hδ hC hκ (A₀ + 1) B A (by linarith) hB hA
  refine ⟨M, max x₀ (Real.exp (max (H : ℝ) 1)), fun x hx Hm Hn hs α hα => ?_⟩
  obtain ⟨v, lo, hi, lam, hv, hlo, hhi, rfl⟩ := hα
  have hx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp (max (H : ℝ) 1) ≤ x := (le_max_right _ _).trans hx
  have hlog : max (H : ℝ) 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hxe
    rwa [Real.log_exp] at this
  have hHL : (H : ℝ) ≤ Real.log x := (le_max_left _ _).trans hlog
  have hL1 : 1 ≤ Real.log x := (le_max_right _ _).trans hlog
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  intro k hk hkL χ t ht
  have hmod : ((Nat.lcm H k : ℕ) : ℝ) ≤ Real.log x ^ (A₀ + 1) := by
    have h1 : Nat.lcm H k ≤ H * k := Nat.le_of_dvd (Nat.mul_pos hH hk) (Nat.lcm_dvd_mul H k)
    have h2 : ((Nat.lcm H k : ℕ) : ℝ) ≤ (H : ℝ) * (k : ℝ) := by exact_mod_cast h1
    calc ((Nat.lcm H k : ℕ) : ℝ) ≤ (H : ℝ) * (k : ℝ) := h2
      _ ≤ Real.log x * Real.log x ^ A₀ := mul_le_mul hHL hkL (Nat.cast_nonneg k) hL0.le
      _ = Real.log x ^ (A₀ + 1) := by rw [Real.rpow_add_one hL0.ne', mul_comm]
  have key := hM x hx₀ Hm Hn hs v hv lo hi hlo hhi (Nat.lcm H k) (Nat.lcm_pos hH hk) hmod
    (prodChar lam χ) t ht
  rw [twistedSum_twist]
  exact key

/-- A twist by a character keeps the support and the bound. -/
theorem roughDyadCoefficient_twist {x C Hm : ℝ} {α : ℕ → ℂ} (h : RoughDyadCoefficient x C Hm α)
    {H : ℕ} (lam : DirichletCharacter ℂ H) :
    RoughDyadCoefficient x C Hm (fun m => α m * lam (m : ZMod H)) where
  support := fun m hm => h.support m (fun h0 => hm (by rw [h0, zero_mul]))
  bound := fun m => by
    rw [norm_mul]
    calc ‖α m‖ * ‖lam (m : ZMod H)‖ ≤ ‖α m‖ * 1 :=
          mul_le_mul_of_nonneg_left (lam.norm_le_one _) (norm_nonneg _)
      _ = ‖α m‖ := mul_one _
      _ ≤ Real.log x ^ C := h.bound m

/-- **Type II with the class carried by characters**: the bound of Theorem 3.1 for `α_m λ(m)`,
from the coefficient form and Lemma 5.2. `K₀` does not depend on the bands; `M`, `x₀` do not
depend on `λ`, `v`, the interval, `F`, `β`. -/
theorem markedTypeII_twisted (hII : MarkedTypeIICoefficientForm)
    (h52 : PrimeMinusRoughLongCoefficient) {H : ℕ} (hH : 0 < H)
    (δ C Dstar q κ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar) (hq : 0 < q) (hq1 : q < 1)
    (hκ : 1 ≤ κ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ 𝔞 : MarkingArray K,
      ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Hm Hn : ℝ, TypeIIScales δ κ x Hm Hn →
        ∀ F : ℕ → ℂ, (∀ h, ‖F h‖ ≤ 1) → BandInvariant 𝔞 x F →
          ∀ v : ℝ, |v| ≤ Real.log x ^ C → ∀ lo hi : ℝ, Hm ≤ lo → hi ≤ 2 * Hm →
            RoughDyadCoefficient x C Hm (primeMinusRough x v lo hi) →
            ∀ lam : DirichletCharacter ℂ H,
              ∀ β : ℕ → ℂ, RoughDyadCoefficient x C Hn β →
                ‖markedBilinearSum q 𝔞 x Hm Hn
                    (fun m => primeMinusRough x v lo hi m * lam (m : ZMod H)) β F‖ ≤
                  M * (Hm * Hn) * Real.log x ^ (-Dstar) := by
  obtain ⟨K₀, hK₀⟩ := hII δ C Dstar q κ hδ hC hD hq hq1 hκ
  refine ⟨K₀, fun K hK 𝔞 => ?_⟩
  obtain ⟨M, x₀, hM⟩ := hK₀ K hK 𝔞 (twistFamily H C)
    (passesCoefficientTest_twistFamily h52 hH hδ hC hκ)
  refine ⟨M, x₀, fun x hx Hm Hn hs F hF hFinv v hv lo hi hlo hhi hα lam β hβ => ?_⟩
  exact hM x hx Hm Hn hs F hF hFinv _ ⟨v, lo, hi, lam, hv, hlo, hhi, rfl⟩
    (roughDyadCoefficient_twist hα lam) β hβ

end

end SimultaneousPrimitiveRoots.Unconditional.Supply
