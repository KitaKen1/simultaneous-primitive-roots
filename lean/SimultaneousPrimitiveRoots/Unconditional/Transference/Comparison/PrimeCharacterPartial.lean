module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Leaves
public import SimultaneousPrimitiveRoots.Unconditional.Supply.ClassicalInputs
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Sums of a nonprincipal character over the primes, from Siegel–Walfisz

Source: `verification/stage7-sources/S-03.tex`, lines 222–230 (`[S-03:0222–0230]`).

"For every fixed `K`, Theorem `thm:sw`, summed against the character over reduced residue classes
and applied with a larger accuracy exponent, gives `A_ρ(t) := ∑_{p ≤ t} ρ(p) ≪_K t (log t)^{-K}`
for these nonprincipal characters."

* `PrimeSums.primeCharSum ρ n = ∑_{p ≤ n} ρ(p)`.
* `PrimeSums.norm_sum_char_le` — a character sum over a finite set `P` of integers, sorted by
  residue classes: if the number of elements of `P` in every reduced class `a` is `c` up to an
  error `E`, then `|∑_{p ∈ P} ρ(p)| ≤ q E` for nonprincipal `ρ` modulo `q` (orthogonality kills
  the main term; the classes which are not reduced contribute `0`).
* `PrimeSums.primeCharSum_le_of_siegelWalfisz` — with the prime counts of the Siegel–Walfisz
  theorem: `|A_ρ(n)| ≤ q M n (log n)^{-A}` for `n ≥ y₁` and `q ≤ (log n)^{C'}`.

The partial summation is in `Comparison/PrimeCharacterSums.lean`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace PrimeSums

/-! ### The partial sums -/

/-- `A_ρ(n) = ∑_{p ≤ n} ρ(p)`, the sum of a character over the primes up to `n`. -/
def primeCharSum {q : ℕ} (ρ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ p ∈ Finset.range (n + 1), if p.Prime then ρ (p : ZMod q) else 0

theorem primeCharSum_succ {q : ℕ} (ρ : DirichletCharacter ℂ q) (n : ℕ) :
    primeCharSum ρ (n + 1) =
      primeCharSum ρ n + (if (n + 1).Prime then ρ ((n + 1 : ℕ) : ZMod q) else 0) := by
  unfold primeCharSum
  exact Finset.sum_range_succ _ _

theorem primeCharSum_eq_filter {q : ℕ} (ρ : DirichletCharacter ℂ q) (n : ℕ) :
    primeCharSum ρ n = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ρ (p : ZMod q) := by
  unfold primeCharSum
  exact (Finset.sum_filter _ _).symm

/-! ### Summing against a nonprincipal character over the residue classes -/

/-- Orthogonality: a constant can be subtracted from the coefficients of a nonprincipal
character. -/
theorem sum_mul_char_sub {q : ℕ} [NeZero q] (ρ : DirichletCharacter ℂ q) (hρ : ρ ≠ 1)
    (g : ZMod q → ℂ) (c : ℂ) :
    ∑ x : ZMod q, g x * ρ x = ∑ x : ZMod q, (g x - c) * ρ x := by
  have h0 : ∑ x : ZMod q, ρ x = 0 := MulChar.sum_eq_zero_of_ne_one hρ
  have h3 : ∑ x : ZMod q, (g x - c) * ρ x =
      ∑ x : ZMod q, g x * ρ x - c * ∑ x : ZMod q, ρ x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => sub_mul _ _ _
  rw [h3, h0, mul_zero, sub_zero]

/-- If the coefficients at the reduced classes are at most `E`, the sum against a character
modulo `q` is at most `q E` (the other classes contribute `0`). -/
theorem norm_sum_mul_char_le {q : ℕ} [NeZero q] (ρ : DirichletCharacter ℂ q) (G : ZMod q → ℂ)
    {E : ℝ} (hE : 0 ≤ E) (hG : ∀ x : ZMod q, IsUnit x → ‖G x‖ ≤ E) :
    ‖∑ x : ZMod q, G x * ρ x‖ ≤ (q : ℝ) * E := by
  have hterm : ∀ x : ZMod q, ‖G x * ρ x‖ ≤ E := by
    intro x
    by_cases hx : IsUnit x
    · rw [norm_mul]
      calc ‖G x‖ * ‖ρ x‖ ≤ E * 1 :=
            mul_le_mul (hG x hx) (DirichletCharacter.norm_le_one ρ x) (norm_nonneg _) hE
        _ = E := mul_one E
    · rw [MulChar.map_nonunit ρ hx, mul_zero, norm_zero]
      exact hE
  calc ‖∑ x : ZMod q, G x * ρ x‖ ≤ ∑ x : ZMod q, ‖G x * ρ x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : ZMod q, E := Finset.sum_le_sum fun x _ => hterm x
    _ = (q : ℝ) * E := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- **Summing the counts over the reduced residue classes against `ρ`.** Let `P` be a finite set
of integers and `F a` its part in the class `a` modulo `q`. If every reduced class contains `c`
elements up to an error `E`, then `|∑_{p ∈ P} ρ(p)| ≤ q E` for a nonprincipal `ρ`. -/
theorem norm_sum_char_le {q : ℕ} [NeZero q] (ρ : DirichletCharacter ℂ q) (hρ : ρ ≠ 1)
    (P : Finset ℕ) {F : ℕ → Finset ℕ} {c E : ℝ}
    (hcount : ∀ a : ℕ, Nat.Coprime a q → |((F a).card : ℝ) - c| ≤ E) (hE : 0 ≤ E)
    (hF : ∀ a p : ℕ, p ∈ F a ↔ p ∈ P ∧ p ≡ a [MOD q]) :
    ‖∑ p ∈ P, ρ (p : ZMod q)‖ ≤ (q : ℝ) * E := by
  -- sort `P` by residue classes
  have h1 : ∑ p ∈ P, ρ (p : ZMod q) = ∑ x : ZMod q, ((F x.val).card : ℂ) * ρ x := by
    refine (Finset.sum_fiberwise' P (fun p : ℕ => (p : ZMod q)) (fun x => ρ x)).symm.trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine congrArg (fun k : ℕ => (k : ℂ) * ρ x) (congrArg Finset.card (Finset.ext fun p => ?_))
    rw [Finset.mem_filter, hF, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  rw [h1, sum_mul_char_sub ρ hρ _ (c : ℂ)]
  refine norm_sum_mul_char_le ρ _ hE fun x hx => ?_
  have hcop : Nat.Coprime x.val q := by
    have h := ZMod.val_coe_unit_coprime hx.unit
    rwa [IsUnit.unit_spec] at h
  have hcast : (((F x.val).card : ℂ) - (c : ℂ)) = ((((F x.val).card : ℝ) - c : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_natCast]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  exact hcount x.val hcop

/-! ### The Siegel–Walfisz theorem for a nonprincipal character -/

/-- **`A_ρ(n) ≪ q n (log n)^{-A}`** [S-03:0222–0230]: the Siegel–Walfisz theorem, summed against
a nonprincipal character over the reduced residue classes. -/
theorem primeCharSum_le_of_siegelWalfisz (hSW : Supply.SiegelWalfiszPrimeCounting) (A C' : ℝ)
    (hA : 0 < A) (hC' : 0 < C') :
    ∃ M₁ : ℝ, 0 < M₁ ∧ ∃ y₁ : ℝ, ∀ q : ℕ, 0 < q → ∀ ρ : DirichletCharacter ℂ q, ρ ≠ 1 →
      ∀ n : ℕ, y₁ ≤ (n : ℝ) → (q : ℝ) ≤ Real.log (n : ℝ) ^ C' →
        ‖primeCharSum ρ n‖ ≤ (q : ℝ) * (M₁ * (n : ℝ) * Real.log (n : ℝ) ^ (-A)) := by
  obtain ⟨M₁, hM₁, y₁, h₁⟩ := hSW A C' hA hC'
  refine ⟨M₁, hM₁, y₁, fun q hq ρ hρ n hn hqn => ?_⟩
  have : NeZero q := ⟨hq.ne'⟩
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne'
  have hcount := fun (a : ℕ) (ha : Nat.Coprime a q) => h₁ (n : ℝ) hn q hq1 hqn a ha
  have hE : 0 ≤ M₁ * (n : ℝ) * Real.log (n : ℝ) ^ (-A) :=
    (abs_nonneg _).trans (hcount 1 (Nat.coprime_one_left q))
  rw [primeCharSum_eq_filter]
  refine norm_sum_char_le ρ hρ _ hcount hE ?_
  intro a p
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic, Finset.mem_range, Nat.floor_natCast,
    Nat.lt_add_one_iff, and_assoc]

end PrimeSums

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
