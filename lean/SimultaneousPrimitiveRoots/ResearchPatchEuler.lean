module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace SimultaneousPrimitiveRoots

/-- Exact local row in research_patch_ja.md (2.2). -/
def patchEulerRow {F : Type*} [Field F] (Q D W V E : F) : F :=
  1 / (1 - V) + W / (1 - W) +
    E / (1 - E) * ((1 - 1 / Q) / (1 - V) + W) -
    D / (1 - E) * (1 + (Q - 1) * W * V / (1 - V))

/-- A cancelled expression with no denominator 1-W. This algebraic expression
can be used at W=1; analytic continuation is a separate theorem. -/
def patchCancelledEuler {F : Type*} [Field F] (Q D W V E : F) : F :=
  (1 - D * W) *
    (Q * (1 - E) * (1 - W * V) +
      E * ((Q - 1) * (1 - W) + Q * W * (1 - V) * (1 - W)) -
      Q * D * ((1 - V) * (1 - W) + (Q - 1) * W * V * (1 - W))) /
    (Q * (1 - D) * (1 - E))

theorem patchEuler_cancel {F : Type*} [Field F] (Q D W V E : F)
    (hQ : Q ≠ 0) (hD : 1 - D ≠ 0) (hW : 1 - W ≠ 0)
    (hV : 1 - V ≠ 0) (hE : 1 - E ≠ 0) :
    (1 - D * W) * (1 - V) * (1 - W) * patchEulerRow Q D W V E / (1 - D) =
      patchCancelledEuler Q D W V E := by
  unfold patchEulerRow patchCancelledEuler
  field_simp
  ring

theorem patchEuler_zeroE_identity {F : Type*} [Field F] (Q D W V : F)
    (hQ : Q ≠ 0) (hD : 1 - D ≠ 0) :
    patchCancelledEuler Q D W V 0 - 1 =
      ((D * W) * (D - D * W) + (1 - D * W) *
        (D * V - V * W - Q * D * V * W + (Q - 1) * D * V * W ^ 2)) /
          (1 - D) := by
  unfold patchCancelledEuler
  field_simp
  ring

/-- The twenty monomials are certified by a ring identity, rather than by a
floating-point check at sample primes. -/
def patchEulerNumerator {F : Type*} [CommRing F] (Q D W V E : F) : F :=
  -E + W * E + D * W * E - D * W ^ 2 * E + Q * E - Q * W * V -
    Q * W ^ 2 * E + Q * W ^ 2 * V * E - Q * D * E + Q * D * V +
    Q * D * W ^ 3 * E - Q * D * W ^ 3 * V * E + Q * D ^ 2 * W -
    Q * D ^ 2 * W * V - Q * D ^ 2 * W ^ 2 + Q * D ^ 2 * W ^ 3 * V -
    Q ^ 2 * D * W * V + Q ^ 2 * D * W ^ 2 * V +
    Q ^ 2 * D ^ 2 * W ^ 2 * V - Q ^ 2 * D ^ 2 * W ^ 3 * V

theorem patchEuler_twenty_term_identity {F : Type*} [Field F] (Q D W V E : F)
    (hQ : Q ≠ 0) (hD : 1 - D ≠ 0) (hE : 1 - E ≠ 0) :
    patchCancelledEuler Q D W V E - 1 =
      patchEulerNumerator Q D W V E / (Q * (1 - D) * (1 - E)) := by
  unfold patchCancelledEuler patchEulerNumerator
  field_simp
  ring

theorem patchEuler_valuationOne_identity {F : Type*} [Field F] (Q T V E : F)
    (hQ : Q ≠ 0) (hV : 1 - V ≠ 0) (hE : 1 - E ≠ 0) :
    (1 - T) * (1 - V) *
      (1 / (1 - V) + (1 - 1 / Q) * E / ((1 - V) * (1 - E)) -
        (Q - 1) * T * V / ((1 - V) * (1 - E)) + T / (1 - E)) =
      (1 - T) * (1 - E / Q + T - Q * T * V) / (1 - E) := by
  field_simp
  ring

theorem patchEuler_valuationOne_remainder {F : Type*} [Field F] (Q T V E : F)
    (hQ : Q ≠ 0) (hE : 1 - E ≠ 0) :
    (1 - T) * (1 - E / Q + T - Q * T * V) / (1 - E) - 1 =
      (E - E / Q + T * E / Q - T ^ 2 - Q * T * V + Q * T ^ 2 * V) / (1 - E) := by
  field_simp
  ring

/-- Exponents of Q,D,W,V,E in the numerator, in the same order as its terms.
The extra -1 is division by Q in the common denominator. -/
def patchEulerMonomials : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(0,0,0,0,1), (0,0,1,0,1), (0,1,1,0,1), (0,1,2,0,1),
   (1,0,0,0,1), (1,0,1,1,0), (1,0,2,0,1), (1,0,2,1,1),
   (1,1,0,0,1), (1,1,0,1,0), (1,1,3,0,1), (1,1,3,1,1),
   (1,2,1,0,0), (1,2,1,1,0), (1,2,2,0,0), (1,2,3,1,0),
   (2,1,1,1,0), (2,1,2,1,0), (2,2,2,1,0), (2,2,3,1,0)]

def patchEulerExponent (t : ℕ × ℕ × ℕ × ℕ × ℕ) : ℚ :=
  (t.1 : ℚ) - t.2.1 + (t.2.2.1 : ℚ) / 10 -
    12 * (t.2.2.2.1 : ℚ) / 5 - 22 * (t.2.2.2.2 : ℚ) / 5 - 1

def patchEulerCoefficients : List ℤ :=
  [-1,1,1,-1,1,-1,-1,1,-1,1,1,-1,1,-1,-1,1,-1,1,1,-1]

def patchEulerMonomial {F : Type*} [CommRing F] (Q D W V E : F)
    (t : ℕ × ℕ × ℕ × ℕ × ℕ) : F :=
  Q ^ t.1 * D ^ t.2.1 * W ^ t.2.2.1 * V ^ t.2.2.2.1 * E ^ t.2.2.2.2

/-- Link the exponent inventory to the very polynomial in the rational
identity; the inventory is not a detached list of favourable exponents. -/
theorem patchEuler_monomial_certificate {F : Type*} [CommRing F] (Q D W V E : F) :
    ((patchEulerCoefficients.zip patchEulerMonomials).map
      (fun t => (t.1 : F) * patchEulerMonomial Q D W V E t.2)).sum =
        patchEulerNumerator Q D W V E := by
  simp only [patchEulerCoefficients, patchEulerMonomials, patchEulerMonomial,
    List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, pow_zero, pow_one, Int.cast_one, Int.cast_neg]
  unfold patchEulerNumerator
  ring

theorem patchEuler_monomials_count : patchEulerMonomials.length = 20 := by decide

theorem patchEuler_exponents_le :
    ∀ t ∈ patchEulerMonomials, patchEulerExponent t ≤ -9 / 5 := by
  norm_num [patchEulerMonomials, patchEulerExponent]

theorem patchEuler_slow_term_exponent : patchEulerExponent (1,2,2,0,0) = -9 / 5 := by
  norm_num [patchEulerExponent]

theorem patch_contour_exponent :
    (9 / 10 : ℚ) / 2 + (1 + 1 / 10000000) - 1 +
      (1 / 10) * (2 / 5) + (133 / 1000) * (-1 / 10 - 1) = 3437001 / 10000000 := by
  norm_num

theorem patch_small_rows_exponent :
    (3437001 / 10000000 : ℚ) + (101 / 1000) * (6 / 5) = 4649001 / 10000000 := by
  norm_num

theorem patch_small_rows_gap :
    (7 / 15 : ℚ) - 4649001 / 10000000 = 52997 / 30000000 ∧
      (52997 / 30000000 : ℚ) > 1 / 1000 := by
  norm_num

theorem patch_far_rows_exponent :
    (3849 / 1000 : ℚ) + (1 / 10) * 4000 + (101 / 1000) * (1 - 4000) = -1 / 20 := by
  norm_num

theorem patch_probe_gap :
    (7 / 15 : ℚ) - 933 / 2000 = 1 / 6000 ∧
      (933 / 2000 : ℚ) + 1 / 100000 < 7 / 15 - 1 / 20000 := by
  norm_num

end SimultaneousPrimitiveRoots
