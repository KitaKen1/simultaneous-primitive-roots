module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing.Local
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Corollary 3.11: the moments `⟨u, (𝒜 𝒜*)^r u⟩` and "spectral Hölder"

Source: `verification/stage7-sources/S-02.tex`, lines 1299–1305 (`[S-02:1299–1305]`):
"For `B₀ = 𝒜 𝒜* ≥ 0`, spectral Hölder gives
`|⟨f_j, 𝒜 g_j⟩| ≤ ‖g_j‖ ‖f_j‖^{1 - 1/R} ⟨f_j, B₀^R f_j⟩^{1/(2R)}`."

The paper quotes the spectral theorem. Here the inequality behind it,
`⟨u, B₀ u⟩^R ≤ ‖u‖^{2(R-1)} ⟨u, B₀^R u⟩`, is proved without spectral theory, for functions `u`
supported on an interval of positions (this is the standard elementary argument, supplied here):

* `altOp r` is the alternating product `… 𝒜 𝒜* 𝒜 𝒜*` of length `r` (`𝒜*` is applied first), so
  `altOp (2R) = (𝒜 𝒜*)^R` (`altOp_two_mul`).
* By adjointness, `⟨altOp i u, altOp j v⟩ = ⟨u, altOp (i + j) v⟩` when `i ≡ j mod 2`
  (`gp_altOp_altOp`). Hence `‖altOp r u‖² = ⟨u, (𝒜 𝒜*)^r u⟩` (`gsq_altOp_eq_gp`): the moments are
  nonnegative, and `physMoment R n = ‖altOp R u_n‖²` (`physMoment_eq_gsq`).
* `‖altOp (r+1) u‖² = ⟨altOp r u, altOp (r+2) u⟩`, so by Cauchy–Schwarz the sequence
  `a_r = ‖altOp r u‖²` satisfies `a_{r+1}² ≤ a_r a_{r+2}` (`gsq_altOp_sq_le`).
* A nonnegative sequence with `a_{r+1}² ≤ a_r a_{r+2}` satisfies `a_1^{R+1} ≤ a_0^R a_{R+1}`
  (`logConvex_pow`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Log-convex sequences -/

/-- For a nonnegative sequence with `a_{r+1}² ≤ a_r a_{r+2}`, the ratios increase:
`a_1 a_r ≤ a_0 a_{r+1}`. -/
theorem logConvex_ratio {a : ℕ → ℝ} (h0 : ∀ r, 0 ≤ a r)
    (hc : ∀ r, a (r + 1) ^ 2 ≤ a r * a (r + 1 + 1)) (r : ℕ) :
    a 1 * a r ≤ a 0 * a (r + 1) := by
  induction r with
  | zero => exact le_of_eq (mul_comm _ _)
  | succ r ih =>
    rcases (h0 (r + 1)).eq_or_lt with hz | hpos
    · rw [← hz, mul_zero]
      exact mul_nonneg (h0 0) (h0 _)
    · have h1 : a 1 * a (r + 1) * a (r + 1) ≤ a 0 * a (r + 1 + 1) * a (r + 1) := by
        calc a 1 * a (r + 1) * a (r + 1) = a 1 * a (r + 1) ^ 2 := by ring
          _ ≤ a 1 * (a r * a (r + 1 + 1)) := mul_le_mul_of_nonneg_left (hc r) (h0 1)
          _ = (a 1 * a r) * a (r + 1 + 1) := by ring
          _ ≤ (a 0 * a (r + 1)) * a (r + 1 + 1) := mul_le_mul_of_nonneg_right ih (h0 _)
          _ = a 0 * a (r + 1 + 1) * a (r + 1) := by ring
      exact le_of_mul_le_mul_right h1 hpos

/-- **The interpolation inequality for a log-convex sequence**: if `a_r ≥ 0` and
`a_{r+1}² ≤ a_r a_{r+2}` for all `r`, then `a_1^{R+1} ≤ a_0^R a_{R+1}`. -/
theorem logConvex_pow {a : ℕ → ℝ} (h0 : ∀ r, 0 ≤ a r)
    (hc : ∀ r, a (r + 1) ^ 2 ≤ a r * a (r + 1 + 1)) (R : ℕ) :
    a 1 ^ (R + 1) ≤ a 0 ^ R * a (R + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    calc a 1 ^ (R + 1 + 1) = a 1 ^ (R + 1) * a 1 := pow_succ _ _
      _ ≤ (a 0 ^ R * a (R + 1)) * a 1 := mul_le_mul_of_nonneg_right ih (h0 1)
      _ = a 0 ^ R * (a 1 * a (R + 1)) := by ring
      _ ≤ a 0 ^ R * (a 0 * a (R + 1 + 1)) :=
          mul_le_mul_of_nonneg_left (logConvex_ratio h0 hc (R + 1)) (pow_nonneg (h0 0) R)
      _ = a 0 ^ (R + 1) * a (R + 1 + 1) := by
          rw [pow_succ]
          ring

/-- Cauchy–Schwarz for sums of nonnegative numbers: if `a_j² ≤ m_j γ_j` then
`(∑ a_j)² ≤ (∑ m_j)(∑ γ_j)`. -/
theorem sum_sq_le_of_forall {κ : Type*} (𝒥 : Finset κ) (a m γ : κ → ℝ)
    (ha : ∀ j ∈ 𝒥, 0 ≤ a j) (hm : ∀ j, 0 ≤ m j) (hγ : ∀ j, 0 ≤ γ j)
    (h : ∀ j ∈ 𝒥, a j ^ 2 ≤ m j * γ j) :
    (∑ j ∈ 𝒥, a j) ^ 2 ≤ (∑ j ∈ 𝒥, m j) * ∑ j ∈ 𝒥, γ j := by
  have h1 : ∑ j ∈ 𝒥, a j ≤ ∑ j ∈ 𝒥, Real.sqrt (m j) * Real.sqrt (γ j) :=
    Finset.sum_le_sum fun j hj => by
      rw [← Real.sqrt_mul (hm j)]
      exact Real.le_sqrt_of_sq_le (h j hj)
  have h2 : ∑ j ∈ 𝒥, Real.sqrt (m j) * Real.sqrt (γ j) ≤
      Real.sqrt (∑ j ∈ 𝒥, m j) * Real.sqrt (∑ j ∈ 𝒥, γ j) :=
    Real.sum_sqrt_mul_sqrt_le 𝒥 hm hγ
  have h3 : 0 ≤ ∑ j ∈ 𝒥, m j := Finset.sum_nonneg fun j _ => hm j
  have h4 : 0 ≤ ∑ j ∈ 𝒥, γ j := Finset.sum_nonneg fun j _ => hγ j
  calc (∑ j ∈ 𝒥, a j) ^ 2
      ≤ (Real.sqrt (∑ j ∈ 𝒥, m j) * Real.sqrt (∑ j ∈ 𝒥, γ j)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg ha) (h1.trans h2) 2
    _ = (∑ j ∈ 𝒥, m j) * ∑ j ∈ 𝒥, γ j := by rw [mul_pow, Real.sq_sqrt h3, Real.sq_sqrt h4]

/-- The same for the norm of a sum of complex numbers. -/
theorem norm_sum_sq_le_of_forall {κ : Type*} (𝒥 : Finset κ) (z : κ → ℂ) (m γ : κ → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hγ : ∀ j, 0 ≤ γ j) (h : ∀ j ∈ 𝒥, ‖z j‖ ^ 2 ≤ m j * γ j) :
    ‖∑ j ∈ 𝒥, z j‖ ^ 2 ≤ (∑ j ∈ 𝒥, m j) * ∑ j ∈ 𝒥, γ j :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
    (sum_sq_le_of_forall 𝒥 (fun j => ‖z j‖) m γ (fun _ _ => norm_nonneg _) hm hγ h)

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-! ### The alternating products of `𝒜*` and `𝒜` -/

section Alt

variable (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type} [Fintype N]
  (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)

/-- **The alternating product of length `r`**: `altOp 0 = 1`, `altOp 1 = 𝒜*`,
`altOp 2 = 𝒜 𝒜*`, `altOp 3 = 𝒜* 𝒜 𝒜*`, … (`𝒜*` is applied first). -/
def altOp : ℕ → Module.End ℂ (PState intPos 𝒢 J ℓ → ℂ)
  | 0 => 1
  | r + 1 =>
      (if Even r then physAdj intPos 𝒢 q 𝔉 k ζ else physOp intPos 𝒢 q 𝔉 k ζ) * altOp r

theorem altOp_zero : altOp 𝒢 q 𝔉 k ζ 0 = 1 := rfl

theorem altOp_succ (r : ℕ) :
    altOp 𝒢 q 𝔉 k ζ (r + 1) =
      (if Even r then physAdj intPos 𝒢 q 𝔉 k ζ else physOp intPos 𝒢 q 𝔉 k ζ) *
        altOp 𝒢 q 𝔉 k ζ r := rfl

theorem altOp_zero_apply (u : PState intPos 𝒢 J ℓ → ℂ) : altOp 𝒢 q 𝔉 k ζ 0 u = u := rfl

theorem altOp_succ_of_even {r : ℕ} (h : Even r) (u : PState intPos 𝒢 J ℓ → ℂ) :
    altOp 𝒢 q 𝔉 k ζ (r + 1) u = physAdj intPos 𝒢 q 𝔉 k ζ (altOp 𝒢 q 𝔉 k ζ r u) := by
  have h1 : altOp 𝒢 q 𝔉 k ζ (r + 1) = physAdj intPos 𝒢 q 𝔉 k ζ * altOp 𝒢 q 𝔉 k ζ r := by
    rw [altOp_succ, if_pos h]
  exact (LinearMap.congr_fun h1 u).trans (Module.End.mul_apply _ _ u)

theorem altOp_succ_of_not_even {r : ℕ} (h : ¬Even r) (u : PState intPos 𝒢 J ℓ → ℂ) :
    altOp 𝒢 q 𝔉 k ζ (r + 1) u = physOp intPos 𝒢 q 𝔉 k ζ (altOp 𝒢 q 𝔉 k ζ r u) := by
  have h1 : altOp 𝒢 q 𝔉 k ζ (r + 1) = physOp intPos 𝒢 q 𝔉 k ζ * altOp 𝒢 q 𝔉 k ζ r := by
    rw [altOp_succ, if_neg h]
  exact (LinearMap.congr_fun h1 u).trans (Module.End.mul_apply _ _ u)

/-- The alternating product of length `1` is `𝒜*`. -/
theorem altOp_one_apply (u : PState intPos 𝒢 J ℓ → ℂ) :
    altOp 𝒢 q 𝔉 k ζ 1 u = physAdj intPos 𝒢 q 𝔉 k ζ u :=
  altOp_succ_of_even 𝒢 q 𝔉 k ζ (r := 0) Even.zero u

/-- **The alternating product of length `2R` is `(𝒜 𝒜*)^R`**. -/
theorem altOp_two_mul (R : ℕ) :
    altOp 𝒢 q 𝔉 k ζ (2 * R) =
      (physOp intPos 𝒢 q 𝔉 k ζ * physAdj intPos 𝒢 q 𝔉 k ζ) ^ R := by
  induction R with
  | zero => rw [Nat.mul_zero, pow_zero, altOp_zero]
  | succ R ih =>
    have h1 : Even (2 * R) := even_two_mul R
    have h2 : ¬Even (2 * R + 1) := by
      rw [Nat.even_add_one, not_not]
      exact h1
    have e : 2 * (R + 1) = 2 * R + 1 + 1 := by ring
    rw [e, altOp_succ, if_neg h2, altOp_succ, if_pos h1, ih, pow_succ', mul_assoc]

/-- The alternating product of length `r` moves the position by at most `r H`. -/
theorem suppIcc_altOp (r : ℕ) {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (h : SuppIcc u a b) :
    SuppIcc (altOp 𝒢 q 𝔉 k ζ r u) (a - r * stepBound 𝒢 J k) (b + r * stepBound 𝒢 J k) := by
  induction r with
  | zero => exact suppIcc_mono h (by simp) (by simp)
  | succ r ih =>
    by_cases hr : Even r
    · rw [altOp_succ_of_even 𝒢 q 𝔉 k ζ hr]
      exact suppIcc_mono (suppIcc_physAdj 𝔉 k ζ ih) (le_of_eq (by push_cast; ring))
        (le_of_eq (by push_cast; ring))
    · rw [altOp_succ_of_not_even 𝒢 q 𝔉 k ζ hr]
      exact suppIcc_mono (suppIcc_physOp 𝔉 k ζ ih) (le_of_eq (by push_cast; ring))
        (le_of_eq (by push_cast; ring))

/-- **One step of adjointness**: a factor is moved from the left argument to the right one. -/
theorem gp_altOp_succ {i j : ℕ} (hij : Even i ↔ ¬Even j) {u v : PState intPos 𝒢 J ℓ → ℂ}
    {a b a' b' : ℤ} (hu : SuppIcc u a b) (hv : SuppIcc v a' b') :
    gp intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ (i + 1) u) (altOp 𝒢 q 𝔉 k ζ j v) =
      gp intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ i u) (altOp 𝒢 q 𝔉 k ζ (j + 1) v) := by
  by_cases hi : Even i
  · have hj : ¬Even j := hij.mp hi
    rw [altOp_succ_of_even 𝒢 q 𝔉 k ζ hi, altOp_succ_of_not_even 𝒢 q 𝔉 k ζ hj]
    exact (gp_physOp_int 𝔉 k ζ (suppIcc_altOp 𝒢 q 𝔉 k ζ i hu) _).symm
  · have hj : Even j := by
      by_contra hj
      exact hi (hij.mpr hj)
    rw [altOp_succ_of_not_even 𝒢 q 𝔉 k ζ hi, altOp_succ_of_even 𝒢 q 𝔉 k ζ hj]
    exact gp_physOp_left_int 𝔉 k ζ (suppIcc_altOp 𝒢 q 𝔉 k ζ j hv) _

/-- **`⟨altOp i u, altOp j v⟩ = ⟨u, altOp (i + j) v⟩`** when `i` and `j` have the same parity. -/
theorem gp_altOp_altOp (i : ℕ) : ∀ j : ℕ, (Even i ↔ Even j) →
    ∀ {u v : PState intPos 𝒢 J ℓ → ℂ} {a b a' b' : ℤ}, SuppIcc u a b → SuppIcc v a' b' →
      gp intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ i u) (altOp 𝒢 q 𝔉 k ζ j v) =
        gp intPos 𝒢 J ℓ u (altOp 𝒢 q 𝔉 k ζ (i + j) v) := by
  induction i with
  | zero =>
    intro j _ u v a b a' b' _ _
    rw [Nat.zero_add, altOp_zero_apply]
  | succ i ih =>
    intro j hij u v a b a' b' hu hv
    have h1 : Even i ↔ ¬Even j := by rw [← hij, Nat.even_add_one, not_not]
    have h2 : Even i ↔ Even (j + 1) := by
      rw [Nat.even_add_one]
      exact h1
    have e : i + 1 + j = i + (j + 1) := by omega
    rw [e, gp_altOp_succ 𝒢 q 𝔉 k ζ h1 hu hv]
    exact ih (j + 1) h2 hu hv

/-- **`‖altOp R u‖² = ⟨u, (𝒜 𝒜*)^R u⟩`**. In particular the moments are nonnegative. -/
theorem gsq_altOp_eq_gp (R : ℕ) {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (hu : SuppIcc u a b) :
    (gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ R u) : ℂ) =
      gp intPos 𝒢 J ℓ u
        (((physOp intPos 𝒢 q 𝔉 k ζ * physAdj intPos 𝒢 q 𝔉 k ζ) ^ R) u) := by
  rw [← gp_self_int (suppIcc_altOp 𝒢 q 𝔉 k ζ R hu),
    gp_altOp_altOp 𝒢 q 𝔉 k ζ R R Iff.rfl hu hu, ← two_mul, altOp_two_mul]

/-- **The moment of (eq:transference-moment) is a squared norm**:
`⟨u_n, (𝒜 𝒜*)^R u_n⟩ = ‖altOp R u_n‖²`. -/
theorem physMoment_eq_gsq (R : ℕ) (n : ℤ) :
    physMoment intPos 𝒢 q 𝔉 k ζ R n =
      gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ R (physUnit intPos 𝒢 J ℓ n)) := by
  have h := gsq_altOp_eq_gp 𝒢 q 𝔉 k ζ R (suppIcc_physUnit (𝒢 := 𝒢) (J := J) (ℓ := ℓ) n)
  rw [gp_physUnit_left (𝔭 := intPos) n] at h
  unfold physMoment
  rw [← h, Complex.ofReal_re]

/-- The moments are nonnegative. -/
theorem physMoment_nonneg (R : ℕ) (n : ℤ) : 0 ≤ physMoment intPos 𝒢 q 𝔉 k ζ R n := by
  rw [physMoment_eq_gsq]
  exact gsq_nonneg_int (suppIcc_altOp 𝒢 q 𝔉 k ζ R (suppIcc_physUnit n))

/-- **Log-convexity of the moments**: `a_{r+1}² ≤ a_r a_{r+2}` for `a_r = ‖altOp r u‖²`,
by `‖altOp (r+1) u‖² = ⟨altOp r u, altOp (r+2) u⟩` and Cauchy–Schwarz. -/
theorem gsq_altOp_sq_le (r : ℕ) {u : PState intPos 𝒢 J ℓ → ℂ} {a b : ℤ} (hu : SuppIcc u a b) :
    gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ (r + 1) u) ^ 2 ≤
      gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ r u) *
        gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ (r + 1 + 1) u) := by
  have h1 : (gsq intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ (r + 1) u) : ℂ) =
      gp intPos 𝒢 J ℓ (altOp 𝒢 q 𝔉 k ζ r u) (altOp 𝒢 q 𝔉 k ζ (r + 1 + 1) u) := by
    rw [← gp_self_int (suppIcc_altOp 𝒢 q 𝔉 k ζ (r + 1) hu)]
    exact gp_altOp_succ 𝒢 q 𝔉 k ζ (by rw [Nat.even_add_one, not_not]) hu hu
  have h2 := norm_gp_sq_le (suppIcc_altOp 𝒢 q 𝔉 k ζ r hu)
    (suppIcc_altOp 𝒢 q 𝔉 k ζ (r + 1 + 1) hu)
  rw [← h1, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h2
  exact h2

end Alt

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing
