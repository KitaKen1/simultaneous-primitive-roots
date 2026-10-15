module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Resample
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The character estimate under a cell restriction (eq:ideal-character-cell)

Source: `verification/stage7-sources/S-03.tex`, lines 208–241 (`[S-03:0208–0241]`).

`characterCell_of_reciprocal : ReciprocalPrimeCharacterSum → CharacterCell`: for distinct members
`χ, χ'` of `𝒞_Q`, `|E[1_{log D ∈ I_j} conj(χ(D)) χ'(D)]| ≤ L^{-D_*}` for all large `x`.

"To see this, hold all but one label fixed. The cell and the selected prime group restrict the
remaining prime to an interval, possibly empty. The character `conj(χ) χ'` on the common modulus
is nonprincipal: otherwise the uniqueness of primitive induction would imply `χ = χ'`. Its modulus
is at most `Q²`. … Partial summation on any subinterval of `[y, exp(L^d)]` bounds its
reciprocal-prime sum … Divide by `V_g ≥ v₋` and choose `K` sufficiently large in terms of `D_*`.
Averaging the other labels proves (eq:ideal-character-cell); its precision is independent of the
width or location of the interval."

* `Cell.logCell_mono`, `Cell.exists_Icc_eq` — the primes `p` of an interval of primes with
  `log(pR)` in one cell are the primes of an interval of integers.
* `Cell.commonChar`, `Cell.commonChar_ne_one` — `conj(χ) χ'` on the modulus `r r'`; it is
  nonprincipal for distinct pairs `(r, χ) ≠ (r', χ')` of primitive characters, because the conductor
  is invariant under change of level (`DirichletCharacter.conductor_changeLevel`).
* `Cell.norm_oneLabel_le` — one label varying: the sum is `V_g⁻¹ conj(χ(R)) χ'(R)` times a
  reciprocal prime sum of `conj(χ) χ'` over an interval.
* `characterCell_of_reciprocal` — the choice `K = (max(D_*, 0) + 1)/c`, `C = 2 q_*/c + 1` and
  `y = exp(L^c)`, and the average over the other labels (`Resample.norm_sum_le_of_slices`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Cell

/-! ### Log cells -/

/-- The index of the log cell is monotone. -/
theorem logCell_mono {h : ℝ} (hh : 0 < h) {D D' : ℕ} (hD : 0 < D) (hle : D ≤ D') :
    logCell h D ≤ logCell h D' := by
  unfold logCell
  have h1 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have h2 : (D : ℝ) ≤ (D' : ℝ) := by exact_mod_cast hle
  exact Int.floor_le_floor (div_le_div_of_nonneg_right (Real.log_le_log h1 h2) hh.le)

/-- "The cell and the selected prime group restrict the remaining prime to an interval"
[S-03:0217–0218]: the primes `p` of an interval of primes with `log(pR) ∈ I_j` are the primes of
an interval of integers whose left end is one of them. -/
theorem exists_Icc_eq {s : Finset ℕ} (hs : IsPrimeInterval s) {h : ℝ} (hh : 0 < h) (j : ℤ)
    {R : ℕ} (hR : 0 < R) (hne : (s.filter fun p => logCell h (p * R) = j).Nonempty) :
    ∃ lo hi : ℕ, lo ∈ s ∧
      (s.filter fun p => logCell h (p * R) = j) = (Finset.Icc lo hi).filter Nat.Prime := by
  obtain ⟨a, b, hab⟩ := hs
  obtain ⟨hlos, hloc⟩ := Finset.mem_filter.mp (Finset.min'_mem _ hne)
  obtain ⟨hhis, hhic⟩ := Finset.mem_filter.mp (Finset.max'_mem _ hne)
  refine ⟨(s.filter fun p => logCell h (p * R) = j).min' hne,
    (s.filter fun p => logCell h (p * R) = j).max' hne, hlos, ?_⟩
  ext q
  constructor
  · intro hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Finset.min'_le _ q hq, Finset.le_max' _ q hq⟩,
      ((hab q).mp (Finset.mem_filter.mp hq).1).1⟩
  · intro hq
    obtain ⟨hqI, hqp⟩ := Finset.mem_filter.mp hq
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hqI
    have hqs : q ∈ s :=
      (hab q).mpr ⟨hqp, ((hab _).mp hlos).2.1.trans h1, h2.trans ((hab _).mp hhis).2.2⟩
    refine Finset.mem_filter.mpr ⟨hqs, le_antisymm ?_ ?_⟩
    · exact (logCell_mono hh (Nat.mul_pos hqp.pos hR) (Nat.mul_le_mul_right R h2)).trans
        (le_of_eq hhic)
    · exact (le_of_eq hloc.symm).trans
        (logCell_mono hh (Nat.mul_pos ((hab _).mp hlos).1.pos hR) (Nat.mul_le_mul_right R h1))

/-! ### The character `conj(χ) χ'` -/

section Characters

variable {r₁ r₂ : ℕ}

/-- `conj(χ(D)) χ'(D)` for a positive integer `D`. -/
def pairChar (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (D : ℕ) : ℂ :=
  conj (χ₁ ((D : ℕ) : ZMod r₁)) * χ₂ ((D : ℕ) : ZMod r₂)

theorem pairChar_mul (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (a b : ℕ) :
    pairChar χ₁ χ₂ (a * b) = pairChar χ₁ χ₂ a * pairChar χ₁ χ₂ b := by
  simp only [pairChar, Nat.cast_mul, map_mul]
  ring

theorem norm_pairChar_le (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (D : ℕ) :
    ‖pairChar χ₁ χ₂ D‖ ≤ 1 := by
  unfold pairChar
  rw [norm_mul, Complex.norm_conj]
  calc ‖χ₁ ((D : ℕ) : ZMod r₁)‖ * ‖χ₂ ((D : ℕ) : ZMod r₂)‖ ≤ 1 * 1 :=
        mul_le_mul (χ₁.norm_le_one _) (χ₂.norm_le_one _) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- "The character `conj(χ) χ'` on the common modulus" [S-03:0219–0220]: the modulus is `r r'`. -/
def commonChar (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) :
    DirichletCharacter ℂ (r₁ * r₂) :=
  (DirichletCharacter.changeLevel (Nat.dvd_mul_right r₁ r₂) χ₁)⁻¹ *
    DirichletCharacter.changeLevel (Nat.dvd_mul_left r₂ r₁) χ₂

/-- On the integers prime to `r r'` the character on the common modulus is `conj(χ) χ'`. -/
theorem commonChar_apply (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (χ₁ : DirichletCharacter ℂ r₁)
    (χ₂ : DirichletCharacter ℂ r₂) {p : ℕ} (hp : Nat.Coprime p (r₁ * r₂)) :
    commonChar χ₁ χ₂ ((p : ℕ) : ZMod (r₁ * r₂)) = pairChar χ₁ χ₂ p := by
  have hN : NeZero (r₁ * r₂) := ⟨Nat.mul_ne_zero hr₁.ne' hr₂.ne'⟩
  have hcop : IsCoprime (p : ℤ) ((r₁ * r₂ : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hp
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₁ (Nat.dvd_mul_right r₁ r₂) hcop
  have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₂ (Nat.dvd_mul_left r₂ r₁) hcop
  rw [Int.cast_natCast, Int.cast_natCast] at h1 h2
  unfold commonChar pairChar
  rw [MulChar.mul_apply, ← MulChar.star_apply']
  exact congrArg₂ (· * ·) (congrArg star h1) h2

/-- **Uniqueness of primitive induction** [S-03:0219–0222]: "the character `conj(χ) χ'` on the
common modulus is nonprincipal: otherwise the uniqueness of primitive induction would imply
`χ = χ'`." Here: if the two lifts to the modulus `r r'` agree, the conductors agree, so `r = r'`,
and the lift is injective. -/
theorem commonChar_ne_one (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) {χ₁ : DirichletCharacter ℂ r₁}
    {χ₂ : DirichletCharacter ℂ r₂} (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (hne : (⟨r₁, χ₁⟩ : Σ r : ℕ, DirichletCharacter ℂ r) ≠ ⟨r₂, χ₂⟩) :
    commonChar χ₁ χ₂ ≠ 1 := by
  intro h
  unfold commonChar at h
  have hN : NeZero (r₁ * r₂) := ⟨Nat.mul_ne_zero hr₁.ne' hr₂.ne'⟩
  have heq : DirichletCharacter.changeLevel (Nat.dvd_mul_right r₁ r₂) χ₁ =
      DirichletCharacter.changeLevel (Nat.dvd_mul_left r₂ r₁) χ₂ := inv_mul_eq_one.mp h
  have hc₁ := DirichletCharacter.conductor_changeLevel χ₁ (Nat.dvd_mul_right r₁ r₂)
  have hc₂ := DirichletCharacter.conductor_changeLevel χ₂ (Nat.dvd_mul_left r₂ r₁)
  rw [heq, hc₂] at hc₁
  have e₁ : χ₁.conductor = r₁ := h₁
  have e₂ : χ₂.conductor = r₂ := h₂
  have hr : r₁ = r₂ := e₁.symm.trans (hc₁.symm.trans e₂)
  subst hr
  have hχ : χ₁ = χ₂ := DirichletCharacter.changeLevel_injective (Nat.dvd_mul_right r₁ r₁) heq
  exact hne (congrArg (Sigma.mk r₁) hχ)

end Characters

/-! ### One label varying -/

section OneLabel

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] {r₁ r₂ : ℕ}

/-- **One label varying and all other labels fixed** [S-03:0216–0239]: the sum over the label
`p` of the group `g₀`, with `R` the product of the other labels, is `V_g⁻¹ conj(χ(R)) χ'(R)`
times the reciprocal prime sum of `conj(χ) χ'` over the primes of an interval. -/
theorem norm_oneLabel_le (𝔊 : PrimeGroups P x S B) (g₀ : B) (hint : IsPrimeInterval (𝔊.big g₀))
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hcop : ∀ p ∈ 𝔊.big g₀, Nat.Coprime p (r₁ * r₂)) {y δ : ℝ} (hδ0 : 0 ≤ δ)
    (hy : ∀ p ∈ 𝔊.big g₀, y ≤ (p : ℝ))
    (hδ : ∀ lo hi : ℕ, y ≤ (lo : ℝ) →
      ‖∑ p ∈ (Finset.Icc lo hi).filter Nat.Prime,
        commonChar χ₁ χ₂ ((p : ℕ) : ZMod (r₁ * r₂)) / (p : ℂ)‖ ≤ δ)
    {h : ℝ} (hh : 0 < h) (j : ℤ) {R : ℕ} (hR : 0 < R) :
    ‖∑ p : {p : ℕ // p ∈ 𝔊.big g₀}, ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
        (if logCell h ((p : ℕ) * R) = j then pairChar χ₁ χ₂ ((p : ℕ) * R) else 0)‖ ≤
      δ / P.vMinus := by
  have hV : 0 < Graph.primeGroupReciprocalMass (𝔊.big g₀) :=
    lt_of_lt_of_le P.vMinus_pos (𝔊.mass_big_ge g₀)
  have hsum : ∑ p : {p : ℕ // p ∈ 𝔊.big g₀}, ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
        (if logCell h ((p : ℕ) * R) = j then pairChar χ₁ χ₂ ((p : ℕ) * R) else 0) =
      ((Graph.primeGroupReciprocalMass (𝔊.big g₀) : ℝ) : ℂ)⁻¹ * pairChar χ₁ χ₂ R *
        ∑ p ∈ (𝔊.big g₀).filter (fun p => logCell h (p * R) = j),
          commonChar χ₁ χ₂ ((p : ℕ) : ZMod (r₁ * r₂)) / (p : ℂ) := by
    rw [Finset.sum_coe_sort (𝔊.big g₀) (fun p => ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
      (if logCell h (p * R) = j then pairChar χ₁ χ₂ (p * R) else 0)), Finset.mul_sum,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    by_cases hc : logCell h (p * R) = j
    · rw [if_pos hc, if_pos hc, pairChar_mul,
        commonChar_apply hr₁ hr₂ χ₁ χ₂ (hcop p hp)]
      unfold Graph.primeGroupLaw
      push_cast
      ring
    · rw [if_neg hc, if_neg hc, mul_zero]
  have hT : ‖∑ p ∈ (𝔊.big g₀).filter (fun p => logCell h (p * R) = j),
      commonChar χ₁ χ₂ ((p : ℕ) : ZMod (r₁ * r₂)) / (p : ℂ)‖ ≤ δ := by
    rcases ((𝔊.big g₀).filter (fun p => logCell h (p * R) = j)).eq_empty_or_nonempty with
      he | hne
    · rw [he, Finset.sum_empty, norm_zero]
      exact hδ0
    · obtain ⟨lo, hi, hlo, heq⟩ := exists_Icc_eq hint hh j hR hne
      rw [heq]
      exact hδ lo hi (hy lo hlo)
  have hvinv : 0 ≤ P.vMinus⁻¹ := inv_nonneg.mpr P.vMinus_pos.le
  rw [hsum, norm_mul, norm_mul, norm_inv, Complex.norm_of_nonneg hV.le]
  calc (Graph.primeGroupReciprocalMass (𝔊.big g₀))⁻¹ * ‖pairChar χ₁ χ₂ R‖ *
        ‖∑ p ∈ (𝔊.big g₀).filter (fun p => logCell h (p * R) = j),
          commonChar χ₁ χ₂ ((p : ℕ) : ZMod (r₁ * r₂)) / (p : ℂ)‖
      ≤ P.vMinus⁻¹ * 1 * δ :=
        mul_le_mul (mul_le_mul (inv_anti₀ P.vMinus_pos (𝔊.mass_big_ge g₀))
          (norm_pairChar_le χ₁ χ₂ R) (norm_nonneg _) hvinv) hT (norm_nonneg _)
          (mul_nonneg hvinv zero_le_one)
    _ = δ / P.vMinus := by rw [mul_one, div_eq_inv_mul]

end OneLabel

end Cell

/-! ### The estimate -/

/-- **The character estimate under a cell restriction (eq:ideal-character-cell)**
[S-03:0208–0241], from the reciprocal prime sums of nonprincipal characters. -/
theorem characterCell_of_reciprocal (hrec : ReciprocalPrimeCharacterSum) : CharacterCell := by
  intro P m qs Dstar hqs
  have hc : 0 < P.c := c_pos P
  have hK : 0 < (max Dstar 0 + 1) / P.c :=
    div_pos (by linarith [le_max_right Dstar 0]) hc
  have hC : 0 < 2 * qs / P.c + 1 := by
    have h0 : 0 ≤ 2 * qs / P.c := div_nonneg (mul_nonneg zero_le_two hqs) hc.le
    linarith
  obtain ⟨M, y₀, hM⟩ := hrec ((max Dstar 0 + 1) / P.c) (2 * qs / P.c + 1) hK hC
  obtain ⟨L₁, -, hL₁'⟩ := exists_rpow_le_sourcePrimeLowerBound P.c hc 1
  obtain ⟨x₂, hscale⟩ := scaleLowerBound P (qs + 1)
  refine ⟨max x₂ (Real.exp (max (max L₁ 2) (max y₀ (max M 0 / P.vMinus)))), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 hint J Λ hne _ h hh j r₁ r₂ χ₁ χ₂ hr₁ hr₁Q hr₂ hr₂Q hprim₁ hprim₂
    hdist
  have hx₂ : x₂ ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp (max (max L₁ 2) (max y₀ (max M 0 / P.vMinus))) ≤ x :=
    (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hLbig : max (max L₁ 2) (max y₀ (max M 0 / P.vMinus)) ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).mpr hxe
  have hLL₁ : L₁ ≤ Real.log x := (le_max_left _ _).trans ((le_max_left _ _).trans hLbig)
  have hL2 : 2 ≤ Real.log x := (le_max_right _ _).trans ((le_max_left _ _).trans hLbig)
  have hLy : y₀ ≤ Real.log x := (le_max_left _ _).trans ((le_max_right _ _).trans hLbig)
  have hLM : max M 0 / P.vMinus ≤ Real.log x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hLbig)
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  -- the scale `y = exp(L^c)`
  have hyL : Real.log x ≤ Graph.sourcePrimeLowerBound P.c (Real.log x) := by
    have h1 := hL₁' _ hLL₁
    rwa [Real.rpow_one] at h1
  have hy₀ : y₀ ≤ Graph.sourcePrimeLowerBound P.c (Real.log x) := hLy.trans hyL
  have hlogy : Real.log (Graph.sourcePrimeLowerBound P.c (Real.log x)) = Real.log x ^ P.c := by
    unfold Graph.sourcePrimeLowerBound
    exact Real.log_exp _
  -- the big primes exceed `Q`, hence are prime to the moduli
  have hQ0 : 0 < Real.log x ^ qs := Real.rpow_pos_of_pos hL0 _
  have hbig : ∀ (g : B) (p : ℕ), p ∈ 𝔊.big g → Real.log x ^ qs < (p : ℝ) := by
    intro g p hp
    have h1 := (hscale x hx₂ S B 𝔊).1 g p hp
    rw [Real.rpow_add_one hL0.ne'] at h1
    have h2 : Real.log x ^ qs * 2 ≤ Real.log x ^ qs * Real.log x :=
      mul_le_mul_of_nonneg_left hL2 hQ0.le
    linarith
  have hcopr : ∀ (g : B) (p : ℕ), p ∈ 𝔊.big g → ∀ r : ℕ, 0 < r →
      (r : ℝ) ≤ Real.log x ^ qs → Nat.Coprime p r := by
    intro g p hp r hr hrQ
    have hlt : r < p := by
      have h1 : (r : ℝ) < (p : ℝ) := lt_of_le_of_lt hrQ (hbig g p hp)
      exact_mod_cast h1
    exact ((𝔊.prime_big g p hp).coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hr hlt)
  obtain ⟨g₀, i, hi⟩ := hne
  have hcop : ∀ p ∈ 𝔊.big g₀, Nat.Coprime p (r₁ * r₂) := fun p hp =>
    Nat.Coprime.mul_right (hcopr g₀ p hp r₁ hr₁ hr₁Q) (hcopr g₀ p hp r₂ hr₂ hr₂Q)
  -- the modulus is at most `(log y)^C`
  have hN0 : 0 < r₁ * r₂ := Nat.mul_pos hr₁ hr₂
  have h4a : P.c * (2 * qs / P.c) = 2 * qs := by field_simp
  have h4b : P.c * ((max Dstar 0 + 1) / P.c) = max Dstar 0 + 1 := by field_simp
  have hNle : ((r₁ * r₂ : ℕ) : ℝ) ≤
      Real.log (Graph.sourcePrimeLowerBound P.c (Real.log x)) ^ (2 * qs / P.c + 1) := by
    rw [hlogy, ← Real.rpow_mul hL0.le, mul_add, mul_one, h4a]
    have h1 : ((r₁ * r₂ : ℕ) : ℝ) ≤ Real.log x ^ qs * Real.log x ^ qs := by
      push_cast
      exact mul_le_mul hr₁Q hr₂Q (Nat.cast_nonneg _) hQ0.le
    have h2 : Real.log x ^ qs * Real.log x ^ qs = Real.log x ^ (qs + qs) :=
      (Real.rpow_add hL0 qs qs).symm
    have h3 : Real.log x ^ (qs + qs) ≤ Real.log x ^ (2 * qs + P.c) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    linarith
  have hKpow : Real.log (Graph.sourcePrimeLowerBound P.c (Real.log x)) ^
      (-((max Dstar 0 + 1) / P.c)) = Real.log x ^ (-(max Dstar 0 + 1)) := by
    rw [hlogy, ← Real.rpow_mul hL0.le, mul_neg, h4b]
  -- the bound for the reciprocal prime sums
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀ : ℝ, δ₀ = max M 0 * Real.log x ^ (-(max Dstar 0 + 1)) := ⟨_, rfl⟩
  have hpow0 : 0 ≤ Real.log x ^ (-(max Dstar 0 + 1)) := Real.rpow_nonneg hL0.le _
  have hδ₀0 : 0 ≤ δ₀ := by
    rw [hδ₀def]
    exact mul_nonneg (le_max_right _ _) hpow0
  have hδ : ∀ lo hi : ℕ, Graph.sourcePrimeLowerBound P.c (Real.log x) ≤ (lo : ℝ) →
      ‖∑ p ∈ (Finset.Icc lo hi).filter Nat.Prime,
        Cell.commonChar χ₁ χ₂ ((p : ℕ) : ZMod (r₁ * r₂)) / (p : ℂ)‖ ≤ δ₀ := by
    intro lo hi hlo
    have h1 := hM _ hy₀ (r₁ * r₂) hN0 hNle (Cell.commonChar χ₁ χ₂)
      (Cell.commonChar_ne_one hr₁ hr₂ hprim₁ hprim₂ hdist) lo hi hlo
    rw [hKpow] at h1
    rw [hδ₀def]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0)
  -- one label varying
  have hslice : ∀ (t : AuxList 𝔊.big Λ)
      (u : {i : Fin J // i ∈ Λ g₀} → {p : ℕ // p ∈ 𝔊.big g₀}),
      ‖∑ p : {p : ℕ // p ∈ 𝔊.big g₀}, ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
        (if logCell h (tupleProd Λ (Function.update t g₀ (Function.update u ⟨i, hi⟩ p))) = j then
          Cell.pairChar χ₁ χ₂
            (tupleProd Λ (Function.update t g₀ (Function.update u ⟨i, hi⟩ p))) else 0)‖ ≤
        δ₀ / P.vMinus := by
    intro t u
    have hR : 0 < (∏ i' ∈ Finset.univ.erase (⟨i, hi⟩ : {i : Fin J // i ∈ Λ g₀}), (u i' : ℕ)) *
        ∏ g ∈ Finset.univ.erase g₀, ∏ i' : {i : Fin J // i ∈ Λ g}, (t g i' : ℕ) :=
      Nat.mul_pos (Finset.prod_pos fun i' _ => (𝔊.prime_big g₀ (u i') (u i').2).pos)
        (Finset.prod_pos fun g _ => Finset.prod_pos fun i' _ =>
          (𝔊.prime_big g (t g i') (t g i').2).pos)
    have h5 := Cell.norm_oneLabel_le 𝔊 g₀ (hint g₀) hr₁ hr₂ χ₁ χ₂ hcop hδ₀0 (𝔊.big_ge g₀) hδ hh j
      hR
    have h6 : ∀ p : {p : ℕ // p ∈ 𝔊.big g₀},
        ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
          (if logCell h (tupleProd Λ (Function.update t g₀ (Function.update u ⟨i, hi⟩ p))) = j
            then Cell.pairChar χ₁ χ₂
              (tupleProd Λ (Function.update t g₀ (Function.update u ⟨i, hi⟩ p))) else 0) =
        ((Graph.primeGroupLaw (𝔊.big g₀) p : ℝ) : ℂ) *
          (if logCell h ((p : ℕ) *
              ((∏ i' ∈ Finset.univ.erase (⟨i, hi⟩ : {i : Fin J // i ∈ Λ g₀}), (u i' : ℕ)) *
                ∏ g ∈ Finset.univ.erase g₀, ∏ i' : {i : Fin J // i ∈ Λ g}, (t g i' : ℕ))) = j
            then Cell.pairChar χ₁ χ₂ ((p : ℕ) *
              ((∏ i' ∈ Finset.univ.erase (⟨i, hi⟩ : {i : Fin J // i ∈ Λ g₀}), (u i' : ℕ)) *
                ∏ g ∈ Finset.univ.erase g₀, ∏ i' : {i : Fin J // i ∈ Λ g}, (t g i' : ℕ)))
            else 0) := fun p => by
      rw [Resample.tupleProd_update Λ t g₀ u ⟨i, hi⟩ p]
    rw [Finset.sum_congr rfl fun p _ => h6 p]
    exact h5
  -- the statement in the form `E[F]`
  have hrew : (∑ t : AuxList 𝔊.big Λ, if logCell h (tupleProd Λ t) = j then
        (auxWeight 𝔊.big Λ t : ℂ) *
          (conj (χ₁ ((tupleProd Λ t : ℕ) : ZMod r₁)) * χ₂ ((tupleProd Λ t : ℕ) : ZMod r₂))
      else 0) =
      ∑ t : AuxList 𝔊.big Λ, ((auxWeight 𝔊.big Λ t : ℝ) : ℂ) *
        (if logCell h (tupleProd Λ t) = j then Cell.pairChar χ₁ χ₂ (tupleProd Λ t) else 0) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hcell : logCell h (tupleProd Λ t) = j
    · rw [if_pos hcell, if_pos hcell]
      rfl
    · rw [if_neg hcell, if_neg hcell, mul_zero]
  have hfinal : δ₀ / P.vMinus ≤ Real.log x ^ (-Dstar) := by
    rw [hδ₀def]
    have h1 : max M 0 * Real.log x ^ (-(max Dstar 0 + 1)) / P.vMinus =
        max M 0 / P.vMinus * Real.log x ^ (-(max Dstar 0 + 1)) := by ring
    rw [h1]
    calc max M 0 / P.vMinus * Real.log x ^ (-(max Dstar 0 + 1))
        ≤ Real.log x * Real.log x ^ (-(max Dstar 0 + 1)) :=
          mul_le_mul_of_nonneg_right hLM hpow0
      _ = Real.log x ^ (-(max Dstar 0 + 1) + 1) := by
          rw [Real.rpow_add_one hL0.ne']
          ring
      _ ≤ Real.log x ^ (-Dstar) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [le_max_left Dstar 0])
  rw [hrew]
  exact (Resample.norm_sum_le_of_slices 𝔊 Λ g₀ ⟨i, hi⟩
    (fun t => if logCell h (tupleProd Λ t) = j then Cell.pairChar χ₁ χ₂ (tupleProd Λ t) else 0)
    (δ₀ / P.vMinus) hslice).trans hfinal

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
