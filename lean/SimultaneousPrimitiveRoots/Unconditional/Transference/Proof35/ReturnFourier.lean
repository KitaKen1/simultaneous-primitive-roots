module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueModel
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.PathExpansion
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The return condition: (eq:return-fourier)

Source: `verification/stage7-sources/S-02.tex`, lines 308–314 (`[S-02:0308–0314]`): "the return
condition is now imposed by the exact identity `1_{h_N = 0} = ∫_0^1 e(θ h_N) dθ`. It suffices to
bound the unrestricted signed path expression uniformly in `θ`."

`returnFourier : ReturnFourier` is proved here. The integral over `θ ∈ [0, 1]` is replaced by the
mean over `θ = j/Q`, `0 ≤ j < Q`, for an integer `Q` larger than every offset `|h_N|` of a walk:
`Q⁻¹ ∑_{j<Q} e(j h / Q) = 1_{h = 0}` for integers `|h| < Q` (`sum_expUnit_range`). The paths are
those of `PathExpansion.lean`; the offsets take finitely many values because there are finitely
many paths. A walk in `tagModel` which starts at `(0, y)` ends at `(h, y + h)`
(`walkEnd_tag_pos`), so it returns to its start exactly when `h = 0`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Roots of unity -/

/-- `Q⁻¹ ∑_{j<Q} e(j h / Q) = 1_{h = 0}` for an integer `h` which is zero or not divisible by
`Q`. -/
theorem sum_expUnit_range (Q : ℕ) (hQ : 0 < Q) (h : ℤ) (hh : h ≠ 0 → ¬((Q : ℤ) ∣ h)) :
    ∑ j ∈ Finset.range Q, expUnit ((j : ℝ) / (Q : ℝ) * (h : ℝ)) =
      if h = 0 then (Q : ℂ) else 0 := by
  by_cases h0 : h = 0
  · subst h0
    simp [expUnit]
  · rw [if_neg h0]
    obtain ⟨z, hz⟩ : ∃ z : ℂ, z = 2 * Real.pi * Complex.I * (((h : ℝ) / (Q : ℝ) : ℝ) : ℂ) :=
      ⟨_, rfl⟩
    have hQc : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
    have hQr : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
    have hterm : ∀ j : ℕ, expUnit ((j : ℝ) / (Q : ℝ) * (h : ℝ)) = Complex.exp z ^ j := by
      intro j
      rw [← Complex.exp_nat_mul]
      unfold expUnit
      congr 1
      rw [hz]
      push_cast
      ring
    have hpow : Complex.exp z ^ Q = 1 := by
      rw [← Complex.exp_nat_mul]
      have e : (Q : ℂ) * z = (h : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hz]
        push_cast
        field_simp
      rw [e]
      exact Complex.exp_int_mul_two_pi_mul_I h
    have hne : Complex.exp z ≠ 1 := by
      intro h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero
      have hc : (((h : ℝ) / (Q : ℝ) : ℝ) : ℂ) = (n : ℂ) := by
        have e : (((h : ℝ) / (Q : ℝ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I) =
            (n : ℂ) * (2 * Real.pi * Complex.I) := by
          rw [← hn, hz]
          ring
        exact mul_right_cancel₀ h2pi e
      have hr : (h : ℝ) / (Q : ℝ) = (n : ℝ) := by exact_mod_cast hc
      have hr' : (h : ℝ) = (n : ℝ) * (Q : ℝ) := (div_eq_iff hQr).mp hr
      have hi : h = n * (Q : ℤ) := by exact_mod_cast hr'
      exact hh h0 ⟨n, by rw [hi]; ring⟩
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    have hgeom := geom_sum_mul (Complex.exp z) Q
    rw [hpow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

/-! ### Walks in the residue model with offsets -/

section Tag

variable {Q : Finset ℕ}

theorem tagModel_shift_zero (n : ℤ × ResVec Q) : (tagModel Q).shift 0 n = n := by
  refine Prod.ext ?_ ?_
  · show n.1 + 0 = n.1
    rw [add_zero]
  · funext p
    show n.2 p + ((0 : ℤ) : Res p.1) = n.2 p
    rw [Int.cast_zero, add_zero]

theorem tagModel_shift_shift (a b : ℤ) (n : ℤ × ResVec Q) :
    (tagModel Q).shift a ((tagModel Q).shift b n) = (tagModel Q).shift (b + a) n := by
  refine Prod.ext ?_ ?_
  · show n.1 + b + a = n.1 + (b + a)
    ring
  · funext p
    show n.2 p + (b : Res p.1) + (a : Res p.1) = n.2 p + ((b + a : ℤ) : Res p.1)
    push_cast
    ring

theorem tagOffset_shift_tagStart (y : ResVec Q) (d : ℤ) :
    tagOffset ((tagModel Q).shift d (tagStart y)) = d := by
  show (0 : ℤ) + d = d
  rw [zero_add]

theorem tagStart_shift_eq_iff (y : ResVec Q) (d : ℤ) :
    (tagModel Q).shift d (tagStart y) = tagStart y ↔ d = 0 := by
  constructor
  · intro h
    have h1 := congrArg tagOffset h
    rw [tagOffset_shift_tagStart] at h1
    exact h1
  · intro h
    subst h
    exact tagModel_shift_zero _

/-- A walk in `tagModel` whose steps are translations ends at a translate of its start. -/
theorem walkEnd_tag_pos {X Ξ : Type*}
    (tgt : (tagModel Q).Pos × X → Ξ → (tagModel Q).Pos × X)
    (htgt : ∀ s ξ, ∃ d : ℤ, (tgt s ξ).1 = (tagModel Q).shift d s.1) (w : List Ξ)
    (s : (tagModel Q).Pos × X) :
    ∃ d : ℤ, (walkEnd tgt s w).1 = (tagModel Q).shift d s.1 := by
  induction w generalizing s with
  | nil => exact ⟨0, (tagModel_shift_zero s.1).symm⟩
  | cons ξ w ih =>
    obtain ⟨d₁, h₁⟩ := htgt s ξ
    obtain ⟨d₂, h₂⟩ := ih (tgt s ξ)
    refine ⟨d₁ + d₂, ?_⟩
    show (walkEnd tgt (tgt s ξ) w).1 = _
    rw [h₂, h₁]
    exact tagModel_shift_shift d₂ d₁ s.1

end Tag

/-! ### The return condition -/

section Return

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  (𝒢 : GroupFamily S B) {J ℓ : ℕ} {N : Type} [Fintype N]

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A round of the physical walk in `tagModel` is a translation of the position. -/
theorem physRoundTgt_tag (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ)
    (s : PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ) (ξ : PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉) :
    ∃ d : ℤ, (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 𝔉 k s ξ).1 =
      (tagModel 𝒢.allPrimes).shift d s.1 :=
  ⟨_, tagModel_shift_shift
    (-(k * dil (𝔉 ξ.2.2.1.1).C
      (permuteLists ξ.2.1 (physFwdTgt (tagModel 𝒢.allPrimes) 𝒢 𝔉 k s ξ.1).2) ξ.2.2.1.2.1))
    (k * dil (𝔉 ξ.1.2.1.1).C (permuteLists ξ.1.1 s.2) ξ.1.2.1.2.1) s.1⟩

end Return

open _root_.Classical in
/-- **(eq:return-fourier), as it is used** [S-02:0308–0313], proved: if the unrestricted signed
path expression `phaseSum θ` has modulus at most `ε` for every real `θ`, then the moment of the
independent residue model with the return condition has modulus at most `ε`. -/
theorem returnFourier : ReturnFourier := by
  intro S B _ _ _ _ 𝒢 q J ℓ N _ 𝔉 k ζ R ε hε
  -- an integer larger than every offset of a walk
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = 1 +
      ∑ t : ResVec 𝒢.allPrimes × Lists 𝒢 J ℓ × (Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉),
        (tagOffset (walkEnd (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 𝔉 k)
          (tagStart t.1, t.2.1) (List.ofFn t.2.2)).1).natAbs := ⟨_, rfl⟩
  have hQpos : 0 < Q := by
    rw [hQdef]
    omega
  have hQbig : ∀ (y : ResVec 𝒢.allPrimes) (x : Lists 𝒢 J ℓ)
      (w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉),
      (tagOffset (walkEnd (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 𝔉 k)
        (tagStart y, x) (List.ofFn w)).1).natAbs < Q := by
    intro y x w
    have h := Finset.single_le_sum
      (f := fun t : ResVec 𝒢.allPrimes × Lists 𝒢 J ℓ ×
          (Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉) =>
        (tagOffset (walkEnd (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 𝔉 k)
          (tagStart t.1, t.2.1) (List.ofFn t.2.2)).1).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (y, x, w))
    rw [hQdef]
    exact Nat.lt_one_add_iff.mpr h
  -- the value at the end of one walk
  have hpt : ∀ (y : ResVec 𝒢.allPrimes) (x : Lists 𝒢 J ℓ)
      (w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉),
      (∑ j ∈ Finset.range Q, phaseVec 𝒢 ((j : ℝ) / (Q : ℝ))
          (walkEnd (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 𝔉 k)
            (tagStart y, x) (List.ofFn w))) =
        (Q : ℂ) * physUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y)
          (walkEnd (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 𝔉 k)
            (tagStart y, x) (List.ofFn w)) := by
    intro y x w
    obtain ⟨d, hd⟩ := walkEnd_tag_pos (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 𝔉 k)
      (physRoundTgt_tag 𝒢 𝔉 k) (List.ofFn w) (tagStart y, x)
    obtain ⟨E, hE⟩ : ∃ E : PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ,
        E = walkEnd (physRoundTgt (tagModel 𝒢.allPrimes) 𝒢 𝔉 k) (tagStart y, x)
          (List.ofFn w) := ⟨_, rfl⟩
    rw [← hE]
    rw [← hE] at hd
    have hoff : tagOffset E.1 = d := by
      rw [hd]
      exact tagOffset_shift_tagStart y d
    have hiff : E.1 = tagStart y ↔ d = 0 := by
      rw [hd]
      exact tagStart_shift_eq_iff y d
    have hdlt : d.natAbs < Q := by
      have := hQbig y x w
      rw [← hE, hoff] at this
      exact this
    have hnd : d ≠ 0 → ¬((Q : ℤ) ∣ d) := by
      intro hd0 hdvd
      have habs : |d| < (Q : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hdlt
      exact hd0 (Int.eq_zero_of_abs_lt_dvd hdvd habs)
    by_cases hp : IsPhys (tagModel 𝒢.allPrimes) E.1 E.2
    · have e1 : ∀ θ : ℝ, phaseVec 𝒢 θ E = expUnit (θ * (d : ℝ)) := by
        intro θ
        unfold phaseVec
        rw [if_pos hp, hoff]
      have e2 : physUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y) E =
          if d = 0 then 1 else 0 := by
        unfold physUnit
        by_cases hd0 : d = 0
        · rw [if_pos ⟨hiff.mpr hd0, hp⟩, if_pos hd0]
        · rw [if_neg (fun h => hd0 (hiff.mp h.1)), if_neg hd0]
      rw [Finset.sum_congr rfl fun j _ => e1 _, sum_expUnit_range Q hQpos d hnd, e2]
      split_ifs
      · rw [mul_one]
      · rw [mul_zero]
    · have e1 : ∀ θ : ℝ, phaseVec 𝒢 θ E = 0 := by
        intro θ
        unfold phaseVec
        rw [if_neg hp]
      have e2 : physUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y) E = 0 := by
        unfold physUnit
        rw [if_neg fun h => hp h.2]
      rw [Finset.sum_congr rfl fun j _ => e1 _, e2, Finset.sum_const_zero, mul_zero]
  -- one start position
  have hy : ∀ y : ResVec 𝒢.allPrimes,
      ∑ j ∈ Finset.range Q, pairUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y)
          (((physOp (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ *
              physAdj (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ) ^ R)
            (phaseVec 𝒢 ((j : ℝ) / (Q : ℝ)))) =
        (Q : ℂ) * pairUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y)
          (((physOp (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ *
              physAdj (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ) ^ R)
            (physUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y))) := by
    intro y
    rw [← pairUnit_sum, ← map_sum, ← pairUnit_smul, ← map_smul]
    refine pairUnit_pow_congr (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ R (tagStart y) _ _ fun x w => ?_
    rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hpt y x w
  -- the mean over the residues
  obtain ⟨Mc, hMc⟩ : ∃ Mc : ℂ, Mc = ((Fintype.card (ResVec 𝒢.allPrimes) : ℝ) : ℂ)⁻¹ *
      ∑ y : ResVec 𝒢.allPrimes, pairUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y)
        (((physOp (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ *
            physAdj (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ) ^ R)
          (physUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y))) := ⟨_, rfl⟩
  have hsum : ∑ j ∈ Finset.range Q, phaseSum 𝒢 q 𝔉 k ζ R ((j : ℝ) / (Q : ℝ)) = (Q : ℂ) * Mc := by
    unfold phaseSum
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun y _ => hy y,
      ← Finset.mul_sum, hMc]
    ring
  have hre : residueMoment 𝒢 q 𝔉 k ζ R = Mc.re := by
    unfold residueMoment resAvg physMoment
    rw [hMc, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
  have hnorm : ‖(Q : ℂ) * Mc‖ ≤ (Q : ℝ) * ε := by
    rw [← hsum]
    calc ‖∑ j ∈ Finset.range Q, phaseSum 𝒢 q 𝔉 k ζ R ((j : ℝ) / (Q : ℝ))‖
        ≤ ∑ j ∈ Finset.range Q, ‖phaseSum 𝒢 q 𝔉 k ζ R ((j : ℝ) / (Q : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range Q, ε := Finset.sum_le_sum fun j _ => hε _
      _ = (Q : ℝ) * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : ‖Mc‖ ≤ ε := by
    rw [norm_mul, Complex.norm_natCast] at hnorm
    exact le_of_mul_le_mul_left hnorm (Nat.cast_pos.mpr hQpos)
  rw [hre]
  exact (Complex.abs_re_le_norm Mc).trans hM

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
