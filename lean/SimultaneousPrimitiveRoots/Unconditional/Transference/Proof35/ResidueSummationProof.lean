module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueSumPath
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueSumMass
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ReturnFourier
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueReplacementProof
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The summation over paths: Lemma 3.6 implies the reduction to the residue model

Source: `verification/stage7-sources/S-02.tex`, lines 212–234 and 293–307
(`[S-02:0212–0234, 0293–0307]`).

"This replacement may be summed over paths with absolute coefficients. … By Lemma 3.4, the
absolute mass of all length `N` paths, even without a return condition, is `L^{O(N)}`. Taking `A`
sufficiently large in Lemma 3.6 makes the summed error smaller than `L^{-A'N}` for any desired
fixed `A'`. We may therefore use the independent residue model."

* `ResSum.abs_intAvg_sub_resAvg_le` — a linear combination of path factors: if every path factor
  satisfies the relative estimate of Lemma 3.6 with the constant `ε`, the two averages of the
  combination differ by at most `ε` times the expectation of the combination with absolute
  coefficients.
* `ResSum.moment_diff_le` — **the summation over paths** for one system of prime groups: if the
  estimate of Lemma 3.6 holds with `ε` for all label sets and offsets, and `ρ₁`, `ρ₂` bound the
  row sums of Lemma 3.4 in the residue model with offsets, then the averaged moment and the
  moment of the residue model differ by at most `ε (ρ₁ ρ₂)^R`. The paths, their amplitudes,
  offsets and label sets are those of `ResidueSumPath.lean`; the same for integer positions and
  for the residue model, because the position enters only through (eq:path-residue-factor). The
  return condition `h_N = 0` is part of the amplitude in both models.
* `residueSummation : ResidueSummation` and `residueReduction : ResidueReduction`. For
  `A' ` given, Lemma 3.6 is used with `A = max(A' + C_abs, 1)`, `C_abs = schurExponent P m C₁`:
  `exp(-A N T) · (L^{C_abs})^{2R} = L^{-(A - C_abs) N} ≤ L^{-A' N}`. The threshold is the one of
  Lemma 3.6 for `(P, J, γ, A)`, and `x ≥ e`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

namespace ResSum

/-! ### Linear combinations of path factors -/

theorem intAvg_double_sum {α β : Type*} [Fintype α] [Fintype β] (X : ℝ) (c : α → β → ℝ)
    (f : α → β → ℤ → ℝ) :
    intAvg X (fun n => ∑ x, ∑ w, c x w * f x w n) = ∑ x, ∑ w, c x w * intAvg X (f x w) := by
  unfold intAvg
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.mul_sum]
  ring

theorem resAvg_double_sum {α β : Type*} [Fintype α] [Fintype β] (Q : Finset ℕ) (c : α → β → ℝ)
    (f : α → β → ResVec Q → ℝ) :
    resAvg Q (fun y => ∑ x, ∑ w, c x w * f x w y) = ∑ x, ∑ w, c x w * resAvg Q (f x w) := by
  rw [resAvg_sum Q Finset.univ fun x y => ∑ w, c x w * f x w y]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [resAvg_sum Q Finset.univ fun w y => c x w * f x w y]
  exact Finset.sum_congr rfl fun w _ => resAvg_const_mul Q (c x w) (f x w)

/-- **A linear combination of path factors** [S-02:0293–0294]: "this replacement may be summed
over paths with absolute coefficients". -/
theorem abs_intAvg_sub_resAvg_le {α β : Type*} [Fintype α] [Fintype β] (Q : Finset ℕ) (q : ℝ)
    (n : ℕ) (a : α → β → ℝ) (Λ : α → β → ℕ → Finset ℕ) (h : α → β → ℕ → ℤ) {X ε Mass : ℝ}
    (hε : 0 ≤ ε) (F : ℤ → ℝ) (G : ResVec Q → ℝ)
    (hF : ∀ n', F n' = ∑ x, ∑ w, a x w * pathFactor intPos Q q n (Λ x w) (h x w) n')
    (hG : ∀ y, G y = ∑ x, ∑ w, a x w * pathFactor (resModel Q) Q q n (Λ x w) (h x w) y)
    (hrep : ∀ x w, |intAvg X (fun n' => pathFactor intPos Q q n (Λ x w) (h x w) n') -
        resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w))| ≤
      ε * resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w)))
    (habs : resAvg Q (fun y => ∑ x, ∑ w,
      |a x w| * pathFactor (resModel Q) Q q n (Λ x w) (h x w) y) ≤ Mass) :
    |intAvg X F - resAvg Q G| ≤ ε * Mass := by
  have hFavg : intAvg X F = ∑ x, ∑ w, a x w *
      intAvg X (fun n' => pathFactor intPos Q q n (Λ x w) (h x w) n') := by
    rw [funext hF]
    exact intAvg_double_sum X a fun x w n' => pathFactor intPos Q q n (Λ x w) (h x w) n'
  have hGavg : resAvg Q G = ∑ x, ∑ w, a x w *
      resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w)) := by
    rw [funext hG]
    exact resAvg_double_sum Q a fun x w => pathFactor (resModel Q) Q q n (Λ x w) (h x w)
  have habs' : ∑ x, ∑ w, |a x w| * resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w)) ≤
      Mass :=
    (resAvg_double_sum Q (fun x w => |a x w|)
      fun x w => pathFactor (resModel Q) Q q n (Λ x w) (h x w)).symm.trans_le habs
  have hterm : ∀ x w, |a x w * intAvg X (fun n' => pathFactor intPos Q q n (Λ x w) (h x w) n') -
      a x w * resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w))| ≤
      ε * (|a x w| * resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w))) := by
    intro x w
    rw [← mul_sub, abs_mul]
    calc |a x w| * |intAvg X (fun n' => pathFactor intPos Q q n (Λ x w) (h x w) n') -
          resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w))|
        ≤ |a x w| * (ε * resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w))) :=
          mul_le_mul_of_nonneg_left (hrep x w) (abs_nonneg _)
      _ = ε * (|a x w| * resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w))) := by ring
  rw [hFavg, hGavg, ← Finset.sum_sub_distrib]
  calc |∑ x, ((∑ w, a x w * intAvg X (fun n' => pathFactor intPos Q q n (Λ x w) (h x w) n')) -
        ∑ w, a x w * resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w)))|
      ≤ ∑ x, |(∑ w, a x w * intAvg X (fun n' => pathFactor intPos Q q n (Λ x w) (h x w) n')) -
        ∑ w, a x w * resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ w, ε * (|a x w| * resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w))) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => hterm x w)
    _ = ε * ∑ x, ∑ w, |a x w| * resAvg Q (pathFactor (resModel Q) Q q n (Λ x w) (h x w)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ε * Mass := mul_le_mul_of_nonneg_left habs' hε

/-! ### The summation over paths -/

theorem norm_physUnit_le_one {S B : Type} (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ)
    (n : 𝔭.Pos) (s : PState 𝔭 𝒢 J ℓ) : ‖physUnit 𝔭 𝒢 J ℓ n s‖ ≤ 1 := by
  unfold physUnit
  split_ifs
  · rw [norm_one]
  · rw [norm_zero]
    exact zero_le_one

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

open _root_.Classical in
/-- **The summation over paths** [S-02:0212–0234, 0293–0307], for one system of prime groups.
If the estimate of Lemma 3.6 holds with the constant `ε` for all label sets and offsets (at the
length `2R`), and `ρ₁`, `ρ₂` bound the row sums of Lemma 3.4 for the residue model with offsets,
then the averaged moment and the moment of the independent residue model differ by at most
`ε (ρ₁ ρ₂)^R`. -/
theorem moment_diff_le {P : GroupParams} {x : ℝ} (𝔊 : PrimeGroups P x S B) {J : ℕ} {N : Type}
    [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ) (k : ℤ) (ζ : ℝ) {R : ℕ} (hR : 0 < R)
    {X ε ρ₁ ρ₂ : ℝ} (hε : 0 ≤ ε)
    (hrep : ∀ (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ), (∀ i, Λ i ⊆ 𝔊.allPrimes) →
      (∀ i, (Λ i).card ≤ (J + P.ℓ) * groupCount S B) → h 0 = 0 →
      |intAvg X (fun n => pathFactor intPos 𝔊.allPrimes P.q (2 * R) Λ h n) -
          resAvg 𝔊.allPrimes (pathFactor (resModel 𝔊.allPrimes) 𝔊.allPrimes P.q (2 * R) Λ h)| ≤
        ε * resAvg 𝔊.allPrimes (pathFactor (resModel 𝔊.allPrimes) 𝔊.allPrimes P.q (2 * R) Λ h))
    (h1 : ∀ s, physAbsRowSum (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily P.q 𝔉 k ζ s ≤ ρ₁)
    (h2 : ∀ s, physAbsColSum (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily P.q 𝔉 k ζ s ≤ ρ₂)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    |intAvg X (fun n => physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ R n) -
        residueMoment 𝔊.toGroupFamily P.q 𝔉 k ζ R| ≤ ε * (ρ₁ * ρ₂) ^ R := by
  have hd := groupsDisjoint_of 𝔊
  have hq := P.q_pos
  have hpos : ∀ p ∈ 𝔊.allPrimes, 0 < p := fun p hp => (ResRepl.prime_of_mem_allPrimes 𝔊 hp).pos
  have hVS : ∀ g, 0 < Graph.primeGroupReciprocalMass (𝔊.small g) := fun g =>
    lt_of_lt_of_le P.vMinus_pos (𝔊.mass_small_ge g)
  have hVB : ∀ g, 0 < Graph.primeGroupReciprocalMass (𝔊.big g) := fun g =>
    lt_of_lt_of_le P.vMinus_pos (𝔊.mass_big_ge g)
  have hmass0 : 0 ≤ stateMass 𝔊.toGroupFamily J P.ℓ := by
    unfold stateMass
    exact mul_nonneg
      (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (hVS g).le _))
      (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (hVB g).le _))
  -- the two position models have additive translations
  have haddI : ∀ (a b : ℤ) (n : intPos.Pos), intPos.shift a (intPos.shift b n) =
      intPos.shift (b + a) n := fun a b n => add_assoc (show ℤ from n) b a
  have hzeroI : ∀ n : intPos.Pos, intPos.shift 0 n = n := fun n => add_zero (show ℤ from n)
  have hfreeI : ∀ (n : ℤ) (d : ℤ), intPos.shift d n = n ↔ d = 0 := fun n d => by
    show n + d = n ↔ d = 0
    omega
  have haddT : ∀ (a b : ℤ) (n : (tagModel 𝔊.allPrimes).Pos),
      (tagModel 𝔊.allPrimes).shift a ((tagModel 𝔊.allPrimes).shift b n) =
        (tagModel 𝔊.allPrimes).shift (b + a) n := fun a b n => tagModel_shift_shift a b n
  have hzeroT : ∀ n : (tagModel 𝔊.allPrimes).Pos, (tagModel 𝔊.allPrimes).shift 0 n = n :=
    fun n => tagModel_shift_zero n
  have hfreeT : ∀ (y : ResVec 𝔊.allPrimes) (d : ℤ),
      (tagModel 𝔊.allPrimes).shift d (tagStart y) = tagStart y ↔ d = 0 := fun y d =>
    tagStart_shift_eq_iff y d
  have hlen : ∀ w : Fin R → PhysChoice 𝔊.toGroupFamily 𝔉 × PhysChoice 𝔊.toGroupFamily 𝔉,
      (flatWord (List.ofFn w)).length = 2 * R := fun w => by
    rw [length_flatWord, List.length_ofFn]
  have hne : ∀ w : Fin R → PhysChoice 𝔊.toGroupFamily 𝔉 × PhysChoice 𝔊.toGroupFamily 𝔉,
      List.ofFn w ≠ [] := fun w h => by
    have h1 := congrArg List.length h
    rw [List.length_ofFn, List.length_nil] at h1
    omega
  -- the absolute mass of all paths
  have hpt : ∀ y : ResVec 𝔊.allPrimes,
      ∑ x : Lists 𝔊.toGroupFamily J P.ℓ,
        ∑ w : Fin R → PhysChoice 𝔊.toGroupFamily 𝔉 × PhysChoice 𝔊.toGroupFamily 𝔉,
          |pathAmp 𝔊.toGroupFamily 𝔉 k ζ x (flatWord (List.ofFn w))| *
            pathFactor (resModel 𝔊.allPrimes) 𝔊.allPrimes P.q (2 * R)
              (skelLab 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w)))
              (skelOff 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w))) y ≤
      (ρ₁ * ρ₂) ^ R * ∑ x : Lists 𝔊.toGroupFamily J P.ℓ,
        if IsPhys (tagModel 𝔊.allPrimes) (tagStart y) x then stateMass 𝔊.toGroupFamily J P.ℓ
          else 0 := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hpf0 : ∀ w : Fin R → PhysChoice 𝔊.toGroupFamily 𝔉 × PhysChoice 𝔊.toGroupFamily 𝔉,
        0 ≤ pathFactor (tagModel 𝔊.allPrimes) 𝔊.allPrimes P.q (2 * R)
          (skelLab 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w)))
          (skelOff 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w))) (tagStart y) := fun w =>
      pathFactor_nonneg _ _ hq.le _ _ _ _
    by_cases h0 : IsPhys (tagModel 𝔊.allPrimes) (tagStart y) x
    · rw [if_pos h0]
      have hw : ∀ w : Fin R → PhysChoice 𝔊.toGroupFamily 𝔉 × PhysChoice 𝔊.toGroupFamily 𝔉,
          |pathAmp 𝔊.toGroupFamily 𝔉 k ζ x (flatWord (List.ofFn w))| *
            pathFactor (resModel 𝔊.allPrimes) 𝔊.allPrimes P.q (2 * R)
              (skelLab 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w)))
              (skelOff 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w))) y ≤
          stateMass 𝔊.toGroupFamily J P.ℓ *
            ‖walkCoef (physRoundCoef (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily P.q 𝔉 k ζ)
              (physRoundTgt (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily 𝔉 k) (tagStart y, x)
              (List.ofFn w)‖ := by
        intro w
        have hre := re_round_term 𝔊.toGroupFamily (tagModel 𝔊.allPrimes) haddT hzeroT hd hq 𝔉 k
          ζ (tagStart y) (hfreeT y) x (List.ofFn w) (hne w)
        rw [hlen w] at hre
        rw [← pathFactor_tag_eq, ← abs_of_nonneg (hpf0 w), ← abs_mul, ← hre]
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_of_nonneg hmass0]
        exact mul_le_of_le_one_right (mul_nonneg hmass0 (norm_nonneg _))
          (norm_physUnit_le_one _ _ _ _ _ _)
      calc ∑ w : Fin R → PhysChoice 𝔊.toGroupFamily 𝔉 × PhysChoice 𝔊.toGroupFamily 𝔉,
            |pathAmp 𝔊.toGroupFamily 𝔉 k ζ x (flatWord (List.ofFn w))| *
              pathFactor (resModel 𝔊.allPrimes) 𝔊.allPrimes P.q (2 * R)
                (skelLab 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w)))
                (skelOff 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w))) y
          ≤ ∑ w : Fin R → PhysChoice 𝔊.toGroupFamily 𝔉 × PhysChoice 𝔊.toGroupFamily 𝔉,
              stateMass 𝔊.toGroupFamily J P.ℓ *
                ‖walkCoef (physRoundCoef (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily P.q 𝔉 k ζ)
                  (physRoundTgt (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily 𝔉 k) (tagStart y, x)
                  (List.ofFn w)‖ := Finset.sum_le_sum fun w _ => hw w
        _ = stateMass 𝔊.toGroupFamily J P.ℓ *
              ∑ w : Fin R → PhysChoice 𝔊.toGroupFamily 𝔉 × PhysChoice 𝔊.toGroupFamily 𝔉,
                ‖walkCoef (physRoundCoef (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily P.q 𝔉 k ζ)
                  (physRoundTgt (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily 𝔉 k) (tagStart y, x)
                  (List.ofFn w)‖ := (Finset.mul_sum _ _ _).symm
        _ ≤ stateMass 𝔊.toGroupFamily J P.ℓ * (ρ₁ * ρ₂) ^ R :=
            mul_le_mul_of_nonneg_left
              (sum_norm_walkCoef_round_le (tagModel 𝔊.allPrimes) 𝔊.toGroupFamily P.q 𝔉 k ζ h1 h2
                R (tagStart y, x)) hmass0
        _ = (ρ₁ * ρ₂) ^ R * stateMass 𝔊.toGroupFamily J P.ℓ := mul_comm _ _
    · rw [if_neg h0, mul_zero]
      refine le_of_eq (Finset.sum_eq_zero fun w _ => ?_)
      have hz := pathAmp_mul_pathFactor_eq_zero 𝔊.toGroupFamily (tagModel 𝔊.allPrimes) hzeroT
        (q := P.q) 𝔉 k ζ (tagStart y) x (flatWord (List.ofFn w)) h0
      rw [hlen w] at hz
      rw [← pathFactor_tag_eq, ← abs_of_nonneg (hpf0 w), ← abs_mul, hz, abs_zero]
  have habs : resAvg 𝔊.allPrimes (fun y => ∑ x : Lists 𝔊.toGroupFamily J P.ℓ,
        ∑ w : Fin R → PhysChoice 𝔊.toGroupFamily 𝔉 × PhysChoice 𝔊.toGroupFamily 𝔉,
          |pathAmp 𝔊.toGroupFamily 𝔉 k ζ x (flatWord (List.ofFn w))| *
            pathFactor (resModel 𝔊.allPrimes) 𝔊.allPrimes P.q (2 * R)
              (skelLab 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w)))
              (skelOff 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w))) y) ≤ (ρ₁ * ρ₂) ^ R := by
    refine (resAvg_mono 𝔊.allPrimes hpt).trans ?_
    rw [resAvg_const_mul]
    exact mul_le_of_le_one_right (pow_nonneg (mul_nonneg hρ₁ hρ₂) R)
      (resAvg_initial_mass_le_one hd hpos hVS hVB J P.ℓ)
  unfold residueMoment
  exact abs_intAvg_sub_resAvg_le 𝔊.allPrimes P.q (2 * R)
    (fun x w => pathAmp 𝔊.toGroupFamily 𝔉 k ζ x (flatWord (List.ofFn w)))
    (fun x w => skelLab 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w)))
    (fun x w => skelOff 𝔊.toGroupFamily 𝔉 k x (flatWord (List.ofFn w))) hε _ _
    (fun n' => physMoment_eq_sum_paths 𝔊.toGroupFamily intPos haddI hzeroI hd hq 𝔉 k ζ n'
      (hfreeI n') hR)
    (fun y => physMoment_eq_sum_paths 𝔊.toGroupFamily (tagModel 𝔊.allPrimes) haddT hzeroT hd hq
      𝔉 k ζ (tagStart y) (hfreeT y) hR)
    (fun x w => hrep _ _ (fun i => skelLab_subset 𝔊.toGroupFamily 𝔉 k x _ i)
      (fun i => card_skelLab_le 𝔊.toGroupFamily 𝔉 k x _ i) (skelOff_zero 𝔊.toGroupFamily 𝔉 k x _))
    habs

end ResSum

/-- **The summation over paths** [S-02:0212–0234, 0293–0307], proved: Lemma 3.6 implies the
reduction to the independent residue model. -/
theorem residueSummation : ResidueSummation := by
  intro hU P m C₁ J C₂ γ A' hγ
  have hA : 0 < max (A' + schurExponent P m C₁) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hAle : A' + schurExponent P m C₁ ≤ max (A' + schurExponent P m C₁) 1 := le_max_left _ _
  obtain ⟨x₀, hx₀⟩ := hU P J γ (max (A' + schurExponent P m C₁) 1) hγ hA
  refine ⟨max x₀ (Real.exp 1), fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm X hX1 hX2 => ?_⟩
  have hxx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hL1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h
  have hL0 : 0 < Real.log x := by linarith
  have hR : 0 < transferR (Real.log x) := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hL0 _)
  have hschur := fun s => tag_schur_bound P m C₁ hL0 𝔊 𝔉 ζ k hadm s
  have hrpow0 : 0 ≤ Real.log x ^ schurExponent P m C₁ := Real.rpow_nonneg hL0.le _
  have key := ResSum.moment_diff_le 𝔊 𝔉 k ζ hR
    (ε := Real.exp (-(max (A' + schurExponent P m C₁) 1 *
      (Graph.sourceMemoryLength (Real.log x) : ℝ) * Real.log (Real.log x))))
    (X := X) (Real.exp_pos _).le
    (fun Λ h hΛ hcard h0 => hx₀ x hxx₀ S B 𝔊 Λ h hΛ hcard h0 X hX1 hX2)
    (fun s => (hschur s).1) (fun s => (hschur s).2) hrpow0 hrpow0
  refine key.trans ?_
  have hNn : (Graph.sourceMemoryLength (Real.log x) : ℝ) = 2 * (transferR (Real.log x) : ℝ) := by
    rw [sourceMemoryLength_eq_two_mul]
    push_cast
    ring
  have hNn0 : (0 : ℝ) ≤ (Graph.sourceMemoryLength (Real.log x) : ℝ) := Nat.cast_nonneg _
  have e1 : Real.exp (-(max (A' + schurExponent P m C₁) 1 *
        (Graph.sourceMemoryLength (Real.log x) : ℝ) * Real.log (Real.log x))) =
      Real.log x ^ (-(max (A' + schurExponent P m C₁) 1 *
        (Graph.sourceMemoryLength (Real.log x) : ℝ))) := by
    rw [Real.rpow_def_of_pos hL0]
    congr 1
    ring
  have e2 : (Real.log x ^ schurExponent P m C₁ * Real.log x ^ schurExponent P m C₁) ^
        transferR (Real.log x) =
      Real.log x ^ (schurExponent P m C₁ * (Graph.sourceMemoryLength (Real.log x) : ℝ)) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, hNn]
    congr 1
    ring
  rw [e1, e2, ← Real.rpow_add hL0]
  refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
  nlinarith [mul_nonneg (sub_nonneg.mpr hAle) hNn0]

/-- **The reduction to the independent residue model** [S-02:0293–0307]: "we may therefore use
the independent residue model". -/
theorem residueReduction : ResidueReduction := residueSummation uniformResidueReplacement

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
