module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueCompare
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueActive
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueScalars
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# [S] Lemma 3.6 (uniform residue replacement), proved

Source: `verification/stage7-sources/S-02.tex`, lines 236–291 (`[S-02:0236–0291]`).

`uniformResidueReplacement : UniformResidueReplacement` — for `x ≥ x₀(P, J, γ, A)`, every system of
prime groups, all sets `Λ_0, …, Λ_N` of at most `M s` group primes, all integer offsets and every
window `I = [X, 2X)` with `X ≥ x^γ`: the average over `I ∩ ℤ` of (eq:path-residue-factor) differs
from its expectation `E` under independent uniform residues by at most `exp(-A N T) · E`.

## The proof

* `ResRepl.path_estimate` — the estimate for one path and one interval `[a, b)` of integers, for an
  arbitrary finite set `Q` of primes (no asymptotics). (eq:path-residue-factor) is the product
  over `p ∈ Q` of the local factors `ResRepl.localFactor` at the residues of the position
  (`ResidueActive.lean`), and `ResRepl.abs_avg_sub_le` (`ResidueCompare.lean`) compares the average
  of such a product over `[a, b)` with the product of the means: Bonferroni's inequalities at the
  primes which are active at no visit, the CRT count of every truncated term, and no expansion at
  the active primes, whose product `Q_act` only enters through `Q_act/(b - a)`.
* `uniformResidueReplacement` — the choice of the truncation degree `K + 1 ≈ 5λ + A N T` and the
  scalar estimates of `ResidueScalars.lean`.

## Differences from the manuscript's proof

* There is no case distinction "compatible / incompatible active congruences" and the
  deterministic damping factors at the active primes are not factored out: at an active prime the
  only property used is that its local factor is nonnegative. If the active congruences are
  incompatible, the mean of some local factor is `0`, the expectation `E` is `0`, and the estimate
  reads `0 ≤ 0`.
* The Bonferroni remainder is bounded by `exp(tλ)/t^{K+1}` with `t = e` instead of `λ^h/h!` and
  Stirling's bound.
* The counting error is bounded through the weighted CRT count `ResRepl.abs_sum_Ico_prod_sub_le`
  (the factors `X_p` are not expanded into residues) and
  `∑_{|T| ≤ K} ∏_{p ∈ T} z_p ≤ Z^K exp(∑ z_p / Z)`, `z_p = ∑_r c_{p,r} ≤ p μ_p`,
  `Z = exp(2 L^d)`; the number of group primes does not enter.
* The upper bound `X ≤ x^{1/γ}` of the statement is not used.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

open Filter

noncomputable section

namespace ResRepl

/-- The modulus at the index `p ∈ Q`: `p - 1 + 1`, so that `ZMod (resMod Q p)` is `Res p`. -/
abbrev resMod (Q : Finset ℕ) (p : {p : ℕ // p ∈ Q}) : ℕ := p.1 - 1 + 1

/-- The local factors of a path as a family over the index type `{p // p ∈ Q}`. -/
def pathLocal (Q : Finset ℕ) (q : ℝ) (n : ℕ) (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ)
    (p : {p : ℕ // p ∈ Q}) (u : ZMod (resMod Q p)) : ℝ :=
  localFactor q n Λ h p.1 u

/-- The expectation of (eq:path-residue-factor) under independent uniform residues is
nonnegative. -/
theorem resAvg_pathFactor_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (Q : Finset ℕ) (n : ℕ)
    (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ) (hΛ : ∀ i, Λ i ⊆ Q) :
    0 ≤ resAvg Q (pathFactor (resModel Q) Q q n Λ h) := by
  have h0 : resAvg Q (fun _ => (0 : ℝ)) ≤ resAvg Q (pathFactor (resModel Q) Q q n Λ h) :=
    resAvg_mono Q fun y => by
      rw [pathFactor_resModel_eq Q q n Λ h hΛ y]
      exact Finset.prod_nonneg fun p _ => localFactor_nonneg hq0 hq1 n Λ h p.1 (y p)
  rwa [resAvg_const] at h0

/-- **The estimate for one path and one interval of integers** [S-02:0244–0289]. `Q` is a finite
set of primes `p ≥ 2(n + 1)`, `p ≤ hi`; `λ ≥ (n + 1) ∑_{p ∈ Q} 1/p`; `Z ≥ max(1, hi · λ)`. The
average over `[a, b)` of (eq:path-residue-factor) equals its expectation `E` under independent
uniform residues up to
`exp(2λ) (exp(eλ)/e^{K+1} + (Q_act/(b - a)) Z^{K+1} e) · E`, where `Q_act` is the product of the
active primes. -/
theorem path_estimate {Q : Finset ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ)
    (Λ : ℕ → Finset ℕ) (h : ℕ → ℤ) (hprimeQ : ∀ p ∈ Q, p.Prime) (hΛ : ∀ i, Λ i ⊆ Q) {a b : ℤ}
    (hab : a < b) {hi lam Z : ℝ} (hlo : ∀ p ∈ Q, 2 * ((n : ℝ) + 1) ≤ (p : ℝ)) (hhi0 : 0 ≤ hi)
    (hhi : ∀ p ∈ Q, (p : ℝ) ≤ hi) (hsum : ((n : ℝ) + 1) * ∑ p ∈ Q, 1 / (p : ℝ) ≤ lam)
    (hZ1 : 1 ≤ Z) (hZ : hi * lam ≤ Z) (K : ℕ) :
    |((b : ℝ) - a)⁻¹ * ∑ k ∈ Finset.Ico a b, pathFactor intPos Q q n Λ h k -
        resAvg Q (pathFactor (resModel Q) Q q n Λ h)| ≤
      Real.exp (2 * lam) * (Real.exp (Real.exp 1 * lam) / Real.exp 1 ^ (K + 1) +
          (∏ p ∈ activeSet Q n Λ, (p.1 : ℝ)) / ((b : ℝ) - a) * (Z ^ (K + 1) * Real.exp 1)) *
        resAvg Q (pathFactor (resModel Q) Q q n Λ h) := by
  have hposQ : ∀ p ∈ Q, 0 < p := fun p hp => (hprimeQ p hp).pos
  have hm_eq : ∀ p : {p : ℕ // p ∈ Q}, resMod Q p = p.1 := fun p =>
    Nat.sub_add_cancel (hposQ p.1 p.2)
  have hmR : ∀ p : {p : ℕ // p ∈ Q}, ((resMod Q p : ℕ) : ℝ) = (p.1 : ℝ) := fun p => by
    rw [hm_eq p]
  have hppos : ∀ p : {p : ℕ // p ∈ Q}, (0 : ℝ) < (p.1 : ℝ) := fun p =>
    Nat.cast_pos.mpr (hposQ p.1 p.2)
  have hcop : Pairwise (Function.onFun Nat.Coprime (resMod Q)) := by
    intro p p' hne
    show Nat.Coprime (resMod Q p) (resMod Q p')
    rw [hm_eq p, hm_eq p']
    exact (Nat.coprime_primes (hprimeQ p.1 p.2) (hprimeQ p'.1 p'.2)).mpr fun h12 =>
      hne (Subtype.ext h12)
  have hφ0 : ∀ (p : {p : ℕ // p ∈ Q}) (u : ZMod (resMod Q p)), 0 ≤ pathLocal Q q n Λ h p u :=
    fun p u => localFactor_nonneg hq0 hq1 n Λ h p.1 u
  have hφ1 : ∀ (p : {p : ℕ // p ∈ Q}) (u : ZMod (resMod Q p)), pathLocal Q q n Λ h p u ≤ 1 :=
    fun p u => localFactor_le_one hq0 hq1 n Λ h p.1 u
  have hAR : Disjoint (activeSet Q n Λ) (Finset.univ \ activeSet Q n Λ) := Finset.disjoint_sdiff
  have hAunion : activeSet Q n Λ ∪ (Finset.univ \ activeSet Q n Λ) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  -- a prime which is active at no visit
  have hdef : ∀ p ∈ Finset.univ \ activeSet Q n Λ,
      defect (resMod Q) (pathLocal Q q n Λ h) p ≤ (n : ℝ) + 1 := fun p hp =>
    sum_one_sub_localFactor_le hq0 hq1 n Λ h p.1
      (notMem_of_notMem_activeSet (Finset.mem_sdiff.mp hp).2)
  have hhalf : ∀ p ∈ Finset.univ \ activeSet Q n Λ,
      defect (resMod Q) (pathLocal Q q n Λ h) p / ((resMod Q p : ℕ) : ℝ) ≤ 1 / 2 := by
    intro p hp
    rw [hmR p, div_le_iff₀ (hppos p)]
    have h1 := hdef p hp
    have h2 := hlo p.1 p.2
    linarith
  have hlam : ∑ p ∈ Finset.univ \ activeSet Q n Λ,
      defect (resMod Q) (pathLocal Q q n Λ h) p / ((resMod Q p : ℕ) : ℝ) ≤ lam := by
    calc ∑ p ∈ Finset.univ \ activeSet Q n Λ,
          defect (resMod Q) (pathLocal Q q n Λ h) p / ((resMod Q p : ℕ) : ℝ)
        ≤ ∑ p ∈ Finset.univ \ activeSet Q n Λ, ((n : ℝ) + 1) * (1 / (p.1 : ℝ)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [hmR p, div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right (hdef p hp) (by positivity)
      _ ≤ ∑ p : {p : ℕ // p ∈ Q}, ((n : ℝ) + 1) * (1 / (p.1 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => by
            positivity
      _ = ((n : ℝ) + 1) * ∑ p ∈ Q, 1 / (p : ℝ) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_coe_sort Q fun p => 1 / (p : ℝ)
      _ ≤ lam := hsum
  have hζ : ∑ p ∈ Finset.univ \ activeSet Q n Λ, defect (resMod Q) (pathLocal Q q n Λ h) p ≤
      Z := by
    calc ∑ p ∈ Finset.univ \ activeSet Q n Λ, defect (resMod Q) (pathLocal Q q n Λ h) p
        ≤ ∑ p ∈ Finset.univ \ activeSet Q n Λ,
            hi * (defect (resMod Q) (pathLocal Q q n Λ h) p / ((resMod Q p : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun p _ => ?_
          have hd0 : 0 ≤ defect (resMod Q) (pathLocal Q q n Λ h) p :=
            defect_nonneg (resMod Q) _ (hφ1 p)
          have hp0 := hppos p
          rw [hmR p]
          calc defect (resMod Q) (pathLocal Q q n Λ h) p
              = (p.1 : ℝ) * (defect (resMod Q) (pathLocal Q q n Λ h) p / (p.1 : ℝ)) := by
                field_simp
            _ ≤ hi * (defect (resMod Q) (pathLocal Q q n Λ h) p / (p.1 : ℝ)) :=
                mul_le_mul_of_nonneg_right (hhi p.1 p.2) (div_nonneg hd0 hp0.le)
      _ = hi * ∑ p ∈ Finset.univ \ activeSet Q n Λ,
            defect (resMod Q) (pathLocal Q q n Λ h) p / ((resMod Q p : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ hi * lam := mul_le_mul_of_nonneg_left hlam hhi0
      _ ≤ Z := hZ
  have key := abs_avg_sub_le (resMod Q) hcop (pathLocal Q q n Λ h) hAR (fun p _ u => hφ0 p u)
    (fun p _ u => hφ0 p u) (fun p _ u => hφ1 p u) hab hhalf (Real.one_le_exp zero_le_one) hZ1
    hlam hζ K
  rw [hAunion] at key
  have hint : ∀ k : ℤ, pathFactor intPos Q q n Λ h k =
      ∏ p : {p : ℕ // p ∈ Q}, pathLocal Q q n Λ h p (k : ZMod (resMod Q p)) := fun k =>
    pathFactor_intPos_eq_prod Q q n Λ h hposQ hΛ k
  have hres : resAvg Q (pathFactor (resModel Q) Q q n Λ h) =
      ∏ p : {p : ℕ // p ∈ Q},
        rsum (resMod Q) (pathLocal Q q n Λ h) p / ((resMod Q p : ℕ) : ℝ) :=
    (congrArg (resAvg Q) (funext fun y => pathFactor_resModel_eq Q q n Λ h hΛ y)).trans
      (resAvg_prod Q (pathLocal Q q n Λ h))
  have hprodA : ∏ p ∈ activeSet Q n Λ, ((resMod Q p : ℕ) : ℝ) =
      ∏ p ∈ activeSet Q n Λ, (p.1 : ℝ) := Finset.prod_congr rfl fun p _ => hmR p
  rw [hprodA] at key
  rw [Finset.sum_congr rfl fun k _ => hint k, hres]
  exact key

end ResRepl

/-- **[S] Lemma 3.6 (uniform residue replacement, `lem:transference-crt`)** [S-02:0236–0291],
proved. -/
theorem uniformResidueReplacement : UniformResidueReplacement := by
  intro P J γ A hγ hA
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (ResRepl.residue_scalar_eventually P J hγ hA)
  refine ⟨x₀, fun x hx S B _ _ _ _ 𝔊 Λ h hΛ hcard _ X hX _ => ?_⟩
  obtain ⟨hx0, hL1, hT1, hprime, hγL, h2, hmain⟩ := hx₀ x hx
  unfold ResRepl.scalarConst at hmain
  set n : ℕ := Graph.sourceMemoryLength (Real.log x) with hn
  have hd : 0 < P.d := P.a_pos.trans (P.a_lt_b.trans (P.b_lt_c.trans P.c_lt_d))
  have hD1 : 1 ≤ Real.log x ^ P.d := Real.one_le_rpow hL1 hd.le
  have hD0 : 0 ≤ Real.log x ^ P.d := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (groupCount S B : ℝ) := Nat.cast_nonneg _
  have hs : (groupCount S B : ℝ) ≤ 2 * P.C₀ * Real.log (Real.log x) := by
    have h1 := 𝔊.card_small_le
    have h2 := 𝔊.card_big_le
    unfold groupCount
    push_cast
    linarith
  have hM0 : (0 : ℝ) ≤ (J : ℝ) + P.ℓ := add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- the window
  have hXge : Real.exp (γ * Real.log x) ≤ X := by
    rw [Real.rpow_def_of_pos hx0, mul_comm] at hX
    exact hX
  have hceil1 : (⌈X⌉ : ℝ) < X + 1 := Int.ceil_lt_add_one X
  have hceil2 : 2 * X ≤ (⌈2 * X⌉ : ℝ) := Int.le_ceil _
  have hab : ⌈X⌉ < ⌈2 * X⌉ := by
    have h' : (⌈X⌉ : ℝ) < (⌈2 * X⌉ : ℝ) := by linarith
    exact_mod_cast h'
  have hw : Real.exp (γ * Real.log x) - 1 ≤ (⌈2 * X⌉ : ℝ) - (⌈X⌉ : ℝ) := by linarith
  -- the group primes
  have hprimeQ : ∀ p ∈ 𝔊.allPrimes, p.Prime := fun p hp => ResRepl.prime_of_mem_allPrimes 𝔊 hp
  have hlo : ∀ p ∈ 𝔊.allPrimes, 2 * ((n : ℝ) + 1) ≤ (p : ℝ) := fun p hp =>
    hprime.trans (ResRepl.le_of_mem_allPrimes 𝔊 hL1 hp)
  have hhi : ∀ p ∈ 𝔊.allPrimes, (p : ℝ) ≤ Real.exp (Real.log x ^ P.d) := fun p hp =>
    ResRepl.mem_allPrimes_le 𝔊 hL1 hp
  have hsum : ((n : ℝ) + 1) * ∑ p ∈ 𝔊.allPrimes, 1 / (p : ℝ) ≤
      ((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus := by
    calc ((n : ℝ) + 1) * ∑ p ∈ 𝔊.allPrimes, 1 / (p : ℝ)
        ≤ ((n : ℝ) + 1) * ((groupCount S B : ℝ) * P.vPlus) :=
          mul_le_mul_of_nonneg_left (ResRepl.sum_inv_allPrimes_le 𝔊) (by linarith)
      _ = ((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus := by ring
  have hlamle : ((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus ≤ γ * Real.log x :=
    ResRepl.residue_scalar_lam hD1 hT1 hn0 hs P.C₀_pos P.vPlus_pos hM0 hA hmain
  have hZ : Real.exp (Real.log x ^ P.d) * (((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus) ≤
      Real.exp (2 * Real.log x ^ P.d) := by
    calc Real.exp (Real.log x ^ P.d) * (((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus)
        ≤ Real.exp (Real.log x ^ P.d) * Real.exp (Real.log x ^ P.d) :=
          mul_le_mul_of_nonneg_left (hlamle.trans hγL) (Real.exp_pos _).le
      _ = Real.exp (2 * Real.log x ^ P.d) := by rw [← Real.exp_add, two_mul]
  have hZ1 : 1 ≤ Real.exp (2 * Real.log x ^ P.d) :=
    Real.one_le_exp (mul_nonneg (by norm_num) hD0)
  -- the truncation degree
  have hκ0 : 0 ≤ 5 * (((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus) +
      A * (n : ℝ) * Real.log (Real.log x) + 1 := by
    have h1 : 0 ≤ ((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus :=
      mul_nonneg (mul_nonneg (by linarith) hs0) P.vPlus_pos.le
    have h2 : 0 ≤ A * (n : ℝ) * Real.log (Real.log x) :=
      mul_nonneg (mul_nonneg hA.le hn0) (by linarith)
    linarith
  have hK1 := Nat.le_ceil (5 * (((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus) +
    A * (n : ℝ) * Real.log (Real.log x) + 1)
  have hK2 : ((⌈5 * (((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus) +
      A * (n : ℝ) * Real.log (Real.log x) + 1⌉₊ : ℕ) : ℝ) ≤
      5 * (((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus) +
        A * (n : ℝ) * Real.log (Real.log x) + 2 := by
    have h1 := Nat.ceil_lt_add_one hκ0
    linarith
  -- the estimate for the path
  have key := ResRepl.path_estimate P.q_pos P.q_lt_one n Λ h hprimeQ hΛ hab hlo
    (Real.exp_pos _).le hhi hsum hZ1 hZ
    ⌈5 * (((n : ℝ) + 1) * (groupCount S B : ℝ) * P.vPlus) +
      A * (n : ℝ) * Real.log (Real.log x) + 1⌉₊
  have hint : intAvg X (fun k => pathFactor intPos 𝔊.allPrimes P.q n Λ h k) =
      ((⌈2 * X⌉ : ℝ) - (⌈X⌉ : ℝ))⁻¹ *
        ∑ k ∈ Finset.Ico ⌈X⌉ ⌈2 * X⌉, pathFactor intPos 𝔊.allPrimes P.q n Λ h k := by
    unfold intAvg intWindow
    have h' : (((Finset.Ico ⌈X⌉ ⌈2 * X⌉).card : ℤ) : ℝ) = ((⌈2 * X⌉ - ⌈X⌉ : ℤ) : ℝ) := by
      rw [Int.card_Ico_of_le _ _ hab.le]
    push_cast at h'
    rw [h']
  rw [hint]
  refine key.trans (mul_le_mul_of_nonneg_right ?_
    (ResRepl.resAvg_pathFactor_nonneg P.q_pos P.q_lt_one 𝔊.allPrimes n Λ h hΛ))
  have hc := ResRepl.card_activeSet_le 𝔊.allPrimes n Λ ((J + P.ℓ) * groupCount S B) hcard
  have hc' : ((ResRepl.activeSet 𝔊.allPrimes n Λ).card : ℝ) ≤
      ((n : ℝ) + 1) * (((J : ℝ) + P.ℓ) * (groupCount S B : ℝ)) := by exact_mod_cast hc
  have hQA : ∏ p ∈ ResRepl.activeSet 𝔊.allPrimes n Λ, (p.1 : ℝ) ≤
      Real.exp (((n : ℝ) + 1) * ((J : ℝ) + P.ℓ) * (groupCount S B : ℝ) * Real.log x ^ P.d) := by
    calc ∏ p ∈ ResRepl.activeSet 𝔊.allPrimes n Λ, (p.1 : ℝ)
        ≤ ∏ _p ∈ ResRepl.activeSet 𝔊.allPrimes n Λ, Real.exp (Real.log x ^ P.d) :=
          Finset.prod_le_prod (fun p _ => Nat.cast_nonneg _) fun p _ => hhi p.1 p.2
      _ = Real.exp (Real.log x ^ P.d) ^ (ResRepl.activeSet 𝔊.allPrimes n Λ).card :=
          Finset.prod_const _
      _ = Real.exp (((ResRepl.activeSet 𝔊.allPrimes n Λ).card : ℝ) * Real.log x ^ P.d) :=
          (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (((n : ℝ) + 1) * ((J : ℝ) + P.ℓ) * (groupCount S B : ℝ) *
            Real.log x ^ P.d) := by
          refine Real.exp_le_exp.mpr ?_
          calc ((ResRepl.activeSet 𝔊.allPrimes n Λ).card : ℝ) * Real.log x ^ P.d
              ≤ (((n : ℝ) + 1) * (((J : ℝ) + P.ℓ) * (groupCount S B : ℝ))) *
                  Real.log x ^ P.d := mul_le_mul_of_nonneg_right hc' hD0
            _ = ((n : ℝ) + 1) * ((J : ℝ) + P.ℓ) * (groupCount S B : ℝ) * Real.log x ^ P.d := by
                ring
  exact ResRepl.residue_scalar_final hD1 hT1 hn0 hs0 hs P.C₀_pos P.vPlus_pos hM0 hA hK1 hK2 hQA
    hw h2 hmain

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
