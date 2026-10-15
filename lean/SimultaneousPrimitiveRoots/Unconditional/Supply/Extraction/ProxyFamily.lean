module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Twist
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Objects
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.CoreInvariance
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Type II estimate for real bilinear sums with a residue class

The bridge between the Type II statement (`MarkedTypeIICoefficientForm`, in the twisted form
`markedTypeII_twisted` of `Supply/Twist.lean`) and its use in the Type II step
(`[P-07:0249–0315]`, `Extraction/ProxyProof.lean`).

* `Proxy.pmrReal x lo hi`: the prime-minus-rough coefficient of Theorem 3.1 without twist
  (`v = 0`), as a real function; `Proxy.primeMinusRough_zero` identifies it with
  `primeMinusRough x 0 lo hi`, `Proxy.pmrReal_eq` with the difference `P(m) - a(m)` of the prime
  indicator and the proxy coefficient on integers `> z` ("the discrepancy in the `m` slot is
  exactly the one in Theorem 3.1", `[P-07:0290–0291]`), and `Proxy.roughDyad_primeMinusRough`
  checks the two hypotheses of `RoughDyadCoefficient` for it.
* `Proxy.clipCore`: "clip `f_x(u) - C_x` to a fixed interval containing all its values on the
  support under consideration, and divide by a fixed bound so that its modulus is at most one"
  (`[P-07:0293–0299]`); `Proxy.bandInvariant_clipCore`: "every long-slot prime lies outside the
  array bands, so `f_x(pu) = f_x(u)` for each band prime `p`; clipping preserves this identity"
  (`Proxy.eventually_band_notMem_slot`).
* `Proxy.abs_bilinear_le`: the residue class `mn ≡ b (mod H)` is carried by the characters
  `λ (mod H)` (`[PUB-tex:0503–0516]`, (eq:char-separate)): if the Type II bound holds for all the
  coefficients `α_m λ(m)`, `β_n λ(n)`, then the real bilinear sum with the factor
  `1_{mn ≡ b (H)}` has the same bound. The number of characters is `φ(H)`
  (`DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity`), so no constant is lost.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

namespace Proxy

/-! ### The class indicator -/

/-- `1_{v ≡ b (mod H)}` as a real number. -/
def clsInd (H b v : ℕ) : ℝ := if v ≡ b [MOD H] then 1 else 0

theorem abs_clsInd_le_one (H b v : ℕ) : |clsInd H b v| ≤ 1 := by
  unfold clsInd
  split_ifs
  · rw [abs_one]
  · rw [abs_zero]
    exact zero_le_one

/-! ### The prime-minus-rough coefficient without twist -/

open _root_.Classical in
/-- `1_{lo ≤ m ≤ hi} (1_{m prime} - 1_{m rough} / (V(W) log m))`: the coefficient of Theorem 3.1
with `v = 0`, as a real function. -/
def pmrReal (x lo hi : ℝ) (m : ℕ) : ℝ :=
  if lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi then
    (if m.Prime then 1 else 0) -
      (if IsRough (roughCutoff x) m then 1 else 0) /
        (mertensProduct (roughCutoff x) * Real.log m)
  else 0

theorem primeMinusRough_zero (x lo hi : ℝ) (m : ℕ) :
    primeMinusRough x 0 lo hi m = ((pmrReal x lo hi m : ℝ) : ℂ) := by
  unfold primeMinusRough pmrReal
  by_cases h : lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi
  · rw [if_pos h, if_pos h, Complex.ofReal_zero, zero_mul, Complex.cpow_zero, one_mul]
    by_cases hp : m.Prime <;> by_cases hr : IsRough (roughCutoff x) m <;> simp [hp, hr]
  · rw [if_neg h, if_neg h, Complex.ofReal_zero]

/-- On the integers `> z = x^γ` of its interval, the coefficient is the difference of the prime
indicator and the proxy coefficient (`[P-07:0249–0253]`). -/
theorem pmrReal_eq {x γ lo hi : ℝ} (hz : 1 ≤ x ^ γ) {m : ℕ} (hm : x ^ γ < (m : ℝ))
    (hin : lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi) :
    pmrReal x lo hi m = primeCoeff (x ^ γ) m - proxyCoeff x γ m := by
  have hm2 : 2 ≤ m := by
    have h : (1 : ℝ) < (m : ℝ) := lt_of_le_of_lt hz hm
    exact_mod_cast h
  unfold pmrReal primeCoeff proxyCoeff proxyKappa
  rw [if_pos hin]
  by_cases hp : m.Prime
  · by_cases hr : IsRough (roughCutoff x) m
    · rw [if_pos hp, if_pos hr, if_pos (And.intro hp hm),
        if_pos (And.intro hm hr), if_pos hm2]
    · rw [if_pos hp, if_neg hr, if_pos (And.intro hp hm),
        if_neg (fun h => hr h.2), zero_div]
  · by_cases hr : IsRough (roughCutoff x) m
    · rw [if_neg hp, if_pos hr, if_neg (fun h => hp h.1),
        if_pos (And.intro hm hr), if_pos hm2]
    · rw [if_neg hp, if_neg hr, if_neg (fun h => hp h.1),
        if_neg (fun h => hr h.2), zero_div]

theorem pmrReal_eq_zero {x lo hi : ℝ} {m : ℕ} (h : ¬(lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi)) :
    pmrReal x lo hi m = 0 := by
  unfold pmrReal
  exact if_neg h

/-- The coefficient is at most `1` in modulus once `κ ≤ 1` on its interval. -/
theorem abs_pmrReal_le_one {x lo hi : ℝ} (h1 : 1 < lo)
    (hκ : ∀ m : ℕ, lo ≤ (m : ℝ) → proxyKappa x m ≤ 1) (m : ℕ) : |pmrReal x lo hi m| ≤ 1 := by
  unfold pmrReal
  by_cases h : lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi
  · rw [if_pos h]
    have hm2 : 2 ≤ m := by
      have h' : (1 : ℝ) < (m : ℝ) := lt_of_lt_of_le h1 h.1
      exact_mod_cast h'
    have hk : 1 / (mertensProduct (roughCutoff x) * Real.log m) = proxyKappa x m := by
      unfold proxyKappa
      rw [if_pos hm2]
    have hk0 := proxyKappa_nonneg x m
    have hk1 := hκ m h.1
    rw [← hk] at hk0 hk1
    rw [div_eq_mul_one_div, abs_le]
    by_cases hp : m.Prime
    · by_cases hr : IsRough (roughCutoff x) m
      · rw [if_pos hp, if_pos hr]
        constructor <;> linarith
      · rw [if_pos hp, if_neg hr]
        constructor <;> linarith
    · by_cases hr : IsRough (roughCutoff x) m
      · rw [if_neg hp, if_pos hr]
        constructor <;> linarith
      · rw [if_neg hp, if_neg hr]
        constructor <;> linarith
  · rw [if_neg h, abs_zero]
    exact zero_le_one

/-- The untwisted prime-minus-rough coefficient on an interval beyond `W` is a rough dyadic
coefficient: a prime `> W` is rough, and `|α_m| ≤ 1 ≤ L^C`. -/
theorem roughDyad_primeMinusRough {x C Hm lo hi : ℝ} (hlo : Hm ≤ lo) (hhi : hi ≤ 2 * Hm)
    (hW : roughCutoff x < lo) (h1 : 1 < lo)
    (hκ : ∀ m : ℕ, lo ≤ (m : ℝ) → proxyKappa x m ≤ 1) (hLC : 1 ≤ Real.log x ^ C) :
    RoughDyadCoefficient x C Hm (primeMinusRough x 0 lo hi) where
  support := by
    intro m hm
    rw [primeMinusRough_zero] at hm
    have hm' : pmrReal x lo hi m ≠ 0 := fun h0 => hm (by rw [h0, Complex.ofReal_zero])
    by_cases h : lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi
    · refine ⟨hlo.trans h.1, h.2.trans hhi, ?_⟩
      by_contra hr
      unfold pmrReal at hm'
      rw [if_pos h, if_neg hr, zero_div, sub_zero] at hm'
      by_cases hp : m.Prime
      · apply hr
        intro p hpp hdvd
        have hpm : p = m := (Nat.prime_dvd_prime_iff_eq hpp hp).mp hdvd
        rw [hpm]
        exact lt_of_lt_of_le hW h.1
      · exact hm' (if_neg hp)
    · exact absurd (pmrReal_eq_zero h) hm'
  bound := by
    intro m
    rw [primeMinusRough_zero, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_pmrReal_le_one h1 hκ m).trans hLC

/-! ### The normalized clipped statistic -/

/-- `f_x(h) - C_x` divided by `Bs` and clipped to `[-1, 1]` (`[P-07:0293–0296]`). -/
def clipCore (Bs : ℝ) {d : ℕ} (S : Fin d → Finset ℕ) (h : ℕ) : ℝ :=
  max (-1) (min 1 (((slotCount S h : ℝ) - slotMass S) / Bs))

theorem abs_clipCore_le (Bs : ℝ) {d : ℕ} (S : Fin d → Finset ℕ) (h : ℕ) :
    |clipCore Bs S h| ≤ 1 := by
  unfold clipCore
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Where `|f_x - C_x| ≤ Bs`, the clipping does nothing. -/
theorem clipCore_eq {Bs : ℝ} (hBs : 0 < Bs) {d : ℕ} (S : Fin d → Finset ℕ) {h : ℕ}
    (hb : |(slotCount S h : ℝ) - slotMass S| ≤ Bs) :
    Bs * clipCore Bs S h = (slotCount S h : ℝ) - slotMass S := by
  have h1 := abs_le.mp hb
  have h2 : -1 ≤ ((slotCount S h : ℝ) - slotMass S) / Bs := by
    rw [le_div_iff₀ hBs]
    linarith
  have h3 : ((slotCount S h : ℝ) - slotMass S) / Bs ≤ 1 := by
    rw [div_le_iff₀ hBs]
    linarith
  unfold clipCore
  rw [min_eq_right h3, max_eq_right h2, mul_comm, div_mul_cancel₀ _ hBs.ne']

/-- The clipped statistic is invariant under the band primes when no band prime is a slot
prime. -/
theorem bandInvariant_clipCore {K : ℕ} {𝔞 : MarkingArray K} {x : ℝ} (Bs : ℝ) {d : ℕ}
    {S : Fin d → Finset ℕ} (hprime : ∀ i, ∀ ℓ ∈ S i, ℓ.Prime)
    (hdisj : ∀ i : Fin K, ∀ p ∈ bandPrimes (𝔞.exponent i) x, ∀ i' : Fin d, p ∉ S i') :
    BandInvariant 𝔞 x (fun h => ((clipCore Bs S h : ℝ) : ℂ)) := by
  intro i p hp h _
  have hpp : p.Prime := (mem_bandPrimes.mp hp).1
  show ((clipCore Bs S (p * h) : ℝ) : ℂ) = ((clipCore Bs S h : ℝ) : ℂ)
  unfold clipCore
  rw [TwoSidedProof.slotCount_mul_of_notMem hprime hpp (hdisj i p hp) h]

/-- "Every long-slot prime lies outside the array bands" (`[P-07:0296–0297]`), for
`x ≥ exp(2^{15} + ε^{-2} + 1)`: a band prime is at most `exp(2 L^{1/5})`, a slot prime at least
`x^ε = exp(ε L)`. -/
theorem eventually_band_notMem_slot {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (K : ℕ) (𝔞 : MarkingArray K) (i : Fin K),
      ∀ p ∈ bandPrimes (𝔞.exponent i) x, ∀ (d : ℕ) (S : Fin d → Finset ℕ),
        SlotsAdmissible ε x S → ∀ i' : Fin d, p ∉ S i' := by
  filter_upwards [eventually_ge_atTop (Real.exp ((2 : ℝ) ^ (15 : ℝ) + (ε ^ 2)⁻¹ + 1))]
    with x hx K 𝔞 i p hp d S hS i' hmem
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hLge : (2 : ℝ) ^ (15 : ℝ) + (ε ^ 2)⁻¹ + 1 ≤ Real.log x := by
    have h1 := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h1
  have hT0 : (0 : ℝ) < (2 : ℝ) ^ (15 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hinv : (0 : ℝ) < (ε ^ 2)⁻¹ := inv_pos.mpr hε2
  have hLT : (2 : ℝ) ^ (15 : ℝ) ≤ Real.log x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  have hLε : 1 < ε ^ 2 * Real.log x := by
    have h1 : ε ^ 2 * (ε ^ 2)⁻¹ < ε ^ 2 * Real.log x :=
      mul_lt_mul_of_pos_left (by linarith) hε2
    rwa [mul_inv_cancel₀ hε2.ne'] at h1
  have h1 : (p : ℝ) ≤ Real.exp (2 * Real.log x ^ 𝔞.exponent i) := (mem_bandPrimes.mp hp).2.2
  have h2 : x ^ ε ≤ (p : ℝ) := hS.lower i' p hmem
  rw [Real.rpow_def_of_pos hx0] at h2
  have h3 : Real.log x * ε ≤ 2 * Real.log x ^ 𝔞.exponent i := Real.exp_le_exp.mp (h2.trans h1)
  have h4 := TwoSidedProof.two_mul_rpow_lt hLT (𝔞.lt_fifth i)
  have h5 := TwoSidedProof.rpow_lt_mul hε hL1 hLε
  have h6 : Real.log x ^ (0.27 : ℝ) ≤ Real.log x ^ (0.46 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  linarith

/-! ### The class carried by characters -/

/-- **The Type II bound for a real bilinear sum with the class `mn ≡ b (mod H)`**
(`[PUB-tex:0503–0516]`). `hTII` is the Type II bound for the coefficients `α_m λ(m)` and
arbitrary rough coefficients, for all characters `λ (mod H)`; `β'` is a real rough coefficient.
By orthogonality, `1_{mn ≡ b (H)} = φ(H)^{-1} ∑_λ λ(b^{-1}) λ(m) λ(n)`. -/
theorem abs_bilinear_le {H b : ℕ} (hH : 0 < H) (hb : b.Coprime H) {q : ℝ} {K : ℕ}
    (𝔞 : MarkingArray K) {x C Hm Hn lo hi Mb : ℝ} (Fr : ℕ → ℝ)
    (hTII : ∀ (lam : DirichletCharacter ℂ H) (β : ℕ → ℂ), RoughDyadCoefficient x C Hn β →
      ‖markedBilinearSum q 𝔞 x Hm Hn (fun m => primeMinusRough x 0 lo hi m * lam (m : ZMod H)) β
        (fun h => ((Fr h : ℝ) : ℂ))‖ ≤ Mb)
    (β' : ℕ → ℝ)
    (hsupp : ∀ n, β' n ≠ 0 → Hn ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (roughCutoff x) n)
    (hbd : ∀ n, |β' n| ≤ Real.log x ^ C) :
    |∑ m ∈ dyad Hm, ∑ n ∈ dyad Hn, pmrReal x lo hi m * β' n * clsInd H b (m * n) *
        Fr (m * n - 1) * markedWeight q 𝔞 x (m * n - 1)| ≤ Mb := by
  have hNe : NeZero H := ⟨hH.ne'⟩
  have hbu : IsUnit ((b : ℕ) : ZMod H) := (ZMod.isUnit_iff_coprime b H).mpr hb
  have hφ : 0 < (H.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hH)
  have hβ : ∀ lam : DirichletCharacter ℂ H,
      RoughDyadCoefficient x C Hn (fun n => ((β' n : ℝ) : ℂ) * lam (n : ZMod H)) := by
    intro lam
    refine ⟨fun n hn => hsupp n fun h0 => hn ?_, fun n => ?_⟩
    · show ((β' n : ℝ) : ℂ) * lam (n : ZMod H) = 0
      rw [h0, Complex.ofReal_zero, zero_mul]
    · show ‖((β' n : ℝ) : ℂ) * lam (n : ZMod H)‖ ≤ Real.log x ^ C
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |β' n| * ‖lam (n : ZMod H)‖ ≤ |β' n| * 1 :=
            mul_le_mul_of_nonneg_left (lam.norm_le_one _) (abs_nonneg _)
        _ = |β' n| := mul_one _
        _ ≤ Real.log x ^ C := hbd n
  -- one pair `(m, n)`: orthogonality of the characters
  have hterm : ∀ m n : ℕ, ∑ lam : DirichletCharacter ℂ H, lam ((b : ZMod H))⁻¹ *
      (primeMinusRough x 0 lo hi m * lam (m : ZMod H) *
        (((β' n : ℝ) : ℂ) * lam (n : ZMod H)) * ((Fr (m * n - 1) : ℝ) : ℂ) *
          ((markedWeight q 𝔞 x (m * n - 1) : ℝ) : ℂ)) =
      (H.totient : ℂ) * ((pmrReal x lo hi m * β' n * clsInd H b (m * n) * Fr (m * n - 1) *
        markedWeight q 𝔞 x (m * n - 1) : ℝ) : ℂ) := by
    intro m n
    have h1 : ∀ lam : DirichletCharacter ℂ H, lam ((b : ZMod H))⁻¹ *
        (primeMinusRough x 0 lo hi m * lam (m : ZMod H) *
          (((β' n : ℝ) : ℂ) * lam (n : ZMod H)) * ((Fr (m * n - 1) : ℝ) : ℂ) *
            ((markedWeight q 𝔞 x (m * n - 1) : ℝ) : ℂ)) =
        primeMinusRough x 0 lo hi m * ((β' n : ℝ) : ℂ) * ((Fr (m * n - 1) : ℝ) : ℂ) *
          ((markedWeight q 𝔞 x (m * n - 1) : ℝ) : ℂ) *
            (lam ((b : ZMod H))⁻¹ * lam (((m * n : ℕ) : ZMod H))) := by
      intro lam
      rw [Nat.cast_mul, map_mul]
      ring
    rw [Finset.sum_congr rfl fun lam _ => h1 lam, ← Finset.mul_sum,
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ hbu, primeMinusRough_zero]
    unfold clsInd
    by_cases hc : m * n ≡ b [MOD H]
    · have hc' : ((b : ℕ) : ZMod H) = ((m * n : ℕ) : ZMod H) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc.symm
      rw [if_pos hc', if_pos hc]
      push_cast
      ring
    · have hc' : ¬((b : ℕ) : ZMod H) = ((m * n : ℕ) : ZMod H) := fun h =>
        hc ((ZMod.natCast_eq_natCast_iff _ _ _).mp h).symm
      rw [if_neg hc', if_neg hc]
      simp
  -- the character sum of the Type II sums
  obtain ⟨Z, hZ⟩ : ∃ Z : ℂ, Z = ∑ lam : DirichletCharacter ℂ H, lam ((b : ZMod H))⁻¹ *
      markedBilinearSum q 𝔞 x Hm Hn (fun m => primeMinusRough x 0 lo hi m * lam (m : ZMod H))
        (fun n => ((β' n : ℝ) : ℂ) * lam (n : ZMod H)) (fun h => ((Fr h : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hid : Z = (H.totient : ℂ) * ((∑ m ∈ dyad Hm, ∑ n ∈ dyad Hn, pmrReal x lo hi m * β' n *
      clsInd H b (m * n) * Fr (m * n - 1) * markedWeight q 𝔞 x (m * n - 1) : ℝ) : ℂ) := by
    rw [hZ]
    unfold markedBilinearSum
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm, Complex.ofReal_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hterm m n
  have hnorm : ‖Z‖ ≤ (H.totient : ℝ) * Mb := by
    rw [hZ]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => Mb) fun lam _ => ?_).trans (le_of_eq ?_)
    · rw [norm_mul]
      exact (mul_le_mul (lam.norm_le_one _) (hTII lam _ (hβ lam)) (norm_nonneg _)
        zero_le_one).trans (le_of_eq (one_mul _))
    · rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ H, nsmul_eq_mul]
  rw [hid, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact le_of_mul_le_mul_left hnorm hφ

end Proxy

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
