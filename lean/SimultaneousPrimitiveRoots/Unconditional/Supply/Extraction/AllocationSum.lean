module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.AllocationTools

/-!
# The allocation step: one active set, and the sum over the active sets

The two halves of the proof of `AllocationLink d H b q q₀` (`[P-07:0518–0615]`), at one fixed `x`.

* `Allocation.abs_shiftSum_le_of_identity` (abstract form) and
  `Allocation.abs_shiftSum_system_le` (`[P-07:0539–0611]`): for one admissible system of active
  groups whose primes are candidate primes above `W`, the tuple sum

  `∑_{u+1 ≡ b (H)} Φ(u/x) F_x(u) ã^{*j}(u+1) W_{1,q₀}(u) ∏_g (q₀/j)^{ω_g(u+1)-1} ω_g(u+1)/V_g`

  is at most `j^{s_P} x M_b + B D^{2 s_P} (1 + j^{s_P}) L^{C₊} Y`, where `M_b` bounds the sum of
  Theorem 6.1^{𝔅} for the allocation core `G_P`, `Y` bounds the divisor sum over the square
  exceptions and `D = 1/((1-q₀) v₋)`. Off the square exceptions the summand is `j^{s_P}` times the
  summand of (ext:correlation-to-use) (`AllocationIdentity`); on the exceptions both summands are
  bounded by `B D^{2 s_P} L^{C₊} τ(u+1)^k` ("their weighted tuple sums remain negligible after all
  fixed log-power losses", `[P-07:0549–0557]`), so the exceptions are removed and restored in one
  step (`Allocation.abs_shiftSum_sub_le`).
* `Allocation.abs_shiftSum_coinProd_le`: the same for the sub-system `restrictGroups 𝒞 P` of the
  candidate groups, in terms of the product of the coin probabilities (ext:active-term).
* `Allocation.abs_shiftSum_retained_le` (`[P-07:0518–0537]`): the retained mass is the signed sum
  of the products `∏_{g ∈ P} s_g` over the pairs `S` retained, `T ⊆ 𝒞 ∖ S`, `P = S ∪ T`
  (`retainedMass_expand`); there are at most `4^{|𝒞|}` pairs (the manuscript counts `3^{|𝒞|}`),
  and every `P` has at least `c₂ log L` groups of each kind because `P ⊇ S`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

namespace Allocation

/-! ### One active set -/

/-- The allocation of one active set, for abstract summands. `A`, `G`, `b`, `w`, `τ` are the
functions of `v = u + 1` written as functions of `u`. If `A b = jn · w G` off the exceptional set,
and `|a|, |b|, |w| ≤ Dn`, `|A|, |G| ≤ Lc τ`, `|F| ≤ B`, then
`|∑ Φ F A a b| ≤ jn |∑ Φ F G a w| + B Dn² (1 + jn) Lc ∑_{exc} Φ τ`. -/
theorem abs_shiftSum_le_of_identity {Φ : ℝ → ℝ} {R x : ℝ} (hR : ∀ t, R < t → Φ t = 0)
    (hx : 0 < x) (hΦ0 : ∀ t, 0 ≤ Φ t) {cls exc : ℕ → Prop} {F A G a b w τ : ℕ → ℝ}
    {B jn Dn Lc X Y : ℝ} (hB : 0 ≤ B) (hjn : 0 ≤ jn) (hDn : 0 ≤ Dn) (hLc : 0 ≤ Lc)
    (hτ : ∀ u, 0 ≤ τ u) (hF : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → |F u| ≤ B)
    (hid : ∀ u : ℕ, ¬exc (u + 1) → A u * b u = jn * w u * G u)
    (ha : ∀ u, |a u| ≤ Dn) (hb : ∀ u, |b u| ≤ Dn) (hw : ∀ u, |w u| ≤ Dn)
    (hA : ∀ u, |A u| ≤ Lc * τ u) (hG : ∀ u, |G u| ≤ Lc * τ u)
    (hmain : |shiftSum Φ x cls (fun u => F u * G u * a u * w u)| ≤ X)
    (hexc : shiftSum Φ x exc τ ≤ Y) :
    |shiftSum Φ x cls (fun u => F u * A u * (a u * b u))| ≤
      jn * X + B * Dn * Dn * (1 + jn) * (Lc * Y) := by
  have h1j : 0 ≤ 1 + jn := by linarith
  have hBd : 0 ≤ B * Dn * Dn * (1 + jn) * Lc :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB hDn) hDn) h1j) hLc
  have hoff : ∀ u : ℕ, cls (u + 1) → Φ ((u : ℝ) / x) ≠ 0 → ¬exc (u + 1) →
      F u * A u * (a u * b u) = jn * (F u * G u * a u * w u) := by
    intro u _ _ hne
    linear_combination (F u * a u) * hid u hne
  have hon : ∀ u : ℕ, cls (u + 1) → Φ ((u : ℝ) / x) ≠ 0 → exc (u + 1) →
      |F u * A u * (a u * b u) - jn * (F u * G u * a u * w u)| ≤
        B * Dn * Dn * (1 + jn) * Lc * τ u := by
    intro u _ hΦu _
    have hFu := hF u hΦu
    have hLτ : 0 ≤ Lc * τ u := mul_nonneg hLc (hτ u)
    have e1 : |F u * A u * (a u * b u)| ≤ B * (Lc * τ u) * (Dn * Dn) := by
      rw [abs_mul, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hFu (hA u) (abs_nonneg _) hB)
        (mul_le_mul (ha u) (hb u) (abs_nonneg _) hDn)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hB hLτ)
    have e2 : |jn * (F u * G u * a u * w u)| ≤ jn * (B * (Lc * τ u) * (Dn * Dn)) := by
      rw [abs_mul, abs_of_nonneg hjn, abs_mul, abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ hjn
      calc |F u| * |G u| * |a u| * |w u| ≤ B * (Lc * τ u) * Dn * Dn :=
            mul_le_mul
              (mul_le_mul (mul_le_mul hFu (hG u) (abs_nonneg _) hB) (ha u) (abs_nonneg _)
                (mul_nonneg hB hLτ))
              (hw u) (abs_nonneg _) (mul_nonneg (mul_nonneg hB hLτ) hDn)
        _ = B * (Lc * τ u) * (Dn * Dn) := by ring
    calc |F u * A u * (a u * b u) - jn * (F u * G u * a u * w u)|
        = |F u * A u * (a u * b u) + -(jn * (F u * G u * a u * w u))| := by
          rw [sub_eq_add_neg]
      _ ≤ |F u * A u * (a u * b u)| + |-(jn * (F u * G u * a u * w u))| := abs_add_le _ _
      _ = |F u * A u * (a u * b u)| + |jn * (F u * G u * a u * w u)| := by rw [abs_neg]
      _ ≤ B * (Lc * τ u) * (Dn * Dn) + jn * (B * (Lc * τ u) * (Dn * Dn)) := add_le_add e1 e2
      _ = B * Dn * Dn * (1 + jn) * Lc * τ u := by ring
  have hsub := abs_shiftSum_sub_le hR hx hΦ0 (P := cls) (E := exc)
    (g₁ := fun u => F u * A u * (a u * b u)) (g₂ := fun u => jn * (F u * G u * a u * w u))
    (g' := τ) hBd hτ hoff hon
  have hconst : shiftSum Φ x cls (fun u => jn * (F u * G u * a u * w u)) =
      jn * shiftSum Φ x cls (fun u => F u * G u * a u * w u) :=
    shiftSum_const_mul hR hx cls jn _
  have h2 : |shiftSum Φ x cls (fun u => jn * (F u * G u * a u * w u))| ≤ jn * X := by
    rw [hconst, abs_mul, abs_of_nonneg hjn]
    exact mul_le_mul_of_nonneg_left hmain hjn
  have h3 : B * Dn * Dn * (1 + jn) * Lc * shiftSum Φ x exc τ ≤
      B * Dn * Dn * (1 + jn) * Lc * Y := mul_le_mul_of_nonneg_left hexc hBd
  have h4 := abs_le.mp hsub
  have h5 := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith [h4.1, h4.2, h5.1, h5.2, h3]

/-- **One admissible system of active groups** (`[P-07:0539–0611]`). The primes of the system are
candidate primes above `W`; `hgrow` is (ext:core-bound) at this `x`; `h61` is the bound of
Theorem 6.1^{𝔅} with the cutoff `Ψ(y) = y Φ(y)` for all admissible cores; `hexc` bounds the divisor
sum over the square exceptions. -/
theorem abs_shiftSum_system_le {Φ : ℝ → ℝ} (hΦ : IsCutoff Φ) {R x : ℝ}
    (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (hL : 1 ≤ Real.log x) (hId : AllocationIdentity)
    {H b : ℕ} (hb : b.Coprime H) {q q₀ : ℝ} (hq₀ : 0 ≤ q₀) (hq₀1 : q₀ < 1) {K : ℕ}
    (𝔞 : MarkingArray K) {d : ℕ} (S : Fin d → Finset ℕ) {γ C B Mb Y : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hB : 0 ≤ B) {cand : Finset ℕ}
    (hgrow : ∀ (active : Finset ℕ) (v : ℕ), 0 < v →
      |allocationCore x γ j cand active v| ≤
        Real.log x ^ C * ((freePart active v).divisors.card : ℝ) ^ C)
    (hF : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → |centeredCore q 𝔞 x S u| ≤ B)
    (hexc : shiftSum Φ x (fun v => ∃ p ∈ cand, p ^ 2 ∣ v)
      (fun u => ((u + 1).divisors.card : ℝ) ^ ⌈C⌉₊) ≤ Y)
    {Pc : ActiveGroupConstants} {𝔊 : ActiveGroups} (hadm : 𝔊.Admissible Pc x)
    (hprimes : ∀ p ∈ 𝔊.allPrimes, p ∈ cand ∧ roughCutoff x < (p : ℝ))
    (h61 : ∀ G : ℕ → ℂ, CoreAdmissible 𝔊 x C G →
      ‖twoSidedSum q q₀ 𝔞 x 𝔊 S (classWeight H b) (mulCutoff Φ) G‖ ≤ Mb) :
    |shiftSum Φ x (fun v => v ≡ b [MOD H])
        (fun u => centeredCore q 𝔞 x S u * convPow j (strippedCoeff x γ cand) (u + 1) *
          ((∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) u) *
            ∏ g : 𝔊.Index, markFactor (q₀ / (j : ℝ)) (𝔊.group g) (u + 1)))| ≤
      (j : ℝ) ^ 𝔊.numGroups * (x * Mb) +
        B * (1 / ((1 - q₀) * Pc.vlo)) ^ 𝔊.numGroups * (1 / ((1 - q₀) * Pc.vlo)) ^ 𝔊.numGroups *
          (1 + (j : ℝ) ^ 𝔊.numGroups) * (Real.log x ^ max C 0 * Y) := by
  have hL0 : 0 ≤ Real.log x := le_trans zero_le_one hL
  have h1q : 0 < 1 - q₀ := by linarith
  have hD0 : 0 ≤ (1 / ((1 - q₀) * Pc.vlo)) ^ 𝔊.numGroups :=
    pow_nonneg (one_div_pos.mpr (mul_pos h1q Pc.vlo_pos)).le _
  have hjn0 : 0 ≤ (j : ℝ) ^ 𝔊.numGroups := pow_nonneg (Nat.cast_nonneg j) _
  -- the main term: Theorem 6.1 for the allocation core, whose two hypotheses are
  -- `allocationCore_coreInvariant` and (ext:core-bound)
  have hG : CoreAdmissible 𝔊 x C
      (fun n => ((allocationCore x γ j cand 𝔊.allPrimes n : ℝ) : ℂ)) :=
    ⟨allocationCore_coreInvariant 𝔊 x γ j cand, fun n hn =>
      le_of_eq_of_le ((Complex.norm_real _).trans (Real.norm_eq_abs _))
        (hgrow 𝔊.allPrimes n hn)⟩
  have hmain := h61 _ hG
  rw [twoSidedSum_mulCutoff hΦ hR hx q q₀ 𝔞 𝔊 S hb (allocationCore x γ j cand 𝔊.allPrimes),
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hx)] at hmain
  have hmain' := (inv_mul_le_iff₀ hx).mp hmain
  -- the allocation identity off the square exceptions
  have hid : ∀ u : ℕ, ¬(∃ p ∈ cand, p ^ 2 ∣ u + 1) →
      convPow j (strippedCoeff x γ cand) (u + 1) *
          ∏ g : 𝔊.Index, markFactor (q₀ / (j : ℝ)) (𝔊.group g) (u + 1) =
        (j : ℝ) ^ 𝔊.numGroups * (∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) (u + 1)) *
          allocationCore x γ j cand 𝔊.allPrimes (u + 1) := by
    intro u hne
    refine hId x γ q₀ j hj cand 𝔊 (fun g p hp => ?_) hadm.disjoint (u + 1) (Nat.succ_pos u)
      (fun p hp hdvd => hne ⟨p, (hprimes p hp).1, hdvd⟩)
    have hmem : p ∈ 𝔊.allPrimes := Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, hp⟩
    exact ⟨hadm.prime g p hp, (hprimes p hmem).1, (hprimes p hmem).2⟩
  exact abs_shiftSum_le_of_identity hR hx hΦ.nonneg
    (cls := fun v => v ≡ b [MOD H]) (exc := fun v => ∃ p ∈ cand, p ^ 2 ∣ v)
    (F := centeredCore q 𝔞 x S)
    (A := fun u => convPow j (strippedCoeff x γ cand) (u + 1))
    (G := fun u => allocationCore x γ j cand 𝔊.allPrimes (u + 1))
    (a := fun u => ∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) u)
    (b := fun u => ∏ g : 𝔊.Index, markFactor (q₀ / (j : ℝ)) (𝔊.group g) (u + 1))
    (w := fun u => ∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) (u + 1))
    (τ := fun u => ((u + 1).divisors.card : ℝ) ^ ⌈C⌉₊)
    hB hjn0 hD0 (Real.rpow_nonneg hL0 _) (fun u => pow_nonneg (Nat.cast_nonneg _) _) hF hid
    (fun u => (abs_of_nonneg (prod_markFactor_nonneg 𝔊 hq₀ u)).le.trans
      (prod_markFactor_le hadm hq₀ hq₀1 u))
    (fun u => (abs_of_nonneg (prod_markFactor_nonneg 𝔊
      (div_nonneg hq₀ (Nat.cast_nonneg j)) (u + 1))).le.trans
      (prod_markFactor_div_le hadm hq₀ hq₀1 hj (u + 1)))
    (fun u => (abs_of_nonneg (prod_markFactor_nonneg 𝔊 hq₀ (u + 1))).le.trans
      (prod_markFactor_le hadm hq₀ hq₀1 (u + 1)))
    (fun u => abs_convPow_le hL (Nat.succ_pos u) (hgrow ∅ (u + 1) (Nat.succ_pos u)))
    (fun u => abs_allocationCore_le hL (Nat.succ_pos u)
      (hgrow 𝔊.allPrimes (u + 1) (Nat.succ_pos u)))
    hmain' hexc

/-- **One active set of candidate groups** (`[P-07:0527–0611]`, (ext:active-term)): the tuple sum
with the product `∏_{g ∈ P} s_g` of the coin probabilities, for an active set `P` whose sub-system
is admissible. The coefficient `c₁^{|P|}` is the one of `[P-07:0532]`. -/
theorem abs_shiftSum_coinProd_le {Φ : ℝ → ℝ} (hΦ : IsCutoff Φ) {R x : ℝ}
    (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (hL : 1 ≤ Real.log x) (hId : AllocationIdentity)
    {H b : ℕ} (hb : b.Coprime H) {q q₀ : ℝ} (hq₀ : 0 ≤ q₀) (hq₀1 : q₀ < 1) {K : ℕ}
    (𝔞 : MarkingArray K) {d : ℕ} (S : Fin d → Finset ℕ) {γ C B c₁ Mb Y : ℝ} {j : ℕ}
    (hj : 1 ≤ j) (hc₁ : 0 ≤ c₁) (hB : 0 ≤ B)
    (hcand : ∀ p ∈ candidatePrimes x, p.Prime ∧ roughCutoff x < (p : ℝ))
    (hgrow : ∀ (candidates active : Finset ℕ) (v : ℕ), 0 < v →
      |allocationCore x γ j candidates active v| ≤
        Real.log x ^ C * ((freePart active v).divisors.card : ℝ) ^ C)
    (hF : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → |centeredCore q 𝔞 x S u| ≤ B)
    (hexc : shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
      (fun u => ((u + 1).divisors.card : ℝ) ^ ⌈C⌉₊) ≤ Y)
    {Pc : ActiveGroupConstants} (P : Finset (candidateGroups x).Index)
    (hadm : (restrictGroups (candidateGroups x) P).Admissible Pc x)
    (h61 : ∀ G : ℕ → ℂ, CoreAdmissible (restrictGroups (candidateGroups x) P) x C G →
      ‖twoSidedSum q q₀ 𝔞 x (restrictGroups (candidateGroups x) P) S (classWeight H b)
        (mulCutoff Φ) G‖ ≤ Mb) :
    |shiftSum Φ x (fun v => v ≡ b [MOD H])
        (fun u => centeredCore q 𝔞 x S u *
          convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1) *
            ∏ g ∈ P, coinProb (candidateGroups x) c₁ q₀ j u g)| ≤
      c₁ ^ P.card * ((j : ℝ) ^ P.card * (x * Mb) +
        B * (1 / ((1 - q₀) * Pc.vlo)) ^ P.card * (1 / ((1 - q₀) * Pc.vlo)) ^ P.card *
          (1 + (j : ℝ) ^ P.card) * (Real.log x ^ max C 0 * Y)) := by
  have hsys := abs_shiftSum_system_le hΦ hR hx hL hId hb hq₀ hq₀1 𝔞 S hj hB
    (hgrow (candidatePrimes x)) hF hexc hadm
    (fun p hp => ⟨restrictGroups_allPrimes_subset (candidateGroups x) P hp,
      (hcand p (restrictGroups_allPrimes_subset (candidateGroups x) P hp)).2⟩) h61
  rw [restrictGroups_numGroups] at hsys
  have e : ∀ u : ℕ, centeredCore q 𝔞 x S u *
      convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1) *
        ∏ g ∈ P, coinProb (candidateGroups x) c₁ q₀ j u g =
      c₁ ^ P.card * (centeredCore q 𝔞 x S u *
        convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1) *
          ((∏ g : (restrictGroups (candidateGroups x) P).Index,
              markFactor q₀ ((restrictGroups (candidateGroups x) P).group g) u) *
            ∏ g : (restrictGroups (candidateGroups x) P).Index,
              markFactor (q₀ / (j : ℝ)) ((restrictGroups (candidateGroups x) P).group g)
                (u + 1))) := by
    intro u
    have h1 : ∏ g : (restrictGroups (candidateGroups x) P).Index,
        markFactor q₀ ((restrictGroups (candidateGroups x) P).group g) u =
          ∏ g ∈ P, markFactor q₀ ((candidateGroups x).group g) u :=
      prod_restrictGroups (candidateGroups x) P fun T => markFactor q₀ T u
    have h2 : ∏ g : (restrictGroups (candidateGroups x) P).Index,
        markFactor (q₀ / (j : ℝ)) ((restrictGroups (candidateGroups x) P).group g) (u + 1) =
          ∏ g ∈ P, markFactor (q₀ / (j : ℝ)) ((candidateGroups x).group g) (u + 1) :=
      prod_restrictGroups (candidateGroups x) P fun T => markFactor (q₀ / (j : ℝ)) T (u + 1)
    rw [prod_coinProb, h1, h2]
    ring
  have hcongr := shiftSum_congr Φ x (fun v => v ≡ b [MOD H]) e
  have hconst := shiftSum_const_mul hR hx (fun v => v ≡ b [MOD H]) (c₁ ^ P.card)
    (fun u => centeredCore q 𝔞 x S u *
      convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1) *
        ((∏ g : (restrictGroups (candidateGroups x) P).Index,
            markFactor q₀ ((restrictGroups (candidateGroups x) P).group g) u) *
          ∏ g : (restrictGroups (candidateGroups x) P).Index,
            markFactor (q₀ / (j : ℝ)) ((restrictGroups (candidateGroups x) P).group g)
              (u + 1)))
  rw [hcongr.trans hconst, abs_mul, abs_of_nonneg (pow_nonneg hc₁ _)]
  exact mul_le_mul_of_nonneg_left hsys (pow_nonneg hc₁ _)

/-! ### The sum over the active sets -/

/-- **The signed expansion of the retained outcomes** (`[P-07:0518–0537]`): if the tuple sum with
`∏_{g ∈ P} s_g` is at most `E` for every active set `P` with at least `c₂ log L` groups of each
kind, then the tuple sum with the retained coin mass is at most `4^{|𝒞|} E`. -/
theorem abs_shiftSum_retained_le {Φ : ℝ → ℝ} {R x : ℝ} (hR : ∀ t, R < t → Φ t = 0)
    (hx : 0 < x) (cls : ℕ → Prop) (𝔊 : ActiveGroups) (c₁ c₂ q₀ : ℝ) (j : ℕ) (Fa : ℕ → ℝ)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hE : ∀ P : Finset 𝔊.Index, c₂ * Real.log (Real.log x) ≤ (P.toLeft.card : ℝ) →
      c₂ * Real.log (Real.log x) ≤ (P.toRight.card : ℝ) →
        |shiftSum Φ x cls (fun u => Fa u * ∏ g ∈ P, coinProb 𝔊 c₁ q₀ j u g)| ≤ E) :
    |shiftSum Φ x cls (fun u => Fa u * retainedMass 𝔊 c₁ c₂ q₀ j x u)| ≤
      (4 : ℝ) ^ 𝔊.numGroups * E := by
  -- the expansion (ext:active-term)
  have h1 : ∀ u : ℕ, Fa u * retainedMass 𝔊 c₁ c₂ q₀ j x u =
      ∑ S ∈ goodSets 𝔊 c₂ x, ∑ T ∈ Sᶜ.powerset,
        (-1) ^ T.card * (Fa u * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g) := by
    intro u
    rw [retainedMass_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by ring
  have hexp : shiftSum Φ x cls (fun u => Fa u * retainedMass 𝔊 c₁ c₂ q₀ j x u) =
      ∑ S ∈ goodSets 𝔊 c₂ x, ∑ T ∈ Sᶜ.powerset, (-1) ^ T.card *
        shiftSum Φ x cls (fun u => Fa u * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g) :=
    calc shiftSum Φ x cls (fun u => Fa u * retainedMass 𝔊 c₁ c₂ q₀ j x u)
        = shiftSum Φ x cls (fun u => ∑ S ∈ goodSets 𝔊 c₂ x, ∑ T ∈ Sᶜ.powerset,
            (-1) ^ T.card * (Fa u * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g)) :=
          shiftSum_congr Φ x cls h1
      _ = ∑ S ∈ goodSets 𝔊 c₂ x, shiftSum Φ x cls (fun u => ∑ T ∈ Sᶜ.powerset,
            (-1) ^ T.card * (Fa u * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g)) :=
          shiftSum_finset_sum hR hx cls (goodSets 𝔊 c₂ x) fun S u => ∑ T ∈ Sᶜ.powerset,
            (-1) ^ T.card * (Fa u * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g)
      _ = ∑ S ∈ goodSets 𝔊 c₂ x, ∑ T ∈ Sᶜ.powerset, (-1) ^ T.card *
            shiftSum Φ x cls (fun u => Fa u * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g) :=
          Finset.sum_congr rfl fun S _ =>
            (shiftSum_finset_sum hR hx cls (Sᶜ.powerset) fun T u =>
              (-1) ^ T.card * (Fa u * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g)).trans
              (Finset.sum_congr rfl fun T _ => shiftSum_const_mul hR hx cls ((-1) ^ T.card)
                fun u => Fa u * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g)
  -- the number of pairs `(S, T)`
  have hpow : ∀ S : Finset 𝔊.Index, ((Sᶜ.powerset).card : ℝ) ≤ (2 : ℝ) ^ 𝔊.numGroups := by
    intro S
    have h : Sᶜ.card ≤ 𝔊.numGroups := by
      rw [← card_index]
      exact Finset.card_le_univ _
    have h' : (Sᶜ.powerset).card ≤ 2 ^ 𝔊.numGroups := by
      rw [Finset.card_powerset]
      exact Nat.pow_le_pow_right (by norm_num) h
    exact_mod_cast h'
  have hcard : ((goodSets 𝔊 c₂ x).card : ℝ) ≤ (2 : ℝ) ^ 𝔊.numGroups := by
    have h : (goodSets 𝔊 c₂ x).card ≤ 2 ^ 𝔊.numGroups := by
      have h' := Finset.card_le_univ (goodSets 𝔊 c₂ x)
      rwa [Fintype.card_finset, card_index] at h'
    exact_mod_cast h
  -- every active set `P = S ∪ T` contains the retained outcome `S`
  have hinner : ∀ S ∈ goodSets 𝔊 c₂ x,
      |∑ T ∈ Sᶜ.powerset, (-1) ^ T.card *
        shiftSum Φ x cls (fun u => Fa u * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g)| ≤
        (2 : ℝ) ^ 𝔊.numGroups * E := by
    intro S hS
    unfold goodSets at hS
    obtain ⟨hSl, hSr⟩ := (Finset.mem_filter.mp hS).2
    have hT : ∀ T ∈ Sᶜ.powerset, |(-1) ^ T.card *
        shiftSum Φ x cls (fun u => Fa u * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g)| ≤ E := by
      intro T _
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hE (S ∪ T)
        (hSl.trans (Nat.cast_le.mpr (Finset.card_le_card
          (Finset.toLeft_subset_toLeft Finset.subset_union_left))))
        (hSr.trans (Nat.cast_le.mpr (Finset.card_le_card
          (Finset.toRight_subset_toRight Finset.subset_union_left))))
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hT).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hpow S) hE0
  rw [hexp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hinner).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have h2E : 0 ≤ (2 : ℝ) ^ 𝔊.numGroups * E := mul_nonneg (pow_nonneg zero_le_two _) hE0
  calc ((goodSets 𝔊 c₂ x).card : ℝ) * ((2 : ℝ) ^ 𝔊.numGroups * E)
      ≤ (2 : ℝ) ^ 𝔊.numGroups * ((2 : ℝ) ^ 𝔊.numGroups * E) :=
        mul_le_mul_of_nonneg_right hcard h2E
    _ = (4 : ℝ) ^ 𝔊.numGroups * E := by
        rw [← mul_assoc, ← mul_pow]
        norm_num

end Allocation

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
