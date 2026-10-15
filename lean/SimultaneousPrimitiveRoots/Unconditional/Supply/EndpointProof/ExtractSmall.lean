module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements

/-!
# The extraction of a small-prime mark (cor:extract-small)

`extractSmallIdentity : ExtractSmallIdentity` (`[P-06:0683–0692]`): for pairwise disjoint groups of
primes, a group `g_s` with `t_{g_s} = 1`, a test that does not depend on the mark of `g_s`, and
`w ≥ 1` not divisible by the square of a prime of `𝒫_{g_s}`,

`W_𝐭^𝐛(w) = V_{g_s}^{-1} ∑_{p_s ∣ w, p_s ∈ 𝒫_{g_s}} W_{𝐭 - 𝐞_{g_s}}^𝐛(w / p_s)`.

"This follows directly by removing the represented small prime; the remaining damping exponent is
unchanged."

* `prime_dvd_div_iff`, `not_dvd_div_of_sq`: for primes `p ≠ p'` with `p ∣ w`, `p' ∣ w/p ↔ p' ∣ w`;
  and `p ∤ w/p` if `p² ∤ w`.
* `primeHits_div_of_notMem`, `primeHits_div_self`, `totalHits_div`: `ω_T(w/p) = ω_T(w)` for
  `p ∉ T`, `ω_G(w/p) = ω_G(w) - 1` for `p ∈ G`, and `ω_P(w/p) = ω_P(w) - 1`.
* `partialLists_div`: the lists with the mark of `g_s` removed are the same at `w/p` and at `w`.
* `exponent_eq`: "the remaining damping exponent is unchanged".
* `sum_representedLists_eq`: a represented list at `w` is a prime `p_s ∣ w` of `𝒫_{g_s}` and a list
  with the mark of `g_s` removed.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### Divisibility after removing one prime -/

/-- For distinct primes `p, p'` with `p ∣ w`: `p' ∣ w / p ↔ p' ∣ w`. -/
theorem prime_dvd_div_iff {p p' w : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p' ≠ p)
    (hpw : p ∣ w) : p' ∣ w / p ↔ p' ∣ w := by
  constructor
  · intro h
    exact h.trans (Nat.div_dvd_of_dvd hpw)
  · intro h
    have h2 : p' ∣ p * (w / p) := by
      rw [Nat.mul_div_cancel' hpw]
      exact h
    rcases (Nat.Prime.dvd_mul hp').mp h2 with h1 | h1
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp' hp).mp h1) hne
    · exact h1

/-- If `p ∣ w` and `p² ∤ w`, then `p ∤ w / p`. -/
theorem not_dvd_div_of_sq {p w : ℕ} (hpw : p ∣ w) (hsq : ¬ p ^ 2 ∣ w) : ¬ p ∣ w / p := by
  intro h
  apply hsq
  have h1 : p * p ∣ p * (w / p) := Nat.mul_dvd_mul_left p h
  rw [Nat.mul_div_cancel' hpw] at h1
  rw [pow_two]
  exact h1

/-- The prime divisors in a set `T ∌ p` are the same for `w / p` and for `w`. -/
theorem filter_dvd_div_of_notMem {T : Finset ℕ} {p w : ℕ} (hT : ∀ p' ∈ T, p'.Prime)
    (hp : p.Prime) (hpT : p ∉ T) (hpw : p ∣ w) :
    T.filter (fun p' => p' ∣ w / p) = T.filter (fun p' => p' ∣ w) := by
  refine Finset.filter_congr fun p' hp' => ?_
  exact prime_dvd_div_iff hp (hT p' hp') (fun h => hpT (h ▸ hp')) hpw

/-- The prime divisors of `w / p` in a set `G ∋ p` are those of `w` other than `p`. -/
theorem filter_dvd_div_self {G : Finset ℕ} {p w : ℕ} (hG : ∀ p' ∈ G, p'.Prime) (hpG : p ∈ G)
    (hpw : p ∣ w) (hsq : ¬ p ^ 2 ∣ w) :
    G.filter (fun p' => p' ∣ w / p) = (G.filter (fun p' => p' ∣ w)).erase p := by
  ext p'
  rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    have hne : p' ≠ p := by
      intro h
      rw [h] at h2
      exact not_dvd_div_of_sq hpw hsq h2
    exact ⟨hne, h1, (prime_dvd_div_iff (hG p hpG) (hG p' h1) hne hpw).mp h2⟩
  · rintro ⟨hne, h1, h2⟩
    exact ⟨h1, (prime_dvd_div_iff (hG p hpG) (hG p' h1) hne hpw).mpr h2⟩

/-- `ω_T(w / p) = ω_T(w)` for `p ∉ T`. -/
theorem primeHits_div_of_notMem {T : Finset ℕ} {p w : ℕ} (hT : ∀ p' ∈ T, p'.Prime)
    (hp : p.Prime) (hpT : p ∉ T) (hpw : p ∣ w) : primeHits T (w / p) = primeHits T w := by
  unfold primeHits
  rw [filter_dvd_div_of_notMem hT hp hpT hpw]

/-- `ω_G(w / p) + 1 = ω_G(w)` for `p ∈ G`, `p ∣ w`, `p² ∤ w`. -/
theorem primeHits_div_self {G : Finset ℕ} {p w : ℕ} (hG : ∀ p' ∈ G, p'.Prime) (hpG : p ∈ G)
    (hpw : p ∣ w) (hsq : ¬ p ^ 2 ∣ w) : primeHits G (w / p) + 1 = primeHits G w := by
  unfold primeHits
  rw [filter_dvd_div_self hG hpG hpw hsq]
  have hmem : p ∈ G.filter (fun p' => p' ∣ w) := Finset.mem_filter.mpr ⟨hpG, hpw⟩
  rw [Finset.card_erase_of_mem hmem]
  have hpos : 0 < (G.filter (fun p' => p' ∣ w)).card := Finset.card_pos.mpr ⟨p, hmem⟩
  omega

/-- `ω_P(w / p) + 1 = ω_P(w)` for a prime `p` of one group with `p ∣ w`, `p² ∤ w`, when the
groups are pairwise disjoint sets of primes. -/
theorem totalHits_div (𝔊 : ActiveGroups) (hprime : ∀ g : 𝔊.Index, ∀ p ∈ 𝔊.group g, p.Prime)
    (hdisj : ∀ g g' : 𝔊.Index, g ≠ g' → Disjoint (𝔊.group g) (𝔊.group g')) (g₀ : 𝔊.Index)
    {p w : ℕ} (hpG : p ∈ 𝔊.group g₀) (hpw : p ∣ w) (hsq : ¬ p ^ 2 ∣ w) :
    𝔊.totalHits (w / p) + 1 = 𝔊.totalHits w := by
  have h1 : ∑ g ∈ Finset.univ.erase g₀, primeHits (𝔊.group g) (w / p) =
      ∑ g ∈ Finset.univ.erase g₀, primeHits (𝔊.group g) w :=
    Finset.sum_congr rfl fun g hg => primeHits_div_of_notMem (hprime g) (hprime g₀ p hpG)
      (Finset.disjoint_left.mp (hdisj g₀ g (Finset.ne_of_mem_erase hg).symm) hpG) hpw
  have h2 := primeHits_div_self (hprime g₀) hpG hpw hsq
  have e1 : 𝔊.totalHits (w / p) = primeHits (𝔊.group g₀) (w / p) +
      ∑ g ∈ Finset.univ.erase g₀, primeHits (𝔊.group g) (w / p) :=
    (Finset.add_sum_erase Finset.univ (fun g => primeHits (𝔊.group g) (w / p))
      (Finset.mem_univ g₀)).symm
  have e2 : 𝔊.totalHits w = primeHits (𝔊.group g₀) w +
      ∑ g ∈ Finset.univ.erase g₀, primeHits (𝔊.group g) w :=
    (Finset.add_sum_erase Finset.univ (fun g => primeHits (𝔊.group g) w)
      (Finset.mem_univ g₀)).symm
  rw [e1, e2, h1]
  omega

/-! ### The lists and the exponent -/

/-- In a list with the mark of the group `g₀` removed, the entry of `g₀` is the dummy list. -/
theorem partialLists_apply_self {𝔊 : ActiveGroups} {t : 𝔊.Index → ℕ} {g₀ : 𝔊.Index} {n : ℕ}
    {𝔭 : (g : 𝔊.Index) → Fin (t g) → ℕ} (h : 𝔭 ∈ partialLists 𝔊 t {g₀} n) :
    𝔭 g₀ = fun _ => 0 := by
  unfold partialLists at h
  have h1 : 𝔭 g₀ ∈ (if g₀ ∈ ({g₀} : Finset 𝔊.Index) then ({fun _ => 0} : Finset (Fin (t g₀) → ℕ))
      else (Fintype.piFinset fun _ : Fin (t g₀) => (𝔊.group g₀).filter fun p => p ∣ n).filter
        fun 𝔮 => Function.Injective 𝔮) := Fintype.mem_piFinset.mp h g₀
  rw [if_pos (Finset.mem_singleton_self g₀)] at h1
  exact Finset.mem_singleton.mp h1

/-- In a list with the mark of the group `g₀` removed, the entries of the other groups are
represented lists. -/
theorem partialLists_apply_of_ne {𝔊 : ActiveGroups} {t : 𝔊.Index → ℕ} {g₀ g : 𝔊.Index} {n : ℕ}
    {𝔭 : (g : 𝔊.Index) → Fin (t g) → ℕ} (h : 𝔭 ∈ partialLists 𝔊 t {g₀} n) (hg : g ≠ g₀) :
    𝔭 g ∈ (Fintype.piFinset fun _ : Fin (t g) => (𝔊.group g).filter fun p => p ∣ n).filter
      fun 𝔮 => Function.Injective 𝔮 := by
  unfold partialLists at h
  have h1 : 𝔭 g ∈ (if g ∈ ({g₀} : Finset 𝔊.Index) then ({fun _ => 0} : Finset (Fin (t g) → ℕ))
      else (Fintype.piFinset fun _ : Fin (t g) => (𝔊.group g).filter fun p => p ∣ n).filter
        fun 𝔮 => Function.Injective 𝔮) := Fintype.mem_piFinset.mp h g
  rw [if_neg (fun h' => hg (Finset.mem_singleton.mp h'))] at h1
  exact h1

/-- The lists with the mark of `g₀` removed are the same at `w / p` and at `w`, for a prime `p`
of `𝒫_{g₀}` dividing `w`. -/
theorem partialLists_div (𝔊 : ActiveGroups) (hprime : ∀ g : 𝔊.Index, ∀ p ∈ 𝔊.group g, p.Prime)
    (hdisj : ∀ g g' : 𝔊.Index, g ≠ g' → Disjoint (𝔊.group g) (𝔊.group g'))
    (t : 𝔊.Index → ℕ) (g₀ : 𝔊.Index) {p w : ℕ} (hpG : p ∈ 𝔊.group g₀) (hpw : p ∣ w) :
    partialLists 𝔊 t {g₀} (w / p) = partialLists 𝔊 t {g₀} w := by
  have hfun : (fun g : 𝔊.Index =>
      if g ∈ ({g₀} : Finset 𝔊.Index) then ({fun _ => 0} : Finset (Fin (t g) → ℕ))
      else (Fintype.piFinset fun _ : Fin (t g) => (𝔊.group g).filter fun q => q ∣ w / p).filter
        fun 𝔮 => Function.Injective 𝔮) =
      fun g : 𝔊.Index =>
      if g ∈ ({g₀} : Finset 𝔊.Index) then ({fun _ => 0} : Finset (Fin (t g) → ℕ))
      else (Fintype.piFinset fun _ : Fin (t g) => (𝔊.group g).filter fun q => q ∣ w).filter
        fun 𝔮 => Function.Injective 𝔮 := by
    funext g
    by_cases hg : g ∈ ({g₀} : Finset 𝔊.Index)
    · rw [if_pos hg, if_pos hg]
    · rw [if_neg hg, if_neg hg]
      have hne : g₀ ≠ g := fun h => hg (Finset.mem_singleton.mpr h.symm)
      rw [filter_dvd_div_of_notMem (hprime g) (hprime g₀ p hpG)
        (Finset.disjoint_left.mp (hdisj g₀ g hne) hpG) hpw]
  exact congrArg (fun F : (g : 𝔊.Index) → Finset (Fin (t g) → ℕ) => Fintype.piFinset F) hfun

/-- "The remaining damping exponent is unchanged" (`[P-06:0691–0692]`). -/
theorem exponent_eq (𝔊 : ActiveGroups) (hprime : ∀ g : 𝔊.Index, ∀ p ∈ 𝔊.group g, p.Prime)
    (hdisj : ∀ g g' : 𝔊.Index, g ≠ g' → Disjoint (𝔊.group g) (𝔊.group g'))
    (t : 𝔊.Index → ℕ) (g₀ : 𝔊.Index) (ht : t g₀ = 1) {p w : ℕ} (hpG : p ∈ 𝔊.group g₀)
    (hpw : p ∣ w) (hsq : ¬ p ^ 2 ∣ w) :
    𝔊.totalHits (w / p) - ∑ g : 𝔊.Index, (if g ∈ ({g₀} : Finset 𝔊.Index) then 0 else t g) =
      𝔊.totalHits w - ∑ g : 𝔊.Index, t g := by
  have h1 := totalHits_div 𝔊 hprime hdisj g₀ hpG hpw hsq
  have h3 : ∑ g ∈ Finset.univ.erase g₀, (if g ∈ ({g₀} : Finset 𝔊.Index) then 0 else t g) =
      ∑ g ∈ Finset.univ.erase g₀, t g :=
    Finset.sum_congr rfl fun g hg =>
      if_neg (fun h => Finset.ne_of_mem_erase hg (Finset.mem_singleton.mp h))
  have e1 : ∑ g : 𝔊.Index, (if g ∈ ({g₀} : Finset 𝔊.Index) then 0 else t g) =
      (if g₀ ∈ ({g₀} : Finset 𝔊.Index) then 0 else t g₀) +
        ∑ g ∈ Finset.univ.erase g₀, (if g ∈ ({g₀} : Finset 𝔊.Index) then 0 else t g) :=
    (Finset.add_sum_erase Finset.univ
      (fun g => if g ∈ ({g₀} : Finset 𝔊.Index) then 0 else t g) (Finset.mem_univ g₀)).symm
  have e2 : ∑ g : 𝔊.Index, t g = t g₀ + ∑ g ∈ Finset.univ.erase g₀, t g :=
    (Finset.add_sum_erase Finset.univ t (Finset.mem_univ g₀)).symm
  rw [e1, e2, h3, if_pos (Finset.mem_singleton_self g₀), ht]
  omega

/-- The product of the reciprocal masses: `V_{g₀}^{-1} ∏_{g ≠ g₀} V_g^{-t_g} = ∏_g V_g^{-t_g}`
when `t_{g₀} = 1`. -/
theorem prod_mass_eq (𝔊 : ActiveGroups) (t : 𝔊.Index → ℕ) (g₀ : 𝔊.Index) (ht : t g₀ = 1) :
    (reciprocalMass (𝔊.group g₀))⁻¹ * ∏ g : 𝔊.Index,
        (if g ∈ ({g₀} : Finset 𝔊.Index) then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) =
      ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹ := by
  have h3 : ∏ g ∈ Finset.univ.erase g₀,
        (if g ∈ ({g₀} : Finset 𝔊.Index) then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) =
      ∏ g ∈ Finset.univ.erase g₀, (reciprocalMass (𝔊.group g) ^ t g)⁻¹ :=
    Finset.prod_congr rfl fun g hg =>
      if_neg (fun h => Finset.ne_of_mem_erase hg (Finset.mem_singleton.mp h))
  have e1 : ∏ g : 𝔊.Index,
        (if g ∈ ({g₀} : Finset 𝔊.Index) then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) =
      (if g₀ ∈ ({g₀} : Finset 𝔊.Index) then 1 else (reciprocalMass (𝔊.group g₀) ^ t g₀)⁻¹) *
        ∏ g ∈ Finset.univ.erase g₀,
          (if g ∈ ({g₀} : Finset 𝔊.Index) then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹) :=
    (Finset.mul_prod_erase Finset.univ
      (fun g => if g ∈ ({g₀} : Finset 𝔊.Index) then 1 else (reciprocalMass (𝔊.group g) ^ t g)⁻¹)
      (Finset.mem_univ g₀)).symm
  have e2 : ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹ =
      (reciprocalMass (𝔊.group g₀) ^ t g₀)⁻¹ *
        ∏ g ∈ Finset.univ.erase g₀, (reciprocalMass (𝔊.group g) ^ t g)⁻¹ :=
    (Finset.mul_prod_erase Finset.univ (fun g => (reciprocalMass (𝔊.group g) ^ t g)⁻¹)
      (Finset.mem_univ g₀)).symm
  rw [e1, e2, h3, if_pos (Finset.mem_singleton_self g₀), ht, pow_one, one_mul]

/-! ### The sum over the lists -/

/-- A represented list at `w` is a prime of `𝒫_{g₀}` dividing `w` together with a list with the
mark of `g₀` removed, when `t_{g₀} = 1`; the test does not see the mark of `g₀`. -/
theorem sum_representedLists_eq (𝔊 : ActiveGroups) (t : 𝔊.Index → ℕ)
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (g₀ : 𝔊.Index) (ht : t g₀ = 1)
    (htest : ∀ 𝔭 𝔭' : (g : 𝔊.Index) → Fin (t g) → ℕ,
      (∀ g : 𝔊.Index, g ≠ g₀ → 𝔭 g = 𝔭' g) → test 𝔭 = test 𝔭') (w : ℕ) :
    ∑ 𝔭 ∈ 𝔊.representedLists t w, test 𝔭 =
      ∑ _p ∈ (𝔊.group g₀).filter (fun p => p ∣ w), ∑ 𝔭 ∈ partialLists 𝔊 t {g₀} w, test 𝔭 := by
  have hsub : Subsingleton (Fin (t g₀)) := by
    rw [ht]
    infer_instance
  have hpos : 0 < t g₀ := by omega
  have hconst : ∀ (v : Fin (t g₀) → ℕ) (i : Fin (t g₀)), (fun _ : Fin (t g₀) => v i) = v :=
    fun v i => funext fun i' => congrArg v (Subsingleton.elim i i')
  refine Eq.trans ?_ (Finset.sum_product' _ _ (fun _ 𝔭 => test 𝔭))
  refine Finset.sum_nbij'
    (fun 𝔭 => (𝔭 g₀ ⟨0, hpos⟩, Function.update 𝔭 g₀ (fun _ => 0)))
    (fun y => Function.update y.2 g₀ (fun _ => y.1)) ?_ ?_ ?_ ?_ ?_
  · -- a represented list gives a prime and a list with the mark removed
    intro 𝔭 h𝔭
    have hall : ∀ g : 𝔊.Index, 𝔭 g ∈
        (Fintype.piFinset fun _ : Fin (t g) => (𝔊.group g).filter fun p => p ∣ w).filter
          fun 𝔮 => Function.Injective 𝔮 := Fintype.mem_piFinset.mp h𝔭
    show (𝔭 g₀ ⟨0, hpos⟩, Function.update 𝔭 g₀ (fun _ => 0)) ∈ _
    refine Finset.mk_mem_product ?_ ?_
    · exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (hall g₀)).1 ⟨0, hpos⟩
    · unfold partialLists
      refine Fintype.mem_piFinset.mpr fun g => ?_
      by_cases hg : g = g₀
      · subst hg
        rw [Function.update_self, if_pos (Finset.mem_singleton_self _)]
        exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hg, if_neg (fun h => hg (Finset.mem_singleton.mp h))]
        exact hall g
  · -- a prime and a list with the mark removed give a represented list
    intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
    show Function.update y.2 g₀ (fun _ => y.1) ∈ 𝔊.representedLists t w
    unfold ActiveGroups.representedLists
    refine Fintype.mem_piFinset.mpr fun g => ?_
    by_cases hg : g = g₀
    · subst hg
      rw [Function.update_self]
      exact Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mpr fun _ => hy1, Function.injective_of_subsingleton _⟩
    · rw [Function.update_of_ne hg]
      exact partialLists_apply_of_ne hy2 hg
  · -- left inverse
    intro 𝔭 _
    show Function.update (Function.update 𝔭 g₀ (fun _ => 0)) g₀ (fun _ => 𝔭 g₀ ⟨0, hpos⟩) = 𝔭
    have h1 : Function.update 𝔭 g₀ (fun _ => 𝔭 g₀ ⟨0, hpos⟩) = Function.update 𝔭 g₀ (𝔭 g₀) :=
      congrArg (Function.update 𝔭 g₀) (hconst (𝔭 g₀) ⟨0, hpos⟩)
    rw [Function.update_idem, h1, Function.update_eq_self]
  · -- right inverse
    intro y hy
    obtain ⟨_, hy2⟩ := Finset.mem_product.mp hy
    have h0 : y.2 g₀ = fun _ => 0 := partialLists_apply_self hy2
    refine Prod.ext ?_ ?_
    · show Function.update y.2 g₀ (fun _ => y.1) g₀ ⟨0, hpos⟩ = y.1
      rw [Function.update_self]
    · show Function.update (Function.update y.2 g₀ (fun _ => y.1)) g₀ (fun _ => 0) = y.2
      rw [Function.update_idem]
      exact (congrArg (Function.update y.2 g₀) h0.symm).trans (Function.update_eq_self g₀ y.2)
  · -- the test does not see the mark of `g₀`
    intro 𝔭 _
    show test 𝔭 = test (Function.update 𝔭 g₀ (fun _ => 0))
    exact htest _ _ fun g hg => (Function.update_of_ne hg _ _).symm

/-! ### The identity -/

/-- **(cor:extract-small)** (`[P-06:0683–0692]`). -/
theorem extractSmallIdentity : ExtractSmallIdentity := by
  intro 𝔊 hprime hdisj q₀ t test i₀ ht htest w _ hsq
  have hclaim : ∀ p ∈ (𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
      (((reciprocalMass (𝔊.group (Sum.inl i₀)))⁻¹ : ℝ) : ℂ) *
          partialWeight 𝔊 q₀ t test {Sum.inl i₀} (w / p) =
        ((q₀ ^ (𝔊.totalHits w - ∑ g : 𝔊.Index, t g) *
            ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹ : ℝ) : ℂ) *
          ∑ 𝔭 ∈ partialLists 𝔊 t {Sum.inl i₀} w, test 𝔭 := by
    intro p hp
    obtain ⟨hpG, hpw⟩ := Finset.mem_filter.mp hp
    unfold partialWeight
    rw [partialLists_div 𝔊 hprime hdisj t (Sum.inl i₀) hpG hpw,
      exponent_eq 𝔊 hprime hdisj t (Sum.inl i₀) ht hpG hpw (hsq p hpG),
      ← prod_mass_eq 𝔊 t (Sum.inl i₀) ht]
    simp only [Complex.ofReal_mul]
    ring
  calc 𝔊.activeWeight q₀ t test w
      = ((q₀ ^ (𝔊.totalHits w - ∑ g : 𝔊.Index, t g) *
            ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹ : ℝ) : ℂ) *
          ∑ 𝔭 ∈ 𝔊.representedLists t w, test 𝔭 := rfl
    _ = ((q₀ ^ (𝔊.totalHits w - ∑ g : 𝔊.Index, t g) *
            ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹ : ℝ) : ℂ) *
          ∑ _p ∈ (𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
            ∑ 𝔭 ∈ partialLists 𝔊 t {Sum.inl i₀} w, test 𝔭 := by
        rw [sum_representedLists_eq 𝔊 t test (Sum.inl i₀) ht htest w]
    _ = ∑ _p ∈ (𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
          ((q₀ ^ (𝔊.totalHits w - ∑ g : 𝔊.Index, t g) *
              ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹ : ℝ) : ℂ) *
            ∑ 𝔭 ∈ partialLists 𝔊 t {Sum.inl i₀} w, test 𝔭 := Finset.mul_sum _ _ _
    _ = ∑ p ∈ (𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
          (((reciprocalMass (𝔊.group (Sum.inl i₀)))⁻¹ : ℝ) : ℂ) *
            partialWeight 𝔊 q₀ t test {Sum.inl i₀} (w / p) :=
        Finset.sum_congr rfl fun p hp => (hclaim p hp).symm
    _ = (((reciprocalMass (𝔊.group (Sum.inl i₀)))⁻¹ : ℝ) : ℂ) *
          ∑ p ∈ (𝔊.group (Sum.inl i₀)).filter (fun p => p ∣ w),
            partialWeight 𝔊 q₀ t test {Sum.inl i₀} (w / p) := (Finset.mul_sum _ _ _).symm
    _ = (((reciprocalMass (𝔊.group (Sum.inl i₀)))⁻¹ : ℝ) : ℂ) *
          primeConv (𝔊.group (Sum.inl i₀)) (partialWeight 𝔊 q₀ t test {Sum.inl i₀}) w := rfl

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
