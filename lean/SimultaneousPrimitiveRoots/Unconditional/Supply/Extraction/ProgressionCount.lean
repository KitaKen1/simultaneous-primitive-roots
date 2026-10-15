module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Objects

/-!
# The count in one progression: (ext:crt-count) with the class

The arithmetic part of [P] Lemma 7.2 (`[P-07:0148–0163]`, with the class of `[PUB-tex:0518–0522]`).

* `shiftSum_eq_zero_of_not_coprime`: for `(b, H) = 1` and `(r, H) > 1` there is no `v` with
  `r ∣ v` and `v ≡ b (mod H)`: the progression sums of Lemma 7.2 are empty.
* `exists_residue_class`: for pairwise coprime `r, H, m` the three conditions `r ∣ u + 1`,
  `u + 1 ≡ b (mod H)`, `m ∣ u` are one residue class of `u` modulo `r H m` ("the Chinese remainder
  theorem", `[P-07:0154]`).
* `abs_shiftSum_dvd_sub_le`: (ext:crt-count),
  `∑_{u ≥ 1, r ∣ u+1, u+1 ≡ b (H), m ∣ u} Φ(u/x) = x/(H r m) ∫Φ + O_Φ(1)`, from smooth summation
  in one progression (`SmoothProgressionCount`, taken here as the hypothesis `hC` with its
  constant `CΦ`; the manuscript's variable `y = u/ℓ` is not needed: the dilation is `1` and the
  modulus is `r H m`).
* `abs_shiftSum_family_dvd_sub_le`: the same for the multiplicity `∑_i 1_{ℓ_i ∣ u}` of a finite
  family of integers `ℓ_i` (the products of the long-prime tuples, or the single integer `1`) and
  a divisor `e` coprime to them.
* `exists_shiftSum_weights`: a shifted sum with a nonnegative factor `g` is a finite sum
  `∑_{u < N} w_u g'(u)` with weights `w_u ≥ 0` supported on the predicate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression

open MeasureTheory

noncomputable section

/-! ### The class and the modulus `r` -/

/-- For `(b, H) = 1` and `(r, H) > 1` no integer is divisible by `r` and `≡ b (mod H)`. -/
theorem not_dvd_and_modEq_of_not_coprime {H b r : ℕ} (hb : b.Coprime H) (hr : ¬ r.Coprime H)
    (v : ℕ) : ¬ (r ∣ v ∧ v ≡ b [MOD H]) := by
  rintro ⟨h1, h2⟩
  apply hr
  have hg1 : Nat.gcd r H ∣ v := (Nat.gcd_dvd_left r H).trans h1
  have hg2 : Nat.gcd r H ∣ b := (Nat.ModEq.dvd_iff h2 (Nat.gcd_dvd_right r H)).mp hg1
  have hg3 : Nat.gcd r H ∣ Nat.gcd b H := Nat.dvd_gcd hg2 (Nat.gcd_dvd_right r H)
  rw [Nat.Coprime.gcd_eq_one hb] at hg3
  exact Nat.eq_one_of_dvd_one hg3

/-- The progression sums of Lemma 7.2 are empty when `(r, H) > 1` (`(b, H) = 1`). -/
theorem shiftSum_eq_zero_of_not_coprime {H b r : ℕ} (hb : b.Coprime H) (hr : ¬ r.Coprime H)
    (Φ : ℝ → ℝ) (x : ℝ) (g : ℕ → ℝ) :
    shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) g = 0 := by
  unfold shiftSum
  refine (finsum_congr fun u => ?_).trans finsum_zero
  exact if_neg (not_dvd_and_modEq_of_not_coprime hb hr (u + 1))

/-- **The Chinese remainder theorem** for the three conditions of Lemma 7.2: for pairwise coprime
`r, H, m` there is a class `a` modulo `r H m` with
`r ∣ u + 1 ∧ u + 1 ≡ b (mod H) ∧ m ∣ u ↔ u ≡ a (mod r H m)`. -/
theorem exists_residue_class {r H m : ℕ} (hrH : r.Coprime H) (hmr : m.Coprime r)
    (hmH : m.Coprime H) (hpos : 0 < r * H * m) (b : ℕ) :
    ∃ a : ℕ, ∀ u : ℕ,
      ((r ∣ u + 1 ∧ u + 1 ≡ b [MOD H]) ∧ m ∣ u) ↔ u ≡ a [MOD r * H * m] := by
  obtain ⟨k₁, hk₁r, hk₁H⟩ := Nat.chineseRemainder hrH 0 b
  have hco : (r * H).Coprime m := Nat.Coprime.mul_left hmr.symm hmH.symm
  obtain ⟨v₀, hv₀1, hv₀m⟩ := Nat.chineseRemainder hco k₁ 1
  have hv₀r : v₀ ≡ 0 [MOD r] := (Nat.ModEq.of_dvd (Nat.dvd_mul_right r H) hv₀1).trans hk₁r
  have hv₀H : v₀ ≡ b [MOD H] := (Nat.ModEq.of_dvd (Nat.dvd_mul_left H r) hv₀1).trans hk₁H
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = r * H * m := ⟨_, rfl⟩
  rw [← hM] at hpos ⊢
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a + 1 = v₀ + M := ⟨v₀ + (M - 1), by omega⟩
  have hshift : a + 1 ≡ v₀ [MOD M] := by
    rw [ha]
    exact Nat.add_mod_right v₀ M
  refine ⟨a, fun u => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have e1 : u + 1 ≡ v₀ [MOD r] := (Nat.modEq_zero_iff_dvd.mpr h1).trans hv₀r.symm
    have e2 : u + 1 ≡ v₀ [MOD H] := h2.trans hv₀H.symm
    have e3 : u + 1 ≡ v₀ [MOD r * H] := (Nat.modEq_and_modEq_iff_modEq_mul hrH).mp ⟨e1, e2⟩
    have e4 : u + 1 ≡ v₀ [MOD m] := by
      have h4 : u + 1 ≡ 0 + 1 [MOD m] := (Nat.modEq_zero_iff_dvd.mpr h3).add_right 1
      rw [zero_add] at h4
      exact h4.trans hv₀m.symm
    have e5 : u + 1 ≡ v₀ [MOD M] := by
      rw [hM]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨e3, e4⟩
    exact Nat.ModEq.add_right_cancel' 1 (e5.trans hshift.symm)
  · intro h
    have e5 : u + 1 ≡ v₀ [MOD M] := (h.add_right 1).trans hshift
    rw [hM] at e5
    obtain ⟨e3, e4⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hco).mpr e5
    obtain ⟨e1, e2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hrH).mpr e3
    refine ⟨⟨Nat.modEq_zero_iff_dvd.mp (e1.trans hv₀r), e2.trans hv₀H⟩, ?_⟩
    have h4 : u + 1 ≡ 0 + 1 [MOD m] := by
      rw [zero_add]
      exact e4.trans hv₀m
    exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' 1 h4)

/-! ### (ext:crt-count) -/

section Count

variable {Φ : ℝ → ℝ} {CΦ : ℝ}

/-- **(ext:crt-count) with the class** (`[P-07:0155–0163]`, `[PUB-tex:0518–0521]`): for pairwise
coprime `r, H, m ≥ 1`,

`| ∑_{u ≥ 0, r ∣ u+1, u+1 ≡ b (H), m ∣ u} Φ(u/x) - x/(H r m) ∫Φ | ≤ C_Φ`,

where `C_Φ` is the constant of `SmoothProgressionCount` for `Φ` (hypothesis `hC`). -/
theorem abs_shiftSum_dvd_sub_le
    (hC : ∀ x : ℝ, 0 < x → ∀ ℓ m a : ℕ, 0 < ℓ → 0 < m →
      |(∑ᶠ y : ℕ, if y ≡ a [MOD m] then Φ ((ℓ : ℝ) * (y : ℝ) / x) else 0) -
        x / ((ℓ : ℝ) * (m : ℝ)) * ∫ t, Φ t| ≤ CΦ)
    {x : ℝ} (hx : 0 < x) {r H m : ℕ} (hr : 0 < r) (hH : 0 < H) (hm : 0 < m)
    (hrH : r.Coprime H) (hmr : m.Coprime r) (hmH : m.Coprime H) (b : ℕ) :
    |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) (fun u => if m ∣ u then (1 : ℝ) else 0) -
        x / ((H : ℝ) * (r : ℝ) * (m : ℝ)) * ∫ t, Φ t| ≤ CΦ := by
  have hpos : 0 < r * H * m := Nat.mul_pos (Nat.mul_pos hr hH) hm
  obtain ⟨a, ha⟩ := exists_residue_class hrH hmr hmH hpos b
  have hsum : shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
      (fun u => if m ∣ u then (1 : ℝ) else 0) =
      ∑ᶠ y : ℕ, if y ≡ a [MOD r * H * m] then Φ ((y : ℝ) / x) else 0 := by
    unfold shiftSum
    refine finsum_congr fun u => ?_
    beta_reduce
    by_cases h1 : r ∣ u + 1 ∧ u + 1 ≡ b [MOD H]
    · by_cases h2 : m ∣ u
      · have h3 : u ≡ a [MOD r * H * m] := (ha u).mp ⟨h1, h2⟩
        rw [if_pos h1, if_pos h2, mul_one, if_pos h3]
      · have h3 : ¬ u ≡ a [MOD r * H * m] := fun h => h2 ((ha u).mpr h).2
        rw [if_pos h1, if_neg h2, mul_zero, if_neg h3]
    · have h3 : ¬ u ≡ a [MOD r * H * m] := fun h => h1 ((ha u).mpr h).1
      rw [if_neg h1, if_neg h3]
  have h := hC x hx 1 (r * H * m) a one_pos hpos
  simp only [Nat.cast_one, one_mul] at h
  have e : x / ((H : ℝ) * (r : ℝ) * (m : ℝ)) = x / ((r * H * m : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, mul_comm (H : ℝ) (r : ℝ)]
  rw [hsum, e]
  exact h

/-- **(ext:crt-count) for a family of long divisors**: for integers `ℓ_i ≥ 1` and `e ≥ 1`, all
coprime to `r` and to `H`, and `(ℓ_i, e) = 1`,

`| ∑_{u, r ∣ u+1, u+1 ≡ b (H)} Φ(u/x) #{i : ℓ_i ∣ u} 1_{e ∣ u}
    - x/(H r) ∫Φ · (∑_i 1/ℓ_i) · 1/e | ≤ #I · C_Φ`. -/
theorem abs_shiftSum_family_dvd_sub_le {R : ℝ} (hR : ∀ t, R < t → Φ t = 0)
    (hC : ∀ x : ℝ, 0 < x → ∀ ℓ m a : ℕ, 0 < ℓ → 0 < m →
      |(∑ᶠ y : ℕ, if y ≡ a [MOD m] then Φ ((ℓ : ℝ) * (y : ℝ) / x) else 0) -
        x / ((ℓ : ℝ) * (m : ℝ)) * ∫ t, Φ t| ≤ CΦ)
    {x : ℝ} (hx : 0 < x) {r H : ℕ} (hr : 0 < r) (hH : 0 < H) (hrH : r.Coprime H) (b : ℕ)
    {ι : Type*} (I : Finset ι) (ℓ : ι → ℕ) {e : ℕ} (he : 0 < e) (her : e.Coprime r)
    (heH : e.Coprime H) (hℓ0 : ∀ i ∈ I, 0 < ℓ i) (hℓr : ∀ i ∈ I, (ℓ i).Coprime r)
    (hℓH : ∀ i ∈ I, (ℓ i).Coprime H) (hℓe : ∀ i ∈ I, (ℓ i).Coprime e) :
    |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
        (fun u => (∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0) *
          (if e ∣ u then (1 : ℝ) else 0)) -
      x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * (∑ i ∈ I, 1 / (ℓ i : ℝ)) * (1 / (e : ℝ))| ≤
      (I.card : ℝ) * CΦ := by
  have hpt : ∀ u : ℕ, (∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0) *
      (if e ∣ u then (1 : ℝ) else 0) = ∑ i ∈ I, (if ℓ i * e ∣ u then (1 : ℝ) else 0) := by
    intro u
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h1 : ℓ i ∣ u
    · by_cases h2 : e ∣ u
      · have h3 : ℓ i * e ∣ u := (hℓe i hi).mul_dvd_of_dvd_of_dvd h1 h2
        rw [if_pos h1, if_pos h2, mul_one, if_pos h3]
      · have h3 : ¬ ℓ i * e ∣ u := fun h => h2 ((Nat.dvd_mul_left e (ℓ i)).trans h)
        rw [if_pos h1, if_neg h2, mul_zero, if_neg h3]
    · have h3 : ¬ ℓ i * e ∣ u := fun h => h1 ((Nat.dvd_mul_right (ℓ i) e).trans h)
      rw [if_neg h1, zero_mul, if_neg h3]
  have hterm : ∀ i ∈ I, |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
        (fun u => if ℓ i * e ∣ u then (1 : ℝ) else 0) -
      x / ((H : ℝ) * (r : ℝ) * ((ℓ i * e : ℕ) : ℝ)) * ∫ t, Φ t| ≤ CΦ := fun i hi =>
    abs_shiftSum_dvd_sub_le hC hx hr hH (Nat.mul_pos (hℓ0 i hi) he) hrH
      (Nat.Coprime.mul_left (hℓr i hi) her) (Nat.Coprime.mul_left (hℓH i hi) heH) b
  have hmain : x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * (∑ i ∈ I, 1 / (ℓ i : ℝ)) *
      (1 / (e : ℝ)) =
      ∑ i ∈ I, x / ((H : ℝ) * (r : ℝ) * ((ℓ i * e : ℕ) : ℝ)) * ∫ t, Φ t := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_mul]
    ring
  rw [shiftSum_congr Φ x _ hpt, shiftSum_finset_sum hR hx, hmain, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ I, (shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
          (fun u => if ℓ i * e ∣ u then (1 : ℝ) else 0) -
        x / ((H : ℝ) * (r : ℝ) * ((ℓ i * e : ℕ) : ℝ)) * ∫ t, Φ t)|
      ≤ ∑ i ∈ I, |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
          (fun u => if ℓ i * e ∣ u then (1 : ℝ) else 0) -
        x / ((H : ℝ) * (r : ℝ) * ((ℓ i * e : ℕ) : ℝ)) * ∫ t, Φ t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, CΦ := Finset.sum_le_sum hterm
    _ = (I.card : ℝ) * CΦ := by rw [Finset.sum_const, nsmul_eq_mul]

end Count

/-! ### Shifted sums as weighted finite sums -/

open _root_.Classical in
/-- A shifted sum with a nonnegative factor `g` is a finite sum with nonnegative weights
`w_u = 1_{P(u+1)} Φ(u/x) g(u)`, supported on the predicate. -/
theorem exists_shiftSum_weights {Φ : ℝ → ℝ} {R x : ℝ} (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (P : ℕ → Prop) {g : ℕ → ℝ} (hg : ∀ u, 0 ≤ g u) :
    ∃ (N : ℕ) (w : ℕ → ℝ), (∀ u, 0 ≤ w u) ∧ (∀ u, w u ≠ 0 → P (u + 1)) ∧
      ∀ g' : ℕ → ℝ,
        shiftSum Φ x P (fun u => g u * g' u) = ∑ u ∈ Finset.range N, w u * g' u := by
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, ∀ u, w u = if P (u + 1) then Φ ((u : ℝ) / x) * g u else 0 :=
    ⟨fun u => if P (u + 1) then Φ ((u : ℝ) / x) * g u else 0, fun _ => rfl⟩
  refine ⟨⌊R * x⌋₊ + 1, w, fun u => ?_, fun u hu => ?_, fun g' => ?_⟩
  · rw [hw u]
    by_cases h : P (u + 1)
    · rw [if_pos h]
      exact mul_nonneg (hΦ0 _) (hg u)
    · rw [if_neg h]
  · by_contra h
    apply hu
    rw [hw u]
    exact if_neg h
  · rw [shiftSum_eq_sum hR hx]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hw u]
    by_cases h : P (u + 1)
    · rw [if_pos h, if_pos h, mul_assoc]
    · rw [if_neg h, if_neg h, zero_mul]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression
