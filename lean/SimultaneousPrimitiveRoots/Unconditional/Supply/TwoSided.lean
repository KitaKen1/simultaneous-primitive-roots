module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Basic

/-!
# The two-sided marked correlation ([P] Theorem 6.1) with a joint residue weight, and (cor:SM)

[P] Theorem 6.1 (`[P-06:0055–0077]`) bounds, for the centered endpoint
`F_x(n) = 𝒲(n) (∑_𝔩 1_{l ∣ n} - C_x)`,

`∑_{w ≥ 1} Ψ(w/x)/w · F_x(w) G(w+1) W_1(w) W_1(w+1) ≪_A L^{-A}`,

uniformly over the active groups and the slot intervals. The first endpoint is this particular
`F_x`, and the second endpoint `G` is invariant under the active primes, so the theorem as stated
does not contain a residue condition on `w + 1`. The public paper carries the class
`w + 1 ≡ b (mod H)` as a *joint* factor `𝓑(w, w+1)` of the two endpoints
(`[PUB-tex:0462–0501]`, `[PUB-ja:0416–0445]`): `𝓑(s,t) = 1_{(t,H)=1} 1_{bs ≡ (b-1)t (H)}`.

* `ActiveGroups`, `ActiveGroups.Admissible`: the active groups `𝒫_g`, `g ∈ 𝒮 ⊔ ℬ`
  (`[P-06:0010–0023]`).
* `freePart`, `ActiveGroups.activeWeight`, `ActiveGroups.oneMark`: `n_*`, `W_𝐭^𝐛`, `W_1`
  (`[P-06:0026–0044]`).
* `JointResidueWeight H`, `classWeight H b`: a `[0,1]`-valued function on `(ℤ/H)²` that is
  invariant under simultaneous multiplication by units; `𝓑_{H,b}`.
* `TwoSidedCorrelation d H 𝔅`: **Theorem 6.1^{𝔅}**; `TwoSidedFixedClass d` is the case
  `𝔅 = 𝓑_{H,b}` for all `H`, `b`, and `H = 1` is [P] Theorem 6.1.
* `EndpointEnergyAt d B C`: **(cor:SM)** (`[P-06:0544–0550]`) with denominators `k ≤ L^B` and
  times `|τ| ≤ x L^C`; `EndpointEnergy d` is the statement for all `B, C > 0`, the form
  (eq:energy-input) of the public paper (`[PUB-tex:0199–0206]`), and `EndpointEnergyPaper d` is
  [P]'s form `B = C_6`, `C = C_6 + 1` for all `C_6 > 0`.

`TwoSidedCorrelation` and `EndpointEnergy` are propositions (`def … : Prop`); they are not proved
here.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply

open Filter Asymptotics
open scoped Topology ContDiff

noncomputable section

/-- `e(θ) = exp(2π i θ)` (`[P-02:0007]`). -/
def addChar (θ : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)

/-! ### Active groups -/

/-- The fixed positive constants `c_0, C_0, v_-, v_+` of `[P-06:0012–0017]`. -/
structure ActiveGroupConstants where
  /-- `c_0`: the number of groups of each kind is at least `c_0 log L` -/
  c₀ : ℝ
  /-- `C_0`: the number of groups of each kind is at most `C_0 log L` -/
  C₀ : ℝ
  /-- `v_-`: lower bound for the reciprocal masses `V_g` -/
  vlo : ℝ
  /-- `v_+`: upper bound for the reciprocal masses `V_g` -/
  vhi : ℝ
  c₀_pos : 0 < c₀
  C₀_pos : 0 < C₀
  vlo_pos : 0 < vlo
  vhi_pos : 0 < vhi

/-- A system of active groups `𝒫_g`, indexed by `𝒮 ⊔ ℬ` with `𝒮 = Fin numSmall` (small groups) and
`ℬ = Fin numBig` (big groups) (`[P-06:0010–0012]`). The conditions are in
`ActiveGroups.Admissible`. -/
structure ActiveGroups where
  /-- `|𝒮|` -/
  numSmall : ℕ
  /-- `|ℬ|` -/
  numBig : ℕ
  /-- the groups `𝒫_g` -/
  group : Fin numSmall ⊕ Fin numBig → Finset ℕ

namespace ActiveGroups

/-- The index set `𝒮 ⊔ ℬ`. -/
abbrev Index (𝔊 : ActiveGroups) : Type := Fin 𝔊.numSmall ⊕ Fin 𝔊.numBig

/-- `𝒫 = ⋃_g 𝒫_g` (`[P-06:0024]`). -/
def allPrimes (𝔊 : ActiveGroups) : Finset ℕ := Finset.univ.biUnion 𝔊.group

/-- `s_P = |𝒮| + |ℬ|` (`[P-06:0024]`). -/
def numGroups (𝔊 : ActiveGroups) : ℕ := 𝔊.numSmall + 𝔊.numBig

/-- `ω_P(n) = ∑_g ω_g(n)` (`[P-06:0029]`). -/
def totalHits (𝔊 : ActiveGroups) (n : ℕ) : ℕ := ∑ g : 𝔊.Index, primeHits (𝔊.group g) n

/-- **The active-group hypotheses** (`[P-06:0010–0023]`, (cor:groups)), at `x`, for the constants
`P`: pairwise disjoint groups of primes; `c_0 log L ≤ |𝒮|, |ℬ| ≤ C_0 log L`;
`v_- ≤ V_g ≤ v_+`; small groups in `[exp(L^{.27}), exp(L^{.36})]`, big groups in
`[exp(L^{.39}), exp(L^{.46})]`; every big group is the set of all primes of an interval.

Disjointness from the bands of `𝒲` (`[PUB-tex:0148]`) is automatic for large `x`
(`a_i < 0.2 < 0.27`) and is not a hypothesis in [P]. -/
structure Admissible (P : ActiveGroupConstants) (x : ℝ) (𝔊 : ActiveGroups) : Prop where
  prime : ∀ g : 𝔊.Index, ∀ p ∈ 𝔊.group g, p.Prime
  disjoint : ∀ g g' : 𝔊.Index, g ≠ g' → Disjoint (𝔊.group g) (𝔊.group g')
  numSmall_ge : P.c₀ * Real.log (Real.log x) ≤ (𝔊.numSmall : ℝ)
  numSmall_le : (𝔊.numSmall : ℝ) ≤ P.C₀ * Real.log (Real.log x)
  numBig_ge : P.c₀ * Real.log (Real.log x) ≤ (𝔊.numBig : ℝ)
  numBig_le : (𝔊.numBig : ℝ) ≤ P.C₀ * Real.log (Real.log x)
  mass_ge : ∀ g : 𝔊.Index, P.vlo ≤ reciprocalMass (𝔊.group g)
  mass_le : ∀ g : 𝔊.Index, reciprocalMass (𝔊.group g) ≤ P.vhi
  small_range : ∀ i : Fin 𝔊.numSmall, ∀ p ∈ 𝔊.group (Sum.inl i),
    Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ))
  big_range : ∀ j : Fin 𝔊.numBig, ∀ p ∈ 𝔊.group (Sum.inr j),
    Real.exp (Real.log x ^ (0.39 : ℝ)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ))
  big_interval : ∀ j : Fin 𝔊.numBig, ∀ p₁ ∈ 𝔊.group (Sum.inr j), ∀ p₂ ∈ 𝔊.group (Sum.inr j),
    ∀ p : ℕ, p.Prime → p₁ ≤ p → p ≤ p₂ → p ∈ 𝔊.group (Sum.inr j)

/-- The represented lists at `n` for the vector `𝐭 = (t_g)`: for each group `g`, `t_g` ordered
distinct prime divisors of `n` from `𝒫_g` (`[P-06:0033–0035]`). -/
def representedLists (𝔊 : ActiveGroups) (t : 𝔊.Index → ℕ) (n : ℕ) :
    Finset ((g : 𝔊.Index) → Fin (t g) → ℕ) :=
  Fintype.piFinset fun g : 𝔊.Index =>
    (Fintype.piFinset fun _ : Fin (t g) => (𝔊.group g).filter fun p => p ∣ n).filter
      fun 𝔭 => Function.Injective 𝔭

/-- The active marked weight
`W_𝐭^𝐛(n) = q_0^{ω_P(n) - ∑_g t_g} ∏_g V_g^{-t_g} ∑_{represented lists 𝔭 at n} 𝐛(𝔭)`
(`[P-06:0036–0042]`, (cor:marked-weight)); it vanishes when `n` has no represented list
(`[P-06:0043]`). The exponent is written with truncated subtraction: it is
`ω_P(n) - ∑_g t_g ≥ 0` whenever a list exists. -/
def activeWeight (𝔊 : ActiveGroups) (q₀ : ℝ) (t : 𝔊.Index → ℕ)
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (n : ℕ) : ℂ :=
  ((q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, t g) *
      ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹ : ℝ) : ℂ) *
    ∑ 𝔭 ∈ 𝔊.representedLists t n, test 𝔭

/-- `W_1 = W_{(1,…,1)}^{1}`, the active one-mark weight (`[P-06:0043–0044]`); it equals
`q_0^{ω_P(n) - s_P} ∏_g ω_g(n) / V_g` (`ActiveGroups.oneMark_eq`). -/
def oneMark (𝔊 : ActiveGroups) (q₀ : ℝ) (n : ℕ) : ℂ :=
  𝔊.activeWeight q₀ (fun _ => 1) (fun _ => 1) n

end ActiveGroups

/-- `n_* = ∏_{p ∉ 𝒫} p^{v_p(n)}`: the part of `n` free of the primes of `𝒫`, with multiplicities
removed entirely (`[P-06:0026–0032]`). -/
def freePart (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ∉ P), p ^ n.factorization p

/-! ### Joint residue weights -/

/-- **A joint residue weight modulo `H`**: a function `𝔅 : (ℤ/H)² → [0, 1]` with
`𝔅(us, ut) = 𝔅(s, t)` for every unit `u`. In Theorem 6.1^{𝔅} it enters as `𝔅(w, w+1)`.

The three properties are those used in the public paper's proof for `𝓑_{H,b}`
(`[PUB-tex:0479–0501]`): a function on `(ℤ/H)²` is a combination of at most `H²` products of
residue indicators with coefficients in `[0,1]`; the invariance is (eq:B-shared); and for a fixed
shift `d`, `w ↦ 𝔅(w, w+d)` is a combination of at most `H` residue indicators (the role of
(eq:B-shift)). The fixed-divisor factor `Δ_D(s) = 1_{D ∣ s}` of `prop:fd` is also of this
kind. -/
@[ext]
structure JointResidueWeight (H : ℕ) where
  /-- the weight -/
  toFun : ZMod H → ZMod H → ℝ
  nonneg : ∀ s t, 0 ≤ toFun s t
  le_one : ∀ s t, toFun s t ≤ 1
  /-- invariance under simultaneous multiplication by a unit (eq:B-shared) -/
  unit_mul : ∀ (u : (ZMod H)ˣ) (s t : ZMod H), toFun (u * s) (u * t) = toFun s t

/-- The trivial joint weight `1`. -/
def JointResidueWeight.one (H : ℕ) : JointResidueWeight H where
  toFun := fun _ _ => 1
  nonneg := fun _ _ => zero_le_one
  le_one := fun _ _ => le_rfl
  unit_mul := fun _ _ _ => rfl

open _root_.Classical in
/-- `𝓑_{H,b}(s,t) = 1_{(t,H)=1} 1_{bs ≡ (b-1)t (mod H)}` (`[PUB-tex:0464–0468]`, (6.1) of
`[PUB-ja:0420–0424]`). -/
def classIndicator (H b : ℕ) (s t : ZMod H) : ℝ :=
  if IsUnit t ∧ (b : ZMod H) * s = ((b : ZMod H) - 1) * t then 1 else 0

/-- (eq:B-shared) `[PUB-tex:0472]`: `𝓑(Rs, Rt) = 𝓑(s, t)` for `(R, H) = 1`. -/
theorem classIndicator_unit_mul (H b : ℕ) (u : (ZMod H)ˣ) (s t : ZMod H) :
    classIndicator H b (u * s) (u * t) = classIndicator H b s t := by
  classical
  unfold classIndicator
  refine if_congr ?_ rfl rfl
  have h1 : IsUnit ((u : ZMod H) * t) ↔ IsUnit t := Units.isUnit_units_mul u t
  have h2 : (b : ZMod H) * (↑u * s) = ((b : ZMod H) - 1) * (↑u * t) ↔
      (b : ZMod H) * s = ((b : ZMod H) - 1) * t := by
    constructor
    · intro h
      have h' : (u : ZMod H) * ((b : ZMod H) * s) =
          (u : ZMod H) * (((b : ZMod H) - 1) * t) := by
        linear_combination h
      exact u.isUnit.mul_left_cancel h'
    · intro h
      linear_combination (u : ZMod H) * h
  rw [h1, h2]

/-- The joint residue weight `𝓑_{H,b}` of the class `b (mod H)`. -/
def classWeight (H b : ℕ) : JointResidueWeight H where
  toFun := classIndicator H b
  nonneg := by
    intro s t
    unfold classIndicator
    split_ifs <;> norm_num
  le_one := by
    intro s t
    unfold classIndicator
    split_ifs <;> norm_num
  unit_mul := classIndicator_unit_mul H b

/-- (eq:B-unit) `[PUB-tex:0471]`: `𝓑(u, u+1) = 1_{u+1 ≡ b (mod H)}` for `(b, H) = 1`. -/
theorem classIndicator_succ {H b : ℕ} (hb : b.Coprime H) (u : ℕ) :
    classIndicator H b (u : ZMod H) ((u + 1 : ℕ) : ZMod H) =
      if u + 1 ≡ b [MOD H] then 1 else 0 := by
  classical
  have key : (IsUnit (((u + 1 : ℕ) : ZMod H)) ∧
      (b : ZMod H) * (u : ZMod H) = ((b : ZMod H) - 1) * ((u + 1 : ℕ) : ZMod H)) ↔
        u + 1 ≡ b [MOD H] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    constructor
    · rintro ⟨_, h⟩
      push_cast at h ⊢
      linear_combination h
    · intro h
      refine ⟨?_, ?_⟩
      · rw [h]
        exact (ZMod.isUnit_iff_coprime b H).mpr hb
      · push_cast at h ⊢
        linear_combination h
  unfold classIndicator
  exact if_congr key rfl rfl

/-- (eq:B-shift) `[PUB-tex:0473–0477]`: `𝓑(w, w+d) = 1_{w ≡ (b-1)d (mod H)}` for `(d, H) = 1` and
`(b, H) = 1`. -/
theorem classIndicator_shift {H b : ℕ} (hb : b.Coprime H) {d : ZMod H} (hd : IsUnit d)
    (w : ZMod H) :
    classIndicator H b w (w + d) = if w = ((b : ZMod H) - 1) * d then 1 else 0 := by
  classical
  have hbu : IsUnit (b : ZMod H) := (ZMod.isUnit_iff_coprime b H).mpr hb
  have key : (IsUnit (w + d) ∧ (b : ZMod H) * w = ((b : ZMod H) - 1) * (w + d)) ↔
      w = ((b : ZMod H) - 1) * d := by
    constructor
    · rintro ⟨_, h⟩
      linear_combination h
    · intro h
      have hwd : w + d = (b : ZMod H) * d := by linear_combination h
      refine ⟨?_, by linear_combination h⟩
      rw [hwd]
      exact hbu.mul hd
  unfold classIndicator
  exact if_congr key rfl rfl

/-- For `H = 1` the class weight is `1`. -/
theorem classIndicator_one (b : ℕ) (s t : ZMod 1) : classIndicator 1 b s t = 1 := by
  unfold classIndicator
  exact if_pos ⟨isUnit_of_subsingleton t, Subsingleton.elim _ _⟩

/-! ### Theorem 6.1 with a joint residue weight -/

/-- The centered first endpoint `F_x(n) = 𝒲(n) (∑_𝔩 1_{l ∣ n} - C_x)` (`[P-06:0060–0065]`,
(cor:centered-core)). -/
def centeredCore (q : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) {d : ℕ} (S : Fin d → Finset ℕ)
    (n : ℕ) : ℝ :=
  markedWeight q 𝔞 x n * ((slotCount S n : ℝ) - slotMass S)

/-- The hypotheses on the second endpoint (`[P-06:0066–0067]`): `G(n) = G(n_*)` and
`|G(n)| ≤ L^C τ(n_*)^C`, for positive integers `n`. -/
structure CoreAdmissible (𝔊 : ActiveGroups) (x C : ℝ) (G : ℕ → ℂ) : Prop where
  /-- `G(n) = G(n_*)` -/
  invariant : ∀ n : ℕ, 0 < n → G n = G (freePart 𝔊.allPrimes n)
  /-- `|G(n)| ≤ L^C τ(n_*)^C` -/
  growth : ∀ n : ℕ, 0 < n →
    ‖G n‖ ≤ Real.log x ^ C * ((freePart 𝔊.allPrimes n).divisors.card : ℝ) ^ C

/-- The two-sided sum
`∑_{w ≥ 1} Ψ(w/x)/w · 𝔅(w, w+1) F_x(w) G(w+1) W_1(w) W_1(w+1)`
(`[P-06:0069–0072]`, (eq:two-sided), with the joint factor `𝔅(w, w+1)`). The term `w = 0`
vanishes (`1/0 = 0` in Lean, and `Ψ(0) = 0` in the statements). -/
def twoSidedSum (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups) {d : ℕ}
    (S : Fin d → Finset ℕ) {H : ℕ} (𝔅 : JointResidueWeight H) (Ψ : ℝ → ℂ) (G : ℕ → ℂ) : ℂ :=
  ∑ᶠ w : ℕ, Ψ ((w : ℝ) / x) / (w : ℂ) *
    ((𝔅.toFun (w : ZMod H) ((w + 1 : ℕ) : ZMod H) : ℝ) : ℂ) *
    ((centeredCore q 𝔞 x S w : ℝ) : ℂ) * G (w + 1) * 𝔊.oneMark q₀ w * 𝔊.oneMark q₀ (w + 1)

/-- **Theorem 6.1^{𝔅}: the two-sided correlation with a joint residue weight**, for `d` slots.

Fixed data, in this order: `ε`; the dampings `q, q_0 ∈ (0,1)`; the `K` inert bands `𝔞`; the
active-group constants `P`; the exponent `C` of the growth of `G`; the smooth compactly supported
`Ψ : (0,∞) → ℂ`; the saving `A`. (`d`, `H` and `𝔅` are parameters of the definition and are fixed
first.) Then there are a constant `M` and a threshold `x₀` such that for all `x ≥ x₀`, **all**
admissible active groups, **all** admissible slot systems and **all** `G` with `G(n) = G(n_*)`,
`|G(n)| ≤ L^C τ(n_*)^C`,

`|∑_{w ≥ 1} Ψ(w/x)/w · 𝔅(w, w+1) F_x(w) G(w+1) W_1(w) W_1(w+1)| ≤ M L^{-A}`.

Source: `[P-06:0055–0077]` for `𝔅 = 1`; by `[P-06:0073–0076]` the constant and the threshold for
`x` may depend on all the fixed data, the inert bands included, and the bound is uniform in the
active groups and in the slot intervals. For `𝔅 = 𝓑_{H,b}`: `[PUB-tex:0479–0501]` and (2.6), §6.1
of `[PUB-ja:0123–0128, 0416–0445]` (written there for `d = 1`). `G` is not
fixed data: in the application it depends on `x` and on the active set (`[P-07:0559–0572]`), and
the proof uses only the two stated properties, so the bound is uniform in `G`.

The statement is meant for `H ≥ 1` (for `H = 0`, `ZMod 0 = ℤ` and a weight need not be
periodic); `TwoSidedFixedClass` has the hypothesis `0 < H`. -/
def TwoSidedCorrelation (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ q q₀ : ℝ, 0 < q → q < 1 → 0 < q₀ → q₀ < 1 →
    ∀ (K : ℕ) (𝔞 : MarkingArray K) (P : ActiveGroupConstants) (C : ℝ) (Ψ : ℝ → ℂ),
      ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Set.Ioi 0 →
        ∀ A : ℝ, 0 < A → ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
          ∀ 𝔊 : ActiveGroups, 𝔊.Admissible P x →
            ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
              ∀ G : ℕ → ℂ, CoreAdmissible 𝔊 x C G →
                ‖twoSidedSum q q₀ 𝔞 x 𝔊 S 𝔅 Ψ G‖ ≤ M * Real.log x ^ (-A)

/-- **Theorem 6.1 with the class factor `1_{w+1 ≡ b (mod H)}`**, for every modulus and every
reduced class (the conclusion of `[PUB-tex:0479–0501]`). -/
def TwoSidedFixedClass (d : ℕ) : Prop :=
  ∀ H b : ℕ, 0 < H → b.Coprime H → TwoSidedCorrelation d H (classWeight H b)

/-- **[P] Theorem 6.1** `thm:two-sided` (`[P-06:0055–0077]`), for `d` slots. -/
def TwoSided (d : ℕ) : Prop := TwoSidedCorrelation d 1 (JointResidueWeight.one 1)

/-! ### The endpoint estimate (cor:SM) -/

/-- The first endpoint of a comparison correlation (`[P-06:0635–0642]`, (cor:U-form)):
`𝒰(w) = ψ_1(w/Y) w^{iσ} (∑_𝔩 1_{l ∣ w} - C_x) H_marks(w)` with
`H_marks(n) = 𝒲(n) W_𝐭^𝐛(n)` (`[P-06:0567]`). -/
def comparisonEndpoint (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups) {d : ℕ}
    (S : Fin d → Finset ℕ) (t : 𝔊.Index → ℕ) (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ)
    (ψ₁ : ℝ → ℂ) (σ Y : ℝ) (w : ℕ) : ℂ :=
  ψ₁ ((w : ℝ) / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) *
    ((centeredCore q 𝔞 x S w : ℝ) : ℂ) * 𝔊.activeWeight q₀ t test w

/-- `Y^{-1} ∑_w 𝒰(w) e(hw/k) w^{iτ}`, the normalized twisted Dirichlet polynomial of
`[P-06:0546–0547]`. -/
def endpointPolynomial (U : ℕ → ℂ) (Y : ℝ) (h : ℤ) (k : ℕ) (τ : ℝ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑ᶠ w : ℕ, U w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
    (w : ℂ) ^ ((τ : ℂ) * Complex.I)

/-- **(cor:SM) with denominators `k ≤ L^B` and times `|τ| ≤ x L^C`**: for every fixed `A > 0`,

`∫_{|τ| ≤ x L^C} |Y^{-1} ∑_w 𝒰(w) e(hw/k) w^{iτ}|² dτ ≪_A L^{-A}`.

Sources: `[P-06:0544–0550]` (cor:SM), which is the case `B = C_6`, `C = C_6 + 1`
(`k ≤ L^{C_6}`, `T_0 = L Y / H = x L^{C_6 + 1}`, for the exponent `C_6` of (cor:major-arcs)
`[P-06:0455–0460]`); `[PUB-tex:0181–0206]` (eq:energy-input), which has the two exponents.

Fixed data, in this order (`d`, `B`, `C` are parameters of the definition and are fixed first):
`ε`; `q, q_0`; the bands `𝔞`; the active-group constants `P`; the bound `m'` for the `t_g`; the
support `[a₁, a₂] ⊂ (0, ∞)` of the cutoff and the exponents `Dψ j` bounding its derivatives; the
exponent `Cσ` of the twist; the constants `c₁, c₂` of the scale; and the saving `A`. Then there are
`M` and `x₀` such that the bound holds for all `x ≥ x₀`, uniformly in: the active groups; the
slots; the scale `Y = x H'` with `exp(2 L^{.39} - c₁) ≤ H' ≤ exp(c₂ L^{.46} log L)`
(`[P-06:0385–0389]`, (cor:comparison-scales): `H' = U_1 U_2`, `U_i ≥ exp(L^{.39} - O(1))`,
`H' ≤ exp(O_{m_0}(L^{.46} log L))`); the vector `(t_g)` with `1 ≤ t_g ≤ m'` and `t_g = 1` on
small groups; the list test of modulus at most one depending only on big-group marks
(`[P-06:0403–0405, 0683–0684]`, `[PUB-tex:0194–0197]`); the twist `|σ| ≤ L^{Cσ}`; the cutoff
`ψ_1` (`[P-06:0641–0642]`: its support is a fixed compact set, and its rescaled derivatives and
`|σ|` are bounded by fixed powers of `L`); the denominator `k ≤ L^B` and the numerator `h`.

Choices: `h` is not required to be coprime to `k` (`e(hw/k)` depends only on the reduced fraction,
whose denominator is at most `k`; frequency zero is included, `[PUB-tex:0206]`). The derivative
bounds of `ψ_1` are given by one exponent `Dψ j` for each order `j`. -/
def EndpointEnergyAt (d : ℕ) (B C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ q q₀ : ℝ, 0 < q → q < 1 → 0 < q₀ → q₀ < 1 →
    ∀ (K : ℕ) (𝔞 : MarkingArray K) (P : ActiveGroupConstants) (m' : ℕ) (a₁ a₂ : ℝ),
      0 < a₁ → a₁ ≤ a₂ → ∀ (Dψ : ℕ → ℝ) (Cσ c₁ c₂ A : ℝ), 0 < A →
        ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
          ∀ 𝔊 : ActiveGroups, 𝔊.Admissible P x →
          ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
          ∀ Y : ℝ, x * Real.exp (2 * Real.log x ^ (0.39 : ℝ) - c₁) ≤ Y →
            Y ≤ x * Real.exp (c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) →
          ∀ t : 𝔊.Index → ℕ, (∀ g, 1 ≤ t g ∧ t g ≤ m') →
            (∀ i : Fin 𝔊.numSmall, t (Sum.inl i) = 1) →
          ∀ test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ, (∀ 𝔭, ‖test 𝔭‖ ≤ 1) →
            (∀ 𝔭 𝔭' : (g : 𝔊.Index) → Fin (t g) → ℕ,
              (∀ j : Fin 𝔊.numBig, 𝔭 (Sum.inr j) = 𝔭' (Sum.inr j)) → test 𝔭 = test 𝔭') →
          ∀ σ : ℝ, |σ| ≤ Real.log x ^ Cσ →
          ∀ ψ₁ : ℝ → ℂ, ContDiff ℝ ∞ ψ₁ → Function.support ψ₁ ⊆ Set.Icc a₁ a₂ →
            (∀ (j : ℕ) (u : ℝ), ‖iteratedDeriv j ψ₁ u‖ ≤ Real.log x ^ Dψ j) →
          ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ B → ∀ h : ℤ,
            ∫ τ in (-(x * Real.log x ^ C))..(x * Real.log x ^ C),
              ‖endpointPolynomial (comparisonEndpoint q q₀ 𝔞 x 𝔊 S t test ψ₁ σ Y) Y h k τ‖ ^ 2
              ≤ M * Real.log x ^ (-A)

/-- **(cor:SM) for all fixed exponents**, in the form (eq:energy-input) of the public paper
(`[PUB-tex:0199–0206]`): for all fixed `A_0, B, C`, with independent exponents for the
denominators (`k ≤ L^B`) and the time (`T ≤ x L^C`).

The quantification over the exponents is explicit because the fixed-class Theorem 6.1^{𝔅} uses
the estimate with denominators `H k ≤ L^{C_6 + 1}` on the original time interval
`T_0 = x L^{C_6 + 1}` (`[PUB-tex:0496–0500]`, `[PUB-ja:0086–0092]`), i.e. `EndpointEnergyAt d
(C_6 + 1) (C_6 + 1)`, which is not an instance of (cor:SM) at the same `C_6`. -/
def EndpointEnergy (d : ℕ) : Prop :=
  ∀ B C : ℝ, 0 < B → 0 < C → EndpointEnergyAt d B C

/-- **[P]'s (cor:SM) for every fixed `C_6`** (`[P-06:0544–0550]`): `k ≤ L^{C_6}` and
`T_0 = x L^{C_6 + 1}`. In [P] the exponent `C_6` is taken large enough for the comparison
multiplier (`[P-06:0455–0474]`), and the proof of (cor:SM) (`[P-06:0555–0925]`) works for every
fixed `C_6`.

`EndpointEnergy d → EndpointEnergyPaper d` is a specialization
(`endpointEnergyPaper_of_endpointEnergy`). Conversely `EndpointEnergyAt d B C` follows from the
case `C_6 = max(B, C)` because the left side increases with the time range and `L^B ≤ L^{C_6}`
(`endpointEnergy_of_endpointEnergyPaper` in `Supply/EndpointEnergyForms.lean`). -/
def EndpointEnergyPaper (d : ℕ) : Prop :=
  ∀ C₆ : ℝ, 0 < C₆ → EndpointEnergyAt d C₆ (C₆ + 1)

theorem endpointEnergyPaper_of_endpointEnergy {d : ℕ} (h : EndpointEnergy d) :
    EndpointEnergyPaper d :=
  fun C₆ hC₆ => h C₆ (C₆ + 1) hC₆ (by linarith)

/-! ### Sanity checks -/

/-- For the class weight, the joint factor of the two-sided sum is `1_{w+1 ≡ b (mod H)}`. -/
theorem twoSidedSum_classWeight (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups)
    {d : ℕ} (S : Fin d → Finset ℕ) {H b : ℕ} (hb : b.Coprime H) (Ψ : ℝ → ℂ) (G : ℕ → ℂ) :
    twoSidedSum q q₀ 𝔞 x 𝔊 S (classWeight H b) Ψ G =
      ∑ᶠ w : ℕ, if w + 1 ≡ b [MOD H] then
        Ψ ((w : ℝ) / x) / (w : ℂ) * ((centeredCore q 𝔞 x S w : ℝ) : ℂ) * G (w + 1) *
          𝔊.oneMark q₀ w * 𝔊.oneMark q₀ (w + 1) else 0 := by
  unfold twoSidedSum
  refine finsum_congr fun w => ?_
  have h : (classWeight H b).toFun (w : ZMod H) ((w + 1 : ℕ) : ZMod H) =
      if w + 1 ≡ b [MOD H] then 1 else 0 := classIndicator_succ hb w
  rw [h]
  split_ifs with hw
  · rw [Complex.ofReal_one, mul_one]
  · rw [Complex.ofReal_zero, mul_zero, zero_mul, zero_mul, zero_mul, zero_mul]

/-- For `H = 1` the class weight is trivial: Theorem 6.1^{𝔅} with `𝔅 = 𝓑_{1,b}` is [P]
Theorem 6.1. -/
theorem twoSidedCorrelation_classWeight_one_iff (d b : ℕ) :
    TwoSidedCorrelation d 1 (classWeight 1 b) ↔ TwoSided d := by
  have h : classWeight 1 b = JointResidueWeight.one 1 :=
    JointResidueWeight.ext (funext fun s => funext fun t => classIndicator_one b s t)
  unfold TwoSided
  rw [h]

/-- With no active prime, `n_* = n`. -/
theorem freePart_empty {n : ℕ} (hn : n ≠ 0) : freePart ∅ n = n := by
  unfold freePart
  rw [Finset.filter_true_of_mem (fun p _ => Finset.notMem_empty p)]
  exact Nat.prod_factorization_pow_eq_self hn

namespace ActiveGroups

/-- The number of represented lists with one prime per group is `∏_g ω_g(n)`. -/
theorem representedLists_one_card (𝔊 : ActiveGroups) (n : ℕ) :
    (𝔊.representedLists (fun _ => 1) n).card = ∏ g : 𝔊.Index, primeHits (𝔊.group g) n := by
  unfold representedLists
  rw [Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hall : ∀ 𝔭 ∈ (Fintype.piFinset fun _ : Fin 1 => (𝔊.group g).filter fun p => p ∣ n),
      Function.Injective 𝔭 := fun 𝔭 _ => Function.injective_of_subsingleton 𝔭
  rw [Finset.filter_true_of_mem hall, Fintype.card_piFinset]
  simp [primeHits]

/-- `W_1(n) = ∏_g q_0^{ω_g(n) - 1} ω_g(n) / V_g = q_0^{ω_P(n) - s_P} ∏_g ω_g(n) / V_g`
(`[P-06:0036–0044]` with all `t_g = 1` and test `1`; the first form is the one of
`[P-07:0394–0395, 0541–0542]`). -/
theorem oneMark_eq (𝔊 : ActiveGroups) (q₀ : ℝ) (n : ℕ) :
    𝔊.oneMark q₀ n = ((∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) n : ℝ) : ℂ) := by
  have hlist : ∑ _𝔭 ∈ 𝔊.representedLists (fun _ => 1) n, (1 : ℂ) =
      ((∏ g : 𝔊.Index, (primeHits (𝔊.group g) n : ℝ) : ℝ) : ℂ) := by
    rw [Finset.sum_const, representedLists_one_card, nsmul_eq_mul, mul_one]
    norm_cast
  have hreal : q₀ ^ (𝔊.totalHits n - ∑ _g : 𝔊.Index, 1) *
      (∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ 1)⁻¹) *
        ∏ g : 𝔊.Index, (primeHits (𝔊.group g) n : ℝ) =
      ∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) n := by
    by_cases h : ∀ g : 𝔊.Index, 1 ≤ primeHits (𝔊.group g) n
    · have hsum : ∑ g : 𝔊.Index, (primeHits (𝔊.group g) n - 1) + ∑ _g : 𝔊.Index, 1 =
          𝔊.totalHits n := by
        unfold totalHits
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun g _ => Nat.sub_add_cancel (h g)
      have hexp : 𝔊.totalHits n - ∑ _g : 𝔊.Index, 1 =
          ∑ g : 𝔊.Index, (primeHits (𝔊.group g) n - 1) := by
        omega
      rw [hexp, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun g _ => ?_
      unfold markFactor
      ring
    · obtain ⟨g, hg⟩ := not_forall.mp h
      have hg0 : primeHits (𝔊.group g) n = 0 := by omega
      have h1 : ∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) n = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ g) (markFactor_eq_zero hg0)
      have h2 : ∏ g : 𝔊.Index, (primeHits (𝔊.group g) n : ℝ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ g) (by rw [hg0, Nat.cast_zero])
      rw [h1, h2, mul_zero]
  show ((q₀ ^ (𝔊.totalHits n - ∑ _g : 𝔊.Index, 1) *
      ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ 1)⁻¹ : ℝ) : ℂ) *
        ∑ _𝔭 ∈ 𝔊.representedLists (fun _ => 1) n, (1 : ℂ) = _
  rw [hlist, ← Complex.ofReal_mul, hreal]

end ActiveGroups

end

end SimultaneousPrimitiveRoots.Unconditional.Supply
