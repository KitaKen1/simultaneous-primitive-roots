module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.Cond
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.TailLift
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lemma 3.10: the simultaneous translation of the small residues and of the pending residues

Source: `verification/stage7-sources/S-02.tex`, lines 911–917, 959–970 (`[S-02:0911–0970]`).

"A clean edge leaves all memory prime lists and sizes unchanged, translates their residues, drops
every unshared big source slot, and fills every unshared big target slot freshly. … The operator
between these maps uses the big-list transitions and translates all unrestricted small and memory
residues by `σ_i k d' D_ℬ`."

* `cleanShiftMem`, `cleanSh` — the translation of the residues of a memory, and of the small
  residues together with all memories, by an integer. It is an action of `ℤ` (`cleanSh_zero`,
  `cleanSh_add`) of period `cleanPeriod` (`cleanSh_period`), and it preserves the measure
  `cleanYW` (`cleanYW_cleanSh`): "counting measure on pending residues and Haar measure on the
  small torus".
* `clean_memOfList_map` — the memory of the translated particles of a memory, listed through
  `memAt`, is the translated memory (with the same order of the particles).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Lists -/

theorem clean_filterMap_some {α β : Type*} (f : α → β) (l : List α) :
    l.filterMap (fun a => some (f a)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    exact (List.filterMap_cons_some (f := fun a => some (f a)) (a := a) (l := l) (b := f a)
      rfl).trans (congrArg (fun t => f a :: t) ih)

theorem clean_append_filter_nil {α β : Type*} (l₁ : List β) (l : List α) (p : α → Bool)
    (ψ : α → β) (hp : ∀ a, p a = false) : l₁ ++ (l.filter p).map ψ = l₁ := by
  have h : l.filter p = [] := List.filter_eq_nil_iff.mpr fun a _ => by
    rw [hp a]
    exact Bool.false_ne_true
  rw [h, List.map_nil, List.append_nil]

section Shift

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ}

/-! ### Translation of the particles -/

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem clean_shiftParticle_mk (a : ℤ) {g : B} (p : {p : ℕ // p ∈ 𝒢.big g}) (r : Res p.1) :
    shiftParticle a (⟨p, r⟩ : Particle 𝒢 g) = ⟨p, (a : Res p.1) + r⟩ := rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem clean_shiftParticle_fst (a : ℤ) {g : B} (pr : Particle 𝒢 g) :
    (shiftParticle a pr).1 = pr.1 := by
  obtain ⟨p, r⟩ := pr
  rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem clean_shiftParticle_zero {g : B} (pr : Particle 𝒢 g) : shiftParticle 0 pr = pr := by
  obtain ⟨p, r⟩ := pr
  show (⟨p, ((0 : ℤ) : Res p.1) + r⟩ : Particle 𝒢 g) = ⟨p, r⟩
  rw [Int.cast_zero, zero_add]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem clean_shiftParticle_add (a b : ℤ) {g : B} (pr : Particle 𝒢 g) :
    shiftParticle (a + b) pr = shiftParticle a (shiftParticle b pr) := by
  obtain ⟨p, r⟩ := pr
  show (⟨p, ((a + b : ℤ) : Res p.1) + r⟩ : Particle 𝒢 g) =
    ⟨p, ((a : ℤ) : Res p.1) + (((b : ℤ) : Res p.1) + r)⟩
  rw [Int.cast_add, add_assoc]

/-- **The translation of the residues of a memory**: the prime list and the size are unchanged
[S-02:0911–0912]. -/
def cleanShiftMem (a : ℤ) {g : B} (z : Mem 𝒢 Bc g) : Mem 𝒢 Bc g :=
  ⟨z.1, fun h => shiftParticle a (z.2 h)⟩

/-- **The translation of the small residues and of all pending residues** by the integer `a`. -/
def cleanSh (a : ℤ) (yy : CleanY 𝒢 Bc) : CleanY 𝒢 Bc :=
  ((resModel (smallPrimes 𝒢)).shift a yy.1, fun g => cleanShiftMem a (yy.2 g))

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem cleanShiftMem_zero {g : B} (z : Mem 𝒢 Bc g) : cleanShiftMem 0 z = z := by
  obtain ⟨k, f⟩ := z
  exact congrArg (fun f' => (⟨k, f'⟩ : Mem 𝒢 Bc g))
    (funext fun h => clean_shiftParticle_zero (f h))

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem cleanShiftMem_add (a b : ℤ) {g : B} (z : Mem 𝒢 Bc g) :
    cleanShiftMem (a + b) z = cleanShiftMem a (cleanShiftMem b z) := by
  obtain ⟨k, f⟩ := z
  exact congrArg (fun f' => (⟨k, f'⟩ : Mem 𝒢 Bc g))
    (funext fun h => clean_shiftParticle_add a b (f h))

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem cleanSh_zero (yy : CleanY 𝒢 Bc) : cleanSh 0 yy = yy := by
  obtain ⟨y, mem⟩ := yy
  refine Prod.ext (funext fun p => ?_) (funext fun g => cleanShiftMem_zero (mem g))
  show y p + ((0 : ℤ) : Res p.1) = y p
  rw [Int.cast_zero, add_zero]

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem cleanSh_add (a b : ℤ) (yy : CleanY 𝒢 Bc) :
    cleanSh (a + b) yy = cleanSh a (cleanSh b yy) := by
  obtain ⟨y, mem⟩ := yy
  refine Prod.ext (funext fun p => ?_) (funext fun g => cleanShiftMem_add a b (mem g))
  show y p + ((a + b : ℤ) : Res p.1) = y p + ((b : ℤ) : Res p.1) + ((a : ℤ) : Res p.1)
  rw [Int.cast_add]
  ring

/-- A common period of all residues: the product of the moduli of all group primes. -/
def cleanPeriod (𝒢 : GroupFamily S B) : ℕ := ∏ p ∈ 𝒢.allPrimes, (p - 1 + 1)

omit [DecidableEq S] [DecidableEq B] in
theorem cleanPeriod_pos (𝒢 : GroupFamily S B) : 0 < cleanPeriod 𝒢 :=
  Finset.prod_pos fun _ _ => Nat.succ_pos _

omit [DecidableEq S] [DecidableEq B] in
theorem clean_period_res (p : ℕ) (hp : p ∈ 𝒢.allPrimes) :
    (((cleanPeriod 𝒢 : ℕ) : ℤ) : Res p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem (fun p => p - 1 + 1) hp)

omit [DecidableEq S] [DecidableEq B] in
theorem cleanSh_period (yy : CleanY 𝒢 Bc) : cleanSh ((cleanPeriod 𝒢 : ℕ) : ℤ) yy = yy := by
  obtain ⟨y, mem⟩ := yy
  refine Prod.ext (funext fun p => ?_) (funext fun g => ?_)
  · have hp : p.1 ∈ 𝒢.allPrimes := by
      rw [allPrimes_eq]
      exact Finset.mem_union_left _ p.2
    show y p + (((cleanPeriod 𝒢 : ℕ) : ℤ) : Res p.1) = y p
    rw [clean_period_res p.1 hp, add_zero]
  · show cleanShiftMem ((cleanPeriod 𝒢 : ℕ) : ℤ) (mem g) = mem g
    have hpart : ∀ pr : Particle 𝒢 g, shiftParticle ((cleanPeriod 𝒢 : ℕ) : ℤ) pr = pr := by
      intro pr
      obtain ⟨p, r⟩ := pr
      have hp : p.1 ∈ 𝒢.allPrimes := by
        rw [allPrimes_eq]
        exact Finset.mem_union_right _ (mem_bigPrimes.mpr ⟨g, p.2⟩)
      show (⟨p, (((cleanPeriod 𝒢 : ℕ) : ℤ) : Res p.1) + r⟩ : Particle 𝒢 g) = ⟨p, r⟩
      rw [clean_period_res p.1 hp, zero_add]
    have hmem : ∀ z : Mem 𝒢 Bc g, cleanShiftMem ((cleanPeriod 𝒢 : ℕ) : ℤ) z = z := by
      intro z
      obtain ⟨k, f⟩ := z
      exact congrArg (fun f' => (⟨k, f'⟩ : Mem 𝒢 Bc g)) (funext fun h => hpart (f h))
    exact hmem (mem g)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The measure of a memory does not depend on its residues. -/
theorem clean_pointMass_shift {g : B} (w : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (a : ℤ)
    (z : Mem 𝒢 Bc g) :
    Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => w pr.1) (cleanShiftMem a z) =
      Graph.finiteMemoryPointMass (fun pr : Particle 𝒢 g => w pr.1) z := by
  obtain ⟨k, f⟩ := z
  show Graph.factorialMemoryPointMass (fun pr : Particle 𝒢 g => w pr.1)
      (fun h => shiftParticle a (f h)) =
    Graph.factorialMemoryPointMass (fun pr : Particle 𝒢 g => w pr.1) f
  unfold Graph.factorialMemoryPointMass
  rw [Finset.prod_congr rfl fun i _ => congrArg w (clean_shiftParticle_fst a (f i))]

omit [DecidableEq S] [DecidableEq B] in
/-- **The measure of the small residues and of the memories is invariant under the translations**
("counting measure on pending residues and Haar measure on the small torus", [S-02:0966–0968]). -/
theorem cleanYW_cleanSh (J : ℕ) (q : ℝ) (n : ℕ) (a : ℤ) (yy : CleanY 𝒢 Bc) :
    cleanYW 𝒢 J q n (cleanSh a yy) = cleanYW 𝒢 J q n yy := by
  have hm : memMass 𝒢 q n (cleanSh a yy).2 = memMass 𝒢 q n yy.2 := by
    unfold memMass
    exact Finset.prod_congr rfl fun g _ =>
      clean_pointMass_shift (fun p => tiltLaw (𝒢.big g) q n p) a (yy.2 g)
  unfold cleanYW
  rw [hm]

/-! ### Memories read through `memAt` -/

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The images of the particles of a memory, read through `memAt`, in their order. -/
theorem clean_filterMap_memAt {g : B} (f : Particle 𝒢 g → Particle 𝒢 g) (z : Mem 𝒢 Bc g) :
    (List.finRange Bc).filterMap (fun j => (memAt z j).map f) =
      List.ofFn (fun h : Fin z.1.val => f (z.2 h)) := by
  have hz : z.1.val ≤ Bc := Nat.le_of_lt_succ z.1.isLt
  have h1 := tail_filterMap_castLE Bc hz (fun j => (memAt z j).map f) (fun j hj => by
    have hn : ¬j.val < z.1.val := by omega
    have e : memAt z j = none := dif_neg hn
    exact congrArg (Option.map f) e)
  rw [h1, List.ofFn_eq_map, ← clean_filterMap_some]
  refine congrArg (fun φ => (List.finRange z.1.val).filterMap φ) (funext fun j => ?_)
  have e : memAt z (Fin.castLE hz j) = some (z.2 j) := dif_pos j.isLt
  exact congrArg (Option.map f) e

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- **The memory of the translated particles of a memory is the translated memory.** -/
theorem clean_memOfList_map {g : B} (a : ℤ) (z : Mem 𝒢 Bc g) :
    memOfList (Bc := Bc)
        ((List.finRange Bc).filterMap (fun j => (memAt z j).map (shiftParticle a))) =
      cleanShiftMem a z := by
  have hz : z.1.val ≤ Bc := Nat.le_of_lt_succ z.1.isLt
  have hlen : (List.ofFn fun h : Fin z.1.val => shiftParticle a (z.2 h)).length ≤ Bc := by
    rw [List.length_ofFn]
    exact hz
  rw [clean_filterMap_memAt]
  refine mem_ext_ofFn _ _ ?_
  rw [ofFn_memOfList hlen]
  rfl

end Shift

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
