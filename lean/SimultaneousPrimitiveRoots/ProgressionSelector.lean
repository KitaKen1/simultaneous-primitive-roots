module

public import SimultaneousPrimitiveRoots.FixedProgression
public import SimultaneousPrimitiveRoots.SelectorProduct

@[expose] public section

namespace SimultaneousPrimitiveRoots

theorem allowedExtensions_prime_properties {M b u p : ℕ} {S : Finset ℕ}
    (hb : b < M) (hS : ∀ q ∈ S, q.Prime)
    (hu : u ∈ allowedExtensions M b S) (hp : 0 < p)
    (hpu : p ≡ u [MOD M * (∏ q ∈ S, q)]) :
    p ≡ b [MOD M] ∧ ∀ q ∈ S, ¬ q ∣ p - 1 := by
  obtain ⟨_, huc, hub, havoid⟩ := Finset.mem_filter.mp hu
  constructor
  · change p % M = b % M
    calc p % M = u % M := hpu.of_dvd (dvd_mul_right M _)
         _ = b := hub
         _ = b % M := (Nat.mod_eq_of_lt hb).symm
  · intro q hq
    have hpq : p % q = u % q := hpu.of_dvd
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun q : ℕ => q) hq) M)
    exact not_dvd_sub_one_of_local_residue hp (hS q hq).one_lt (havoid q hq) hpq

/-- M is fixed before T. Retaining every allowed extension gives the density
needed for the later parameter choice, without enumerating a huge modulus. -/
theorem exists_progression_selector {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hSQ : SquareCondition A) :
    ∃ M : ℕ, 0 < M ∧ ∀ T : ℕ, 1 ≤ T → ∃ H : ℕ, ∃ C : Finset ℕ,
      0 < H ∧ C.Nonempty ∧
        1 / (2 * (Nat.totient M : ℝ) * (T : ℝ)) ≤ (C.card : ℝ) / Nat.totient H ∧
          ∀ u ∈ C, u < H ∧ u.Coprime H ∧
            ∀ p : ℕ, p.Prime → 3 < p → p ≡ u [MOD H] →
              (∀ a ∈ A, ¬ IsSquare (a : ZMod p)) ∧
                ∀ q : ℕ, q.Prime → 3 ≤ q → q ≤ 2 * T ^ 2 + 1 → ¬ q ∣ p - 1 := by
  classical
  obtain ⟨M, b, hM, hb, hbc, hbase⟩ := exists_nonsquare_progression_strong hpos hSQ 0
  refine ⟨M, hM, ?_⟩
  intro T hT
  let S := (Finset.range (2 * T ^ 2 + 2)).filter fun q =>
    q.Prime ∧ 3 ≤ q ∧ M.Coprime q
  have hS : ∀ q ∈ S, q.Prime ∧ 3 ≤ q ∧ q ≤ 2 * T ^ 2 + 1 := by
    intro q hq
    obtain ⟨hqr, hprime, hq3, _⟩ := Finset.mem_filter.mp hq
    exact ⟨hprime, hq3, by have := Finset.mem_range.mp hqr; omega⟩
  have hcop : ∀ q ∈ S, M.Coprime q := fun q hq => (Finset.mem_filter.mp hq).2.2.2
  let H := M * (∏ q ∈ S, q)
  let C := allowedExtensions M b S
  have hH : 0 < H := Nat.mul_pos hM (Finset.prod_pos fun q hq => (hS q hq).1.pos)
  have hden := allowedExtensions_density_lower hM hb hbc hT hS hcop
  have hphi : 0 < (Nat.totient M : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hC : C.Nonempty := by
    by_contra hn
    have hz : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hzero : (allowedExtensions M b S).card = 0 := by change C.card = 0; rw [hz]; rfl
    rw [hzero, Nat.cast_zero, zero_div] at hden
    have hpositive : 0 < 1 / (2 * (Nat.totient M : ℝ) * (T : ℝ)) := by positivity
    linarith
  refine ⟨H, C, hH, hC, hden, ?_⟩
  intro u hu
  have humem := Finset.mem_filter.mp hu
  refine ⟨Finset.mem_range.mp humem.1, humem.2.1, ?_⟩
  intro p hprime hp hpu
  obtain ⟨hpbase, havoid⟩ := allowedExtensions_prime_properties hb
    (fun q hq => (hS q hq).1) hu (by omega) hpu
  have hbasic := hbase p hprime hp hpbase
  refine ⟨hbasic.1, ?_⟩
  intro q hq hq3 hqY
  by_cases hqM : q ∣ M
  · exact hbasic.2 q hq hq3 (Or.inr hqM)
  · apply havoid q
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hq3,
      (hq.coprime_iff_not_dvd.mpr hqM).symm⟩

end SimultaneousPrimitiveRoots
