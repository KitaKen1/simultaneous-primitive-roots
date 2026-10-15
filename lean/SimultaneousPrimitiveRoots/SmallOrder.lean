module

public import SimultaneousPrimitiveRoots.OrderObstruction

@[expose] public section

namespace SimultaneousPrimitiveRoots

/-- The integer whose prime divisors cover all orders at most N. -/
def smallOrderProduct (a N : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 1 N, (a ^ j - 1)

theorem smallOrderProduct_pos {a : ℕ} (ha : 2 ≤ a) (N : ℕ) :
    0 < smallOrderProduct a N := by
  unfold smallOrderProduct
  apply Finset.prod_pos
  intro j hj
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  have hp : 1 < a ^ j := one_lt_pow₀ (by omega) (by omega)
  omega

theorem dvd_smallOrderProduct_of_pow_eq_one {a p j N : ℕ}
    (ha : 2 ≤ a) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hpow : (a : ZMod p) ^ j = 1) : p ∣ smallOrderProduct a N := by
  have hpowge : 1 ≤ a ^ j := Nat.one_le_pow j a (by omega)
  have hz : ((a ^ j - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hpowge, Nat.cast_pow, Nat.cast_one, hpow, sub_self]
  have hdvd : p ∣ a ^ j - 1 := (ZMod.natCast_eq_zero_iff _ _).mp hz
  exact hdvd.trans (Finset.dvd_prod_of_mem (fun k => a ^ k - 1) (Finset.mem_Icc.mpr ⟨hj, hjN⟩))

theorem marked_prime_obstruction_dvd_product {a p Q r N : ℕ}
    (ha : 2 ≤ a) (hQ : Q.Prime) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hfactor : p - 1 = Q * r)
    (hpow : (a : ZMod p) ^ ((p - 1) / Q) = 1) :
    p ∣ smallOrderProduct a N := by
  apply dvd_smallOrderProduct_of_pow_eq_one ha hr hrN
  simpa only [hfactor, Nat.mul_div_cancel_left r hQ.pos] using hpow

end SimultaneousPrimitiveRoots
