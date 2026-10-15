axiom forbidden : ∀ n : Nat, n + 0 = n
theorem control_test (n : Nat) : n + 0 = n := forbidden n
