import OMAStatements.S_oeis_a350142

/-!
With m = 2^k + 1 we have m - 1 = 2^k and τ(2^k) = k + 1, so τ(m - 1) - 1 = k and both sides of the
equivalence are the same statement τ(m - 2) = k.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a350142.main := by
  intro k
  show OMA.S_oeis_a350142.tau (2 ^ k + 1 - 2) = OMA.S_oeis_a350142.tau (2 ^ k + 1 - 1) - 1 ↔
    OMA.S_oeis_a350142.tau (2 ^ k + 1 - 2) = k
  have h1 : 2 ^ k + 1 - 1 = 2 ^ k := Nat.add_sub_cancel _ _
  have h2 : OMA.S_oeis_a350142.tau (2 ^ k) = k + 1 := by
    unfold OMA.S_oeis_a350142.tau
    rw [Nat.divisors_prime_pow Nat.prime_two k, Finset.card_map, Finset.card_range]
  simp only [h1, h2, Nat.add_sub_cancel, iff_self]
