import Mathlib

/-!
# A033919: the dual Sierpiński problem: 78557 is the least odd k with k + 2^m always composite

Source: https://oeis.org/A033919
Credit: @Solfanbtc

A033919: odd `k` for which `k + 2^m` is composite for all `m < k`.

The entry (T. D. Noe, 2007; P. Moore, 2009), on the dual Sierpiński problem: "It is conjectured
that, for each of these k<78557, there is an m such that k+2^m is prime. Then a covering argument
would show that 78557 is the least odd number such that 78557+2^m is composite for all m."
"40291 is the only value of k < 78557 for which there is currently no m known making k + 2^m a
prime or probable prime."

`main` states the resulting conjecture: `78557` is the least odd `k` such that `k + 2^m` is
composite for every `m ≥ 0`. (Since `k + 2^m ≥ 2`, composite means not prime.) The half
"`78557 + 2^m` is always composite" is the covering argument: every `78557 + 2^m` is divisible by
one of 3, 5, 7, 13, 19, 37, 73 (checked with python3 for `m < 3600`; the pattern has period 36).
The open half is that every odd `k < 78557` has some `m` with `k + 2^m` prime.
-/

namespace OMA.S_oeis_a033919

/-- The dual Sierpiński conjecture: `78557` is the least odd `k` with `k + 2^m` composite for
all `m`. -/
theorem main : IsLeast {k : ℕ | Odd k ∧ ∀ m : ℕ, ¬ (k + 2 ^ m).Prime} 78557 := by
  sorry

end OMA.S_oeis_a033919
