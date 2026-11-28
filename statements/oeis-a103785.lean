import Mathlib

/-!
# A103785: Primes of the form A019565(2^n-1-k)+A019565(k) with minimum k.

Source: https://oeis.org/A103785
Credit: @Solfanbtc

Conjecture (entry comment): the sequence is defined for any n ≥ 1, i.e. for every n ≥ 1 some
k makes A019565(2^n-1-k) + A019565(k) prime.

Definitions.
* A019565(k) = product of the primes p_(i+1) over the bits i set in the binary expansion of k
  (so A019565(0) = 1, A019565(2^n - 1) = p_1 ⋯ p_n = primorial).
* The search in the Mathematica program runs over k = 0, 1, 2, ... with the sum
  primorial(n)/A019565(k) + A019565(k), which equals A019565(2^n-1-k) + A019565(k) for
  k ≤ 2^n - 1 (complementary bits); for larger k the quotient is not an integer and the program
  stops. So "a(n) is defined" means: some k with 0 ≤ k ≤ 2^n - 1 gives a prime.
* `#eval` (with the primes taken from a finite list) reproduces the first 12 data terms
  3, 7, 31, 211, 2311, 15017, ... with the least such k.
-/

namespace OMA.S_oeis_a103785

/-- A019565(k): product of `p_(i+1)` over the set bits `i` of `k`. -/
noncomputable def A019565 (k : ℕ) : ℕ :=
  ∏ i ∈ (Finset.range k.size).filter (fun i => k.testBit i), Nat.nth Nat.Prime i

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, k ≤ 2 ^ n - 1 ∧ (A019565 (2 ^ n - 1 - k) + A019565 k).Prime := by
  sorry

end OMA.S_oeis_a103785
