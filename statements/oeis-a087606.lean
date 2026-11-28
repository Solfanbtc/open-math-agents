import Mathlib

/-!
# A087606: Smallest k such that k concatenated n times, followed by 9, is prime

Source: https://oeis.org/A087606
Credit: @Solfanbtc

`a(n)` (offset 1) is the smallest `k ≥ 1` such that `k ‖ k ‖ ⋯ ‖ k ‖ 9` (`n` copies of `k`, then the
digit `9`) is prime, or `0` if no such number exists: `1, 2, 0, 1, 1, 0, 1, 11, …` (e.g. `229` is
prime but `119` is not, so `a(2) = 2`; a search reproduces the first 30 data terms). With `L` the
number of digits of `k`, `n` copies of `k` form `k (10^(nL) - 1)/(10^L - 1)`.

Conjecture (OEIS comment): `a(3n) = 0`, and no other term is zero. The first part holds (Sam
Alexander: the digit sum is `≡ 0 (mod 3)`); both parts are stated: for `3 ∣ n` no such prime exists,
and for `3 ∤ n` some `k ≥ 1` gives a prime.
-/

namespace OMA.S_oeis_a087606

/-- `n` copies of `k`, concatenated in decimal, followed by the digit `9`. -/
def rep9 (k n : ℕ) : ℕ :=
  (∑ i ∈ Finset.range n, k * 10 ^ ((Nat.digits 10 k).length * i)) * 10 + 9

/-- `a(3n) = 0` and no other term of A087606 is zero. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → 3 ∣ n → ∀ k : ℕ, 1 ≤ k → ¬ (rep9 k n).Prime) ∧
    (∀ n : ℕ, 1 ≤ n → ¬ 3 ∣ n → ∃ k : ℕ, 1 ≤ k ∧ (rep9 k n).Prime) := by
  sorry

end OMA.S_oeis_a087606
