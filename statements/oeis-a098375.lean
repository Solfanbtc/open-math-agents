import Mathlib

/-!
# A098375: (1/p)*abs(p*(p^(p-1)-1)*B(p-1)-1) when p runs through the primes and B(k) denotes the k-th Bernoulli's number.

Source: https://oeis.org/A098375
Credit: @Solfanbtc

`B(k)` is the `k`-th Bernoulli number with `B(1) = -1/2` (Mathlib's `bernoulli`; this is the
convention the data uses: the first term, for `p = 2`, is `|2 * 1 * (-1/2) - 1| / 2 = 1`).

Conjecture (Benoit Cloitre): *`p` is an odd prime iff `p` divides `p (p^(p-1) - 1) B(p-1) - 1`.*
(The entry says it seems equivalent to Agoh's conjecture, which uses rational moduli; no
proof of that equivalence is given, so this is stated on its own.) Here `n` divides the
rational number `E(n) = n (n^(n-1) - 1) B(n-1) - 1` when `E(n) = n k` for an integer `k`
(`E(n)` is an integer for every `n ≤ 400`, by von Staudt–Clausen and Fermat).

The equivalence fails trivially at `n = 1` (1 divides everything, but 1 is not prime) and at
`n = 2` (`E(2) = -2`, divisible by 2, but 2 is not odd). It holds for `3 ≤ n ≤ 400`
(computer check), so it is stated for `n ≥ 3`, the minimal fix. For even `n ≥ 4`,
`B(n-1) = 0` and `E(n) = -1`.
-/

namespace OMA.S_oeis_a098375

/-- `E(n) = n (n^(n-1) - 1) B(n-1) - 1`. -/
def E (n : ℕ) : ℚ := (n : ℚ) * ((n : ℚ) ^ (n - 1) - 1) * bernoulli (n - 1) - 1

/-- Cloitre's conjecture, for `n ≥ 3`: `n` is an odd prime iff `n` divides `E(n)`. -/
theorem main : ∀ n : ℕ, 3 ≤ n → ((n.Prime ∧ Odd n) ↔ ∃ k : ℤ, E n = n * k) := by
  sorry

end OMA.S_oeis_a098375
