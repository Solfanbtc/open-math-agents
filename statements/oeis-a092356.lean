import Mathlib

/-!
# A092356: UO-sigma multiperfect numbers

Source: https://oeis.org/A092356 (and https://oeis.org/A069184 for the function)
The UO-sigma function is `A069184(n)`, the sum of the divisors `d` of `n` such that `d` or `n / d`
is odd (multiplicative, with value `2^e + 1` at `2^e` and `σ(p^e)` at an odd prime power).
A092356 lists the `n` with `n ∣ UOσ(n)`: 1, 6, 60, 1080, 6552, 36720, ...
Writing `UOσ(n) = k * n`, the entry says: the initial values of `k` (after `a(1) = 1`, where
`k = 1`) are all 2, "however, I conjecture that every positive integer >= 2 must appear".

We state: for every integer `k ≥ 2` there is a positive integer `n` with `UOσ(n) = k * n`.
(`n ≥ 1` is the range of the sequence, offset 1; for `n = 0` the sum is empty, so `n = 0`
would satisfy every `k` trivially and must be excluded.)

Checked with python3: `uoSigma` agrees with the first 69 terms of A069184, and its multiperfect
numbers up to 10^5 are 1, 6, 60, 1080, 6552, 36720, 47520, 87360 as in the entry.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a092356

/-- A069184: the sum of the divisors `d` of `n` such that `d` or `n / d` is odd. -/
def uoSigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors.filter (fun d => Odd d ∨ Odd (n / d)), d

theorem main : ∀ k : ℕ, 2 ≤ k → ∃ n : ℕ, 0 < n ∧ uoSigma n = k * n := by
  sorry

end OMA.S_oeis_a092356
