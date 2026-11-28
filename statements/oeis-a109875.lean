import Mathlib

/-!
# A109875: Chen primes p such that their p + 2 counterpart is a golden semiprime.

Source: https://oeis.org/A109875
Credit: @Solfanbtc

Conjecture (entry comment): the sequence is infinite.

Definitions.
* A golden semiprime (A108540) is `q * r` with `q, r` prime and `|q φ - r| < 1`, φ the golden
  ratio (example in A108540: 589 = 19*31, |19 φ - 31| < 1). The order of the factors needs no
  convention: if `r < q` then `q φ - r > (φ - 1) q > 1`, so only the smaller factor times φ can be
  within 1 of the larger.
* A Chen prime is a prime `p` with `p + 2` prime or semiprime; when `p + 2` is a golden semiprime
  this holds automatically, so a term is just a prime `p` with `p + 2` a golden semiprime.
* python3: the terms below 10^8 are the 26 data terms 13, 587, 1361, ..., 94671671 and then
  95906441.
-/

namespace OMA.S_oeis_a109875

/-- `p` is a term of A109875. -/
def InSeq (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ p + 2 = q * r ∧
    |(q : ℝ) * Real.goldenRatio - r| < 1

theorem main : {p : ℕ | InSeq p}.Infinite := by
  sorry

end OMA.S_oeis_a109875
