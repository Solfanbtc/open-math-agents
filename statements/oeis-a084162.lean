import Mathlib

/-!
# A084162: a(n) is the length of the gap in sequence A084161.

Source: https://oeis.org/A084162
Credit: @Solfanbtc

A002313 is the primes that are sums of two squares: `2` and the primes `p ≡ 1 (mod 4)`. Let
`q(0) = 2, q(1) = 5, q(2) = 13, …` enumerate it and `gap(i) = q(i+1) - q(i)`. An index `i` is a
record when `gap(i) > gap(j)` for all `j < i` (first-occurrence maximal gaps). A084161(n) is
`q` at the `n`-th record index (offset `0`), A268963(n) the next term `q(·+1)` (the end of the
gap), and `a(n)` the gap length. This reproduces the first 27 terms of the data, all the records
below `6·10^7` (Python).

Conjectures (Alexei Kourbatov):
1. (Feb 16 2016) `a(n) < φ(4) log²(A268963(n))` for all `n ≥ 0` (`φ(4) = 2`, natural log).
2. (Aug 12 2017) `a(n) < φ(4) n²` for all `n > 2` (offset `0`).
Both hold for the 27 records below `6·10^7` (Python).
-/

namespace OMA.S_oeis_a084162

/-- A002313: `2` and the primes `≡ 1 (mod 4)`. -/
def Q (p : ℕ) : Prop := p = 2 ∨ (p.Prime ∧ p % 4 = 1)

/-- `q i`: the `i`-th term of A002313 (0-indexed, `q 0 = 2`). -/
noncomputable def q (i : ℕ) : ℕ := Nat.nth Q i

/-- The gap after `q i`. -/
noncomputable def gap (i : ℕ) : ℕ := q (i + 1) - q i

/-- `i` is the index of a record (first-occurrence maximal) gap. -/
def IsRecord (i : ℕ) : Prop := ∀ j : ℕ, j < i → gap j < gap i

/-- The index of the `n`-th record gap (offset 0). -/
noncomputable def r (n : ℕ) : ℕ := Nat.nth IsRecord n

/-- A084162. -/
noncomputable def a (n : ℕ) : ℕ := gap (r n)

/-- A268963: the prime at the end of the `n`-th record gap. -/
noncomputable def endPrime (n : ℕ) : ℕ := q (r n + 1)

theorem main :
    (∀ n : ℕ, (a n : ℝ) < (Nat.totient 4 : ℝ) * Real.log (endPrime n) ^ 2) ∧
    (∀ n : ℕ, 2 < n → a n < Nat.totient 4 * n ^ 2) := by
  sorry

end OMA.S_oeis_a084162
