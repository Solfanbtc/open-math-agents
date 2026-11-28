import Mathlib

/-!
# A099154: Largest number k such that the interval [k^2,(k+1)^2] contains not more than n pairs of twin primes.

Source: https://oeis.org/A099154
Credit: @Solfanbtc

Let `t(k)` be the number of twin prime pairs `(p, p + 2)` lying in `[k^2, (k+1)^2]` (A091591; the
endpoints are squares, hence not prime, so open or closed intervals give the same count).
The entry (offset 0) lists 122, 213, 502, 545, 922, 950, 749, 1098, ... and says: "The terms of
this sequence are conjectural, even under the twin prime conjecture." `main` states that the 43
listed terms are correct.

Minimal fix: the name says "not more than n" pairs, but the listed terms are not monotone
(a(5) = 950 > a(6) = 749), which is impossible for "the largest `k` with `t(k) ≤ n`". The data is
exactly "the largest `k` with `t(k) = n`" (python3, all 43 terms, searching `k ≤ 60000`; the
"not more than" reading differs at n = 6, 11, 13, 17, ...). So `main` uses `t(k) = n`, the reading
that makes the listed terms right. Example: a(1) = 213, the interval `[45369, 45796]` holds the
single pair (45587, 45589).

The case `n = 0` (122 is the last `k` with no twin primes in `[k^2, (k+1)^2]`) is the conjecture of
A091591/A091592 (`OeisA91591.conjecture` upstream); `main` is stronger, as it fixes all 43 terms.
-/

namespace OMA.S_oeis_a099154

/-- The number of twin prime pairs `(p, p + 2)` with `k^2 ≤ p` and `p + 2 ≤ (k+1)^2` (A091591). -/
def t (k : ℕ) : ℕ :=
  ((Finset.Icc (k ^ 2) ((k + 1) ^ 2)).filter
    fun p => p.Prime ∧ (p + 2).Prime ∧ p + 2 ≤ (k + 1) ^ 2).card

/-- The 43 listed terms of A099154, `a(0), ..., a(42)`. -/
def data : List ℕ :=
  [122, 213, 502, 545, 922, 950, 749, 1098, 1330, 1450, 1634, 1623, 2135, 2110, 2177,
   2244, 2760, 2413, 2556, 3280, 3454, 3211, 3740, 3540, 4104, 4096, 4391, 4457,
   4592, 5309, 4758, 5720, 5747, 5295, 5902, 5456, 5920, 6395, 5810, 7007, 7109, 7450, 7540]

/-- Conjecture: for each `n ≤ 42`, the listed term is the largest `k` whose interval
`[k^2, (k+1)^2]` contains exactly `n` pairs of twin primes. -/
theorem main : ∀ n : ℕ, (h : n < data.length) → IsGreatest {k : ℕ | t k = n} data[n] := by
  sorry

end OMA.S_oeis_a099154
