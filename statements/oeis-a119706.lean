import Mathlib

/-!
# A119706: Total length of longest runs of 1's in all bitstrings of length n.

Source: https://oeis.org/A119706 (and https://oeis.org/A102712)
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jun 05 2025): `a(n) = A102712(n+1) - 2^n`, where A102712(m) is the
sum of the largest parts of all compositions of `m`.

Conventions. Bitstrings of length `n` are the numbers `x < 2^n` read through their `n` low
binary digits (`Nat.testBit`); the longest run of 1's of `x` is the largest `k ≤ n` such that
some `k` consecutive positions `i, ..., i+k-1` (`i + k ≤ n`) all carry a 1 (it is `0` for
the all-zero string). Compositions of `m` are Mathlib's `Composition m`, and the largest part
is the maximum of `blocks` (`0` for the empty composition of `0`, unused here). Offset of
A119706 is `1`, so the claim is stated for `n ≥ 1`, as `a(n) + 2^n = A102712(n+1)`
(natural subtraction avoided). Checked with `#eval`: `a` and `b` reproduce the data for `n ≤ 11`,
and the identity holds for `1 ≤ n ≤ 9`.
-/

namespace OMA.S_oeis_a119706

/-- Longest run of 1's among the `n` low binary digits of `x`. -/
def longestRun (n x : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun k =>
    ∃ i ∈ Finset.range (n + 1), i + k ≤ n ∧ ∀ j ∈ Finset.range k, x.testBit (i + j)).sup id

/-- A119706(n): total length of the longest runs of 1's over all bitstrings of length `n`. -/
def a (n : ℕ) : ℕ := ∑ x ∈ Finset.range (2 ^ n), longestRun n x

/-- A102712(m): sum of the largest parts of all compositions of `m`. -/
def b (m : ℕ) : ℕ := ∑ c : Composition m, c.blocks.foldr max 0

/-- Mathar's conjecture: `a(n) = A102712(n+1) - 2^n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n + 2 ^ n = b (n + 1) := by
  sorry

end OMA.S_oeis_a119706
