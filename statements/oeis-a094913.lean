import Mathlib

/-!
# A094913: Maximal number of distinct nonempty substrings of a binary string of length n

Source: https://oeis.org/A094913
Credit: @Solfanbtc

`a(n)` is the maximal number of distinct nonempty substrings (contiguous factors) of any binary
string of length `n` (offset 0, `a(0) = 0`). The entry (J. W. Layman) states:

Conjecture: the maximum number `a(n)` of distinct substrings of a binary string of length `n` is
given by `a(n) = Sum_{k=1..n} t(k)`, where `t(k)` is the smaller of `2^k` and `n-k+1`.

`main` states this for every `n` (for `n = 0` both sides are `0`), as: some binary string of
length `n` has exactly that many distinct nonempty substrings, and none has more.
Checked by brute force for `n ≤ 15` against the data `0, 1, 3, 5, 8, 12, 16, 21, 27, ...`.

Status: the entry notes that some of its conjectures are proven in the cited papers:
J. Shallit, "On the maximum number of distinct factors in a binary string", Graphs Combin. 9
(1993) 197-200; A. Flaxman, A. W. Harrow, G. B. Sorkin, "Strings with Maximally Many Distinct
Subsequences and Substrings", Electron. J. Combin. 11 (2004) R8.
-/

namespace OMA.S_oeis_a094913

/-- The distinct nonempty substrings (contiguous factors) of `w`: every factor is a prefix of a
suffix of `w`. -/
def substrings (w : List Bool) : List (List Bool) :=
  ((w.tails.flatMap List.inits).filter (fun u => !u.isEmpty)).dedup

/-- The number of distinct nonempty substrings of `w`. -/
def numSubstrings (w : List Bool) : ℕ := (substrings w).length

/-- The conjectured maximum `Sum_{k=1..n} min(2^k, n-k+1)`. -/
def bound (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, min (2 ^ k) (n - k + 1)

/-- Conjecture (Layman): the maximal number of distinct nonempty substrings of a binary string of
length `n` is `Sum_{k=1..n} min(2^k, n-k+1)`. -/
theorem main : ∀ n : ℕ,
    (∃ w : List Bool, w.length = n ∧ numSubstrings w = bound n) ∧
    ∀ w : List Bool, w.length = n → numSubstrings w ≤ bound n := by
  sorry

end OMA.S_oeis_a094913
