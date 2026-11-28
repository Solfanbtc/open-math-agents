import Mathlib

/-!
# A060064: First subsequent, disjoint occurrence of n consecutive nonprimes.

Source: https://oeis.org/A060064
Credit: @Solfanbtc

Conjecture (Robert Israel, OEIS A060064, comment, May 04 2025): a(n) - 1 is always prime.

Conventions:
* a(1) is the first nonprime counted from 2 (1 is not considered, as the example's a(1) = 4
  shows). For n ≥ 2, a(n) is the least s after the block of a(n-1), i.e.
  s ≥ a(n-1) + (n-1), such that s, s+1, ..., s+n-1 are all nonprime ("first subsequent,
  disjoint occurrence"). Example: 4; 8,9; 14,15,16; 24..27; ...
* In Lean `a 0 = 2` is an auxiliary start value (a block of length 0 ending before 2), so the
  recursion `a (n+1) = min {s ≥ a n + n : s, ..., s+n nonprime}` gives a(1) = 4, a(2) = 8, ...
  The minimum is written with `sInf`; the set is nonempty (arbitrarily long runs of composites).
* Checked in Python (primes below 10^8): the recursion reproduces %S and gives 178 terms, and
  a(n) - 1 is prime for all of them.
-/

namespace OMA.S_oeis_a060064

/-- A060064 (with the auxiliary value `a 0 = 2`). -/
noncomputable def a : ℕ → ℕ
  | 0 => 2
  | n + 1 => sInf {s : ℕ | a n + n ≤ s ∧ ∀ i < n + 1, ¬ (s + i).Prime}

/-- Israel's conjecture: `a(n) - 1` is prime for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n - 1).Prime := by
  sorry

end OMA.S_oeis_a060064
