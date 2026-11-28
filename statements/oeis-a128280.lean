import Mathlib

/-!
# A128280: a(n) is the least number not occurring earlier such that a(n)+a(n-1) is prime, a(0) = 0.

Source: https://oeis.org/A128280
Credit: @Solfanbtc

Conjecture (M. F. Hasler, Nov 09 2013, comment in A128280; also "the sequence may well be a
rearrangement of natural numbers" in the preceding comment): starting with `a(0) = 0`, the
sequence is a permutation of the nonnegative integers.

Formalization.
* `a(0) = 0`; for `n ≥ 1`, `a(n)` is the least `x ≥ 0` not among `a(0), ..., a(n-1)` with
  `a(n-1) + x` prime. Such an `x` always exists (take `x = p - a(n-1)` for a prime `p` larger
  than `a(n-1)` plus every earlier term); the step uses classical choice (`Nat.find`), with an
  unused junk value `0` otherwise.
* `pre n = [a(0), ..., a(n)]`, built left to right.
* The terms are distinct by construction, so "permutation of the nonnegative integers" amounts
  to: every `m ≥ 0` occurs, which is the statement.

Checked with python3: the definition reproduces all listed %S/%T/%U terms; after 20000 terms
the least missing number is 19993.
-/

namespace OMA.S_oeis_a128280

open Classical in
/-- The next term after the list `l = [a(0), ..., a(n-1)]` (nonempty). -/
noncomputable def nextTerm (l : List ℕ) : ℕ :=
  if h : ∃ x : ℕ, x ∉ l ∧ (l.getLastD 0 + x).Prime then Nat.find h else 0

/-- `pre n = [a(0), ..., a(n)]`. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => pre n ++ [nextTerm (pre n)]

/-- A128280 (with `a(0) = 0`). -/
noncomputable def a (n : ℕ) : ℕ := (pre n).getD n 0

/-- Every nonnegative integer occurs in A128280. -/
theorem main : ∀ m : ℕ, ∃ n : ℕ, a n = m := by
  sorry

end OMA.S_oeis_a128280
