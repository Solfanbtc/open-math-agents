import Mathlib

/-!
# A070991: Numbers n such that the trajectory of n under the `3x+1' map reaches n - 1.

Source: https://oeis.org/A070991
Credit: @Solfanbtc

The `3x+1` map is `T x = x / 2` for even `x` and `T x = 3 x + 1` for odd `x`. The sequence is the
set of positive integers `n` such that some iterate `T^[t] n` with `t ≥ 1` equals `n - 1`:
2, 3, 5, 6, 9, 11, 14, 17, 18, 39, ..., 9233 (checked with python3 against the full data list up
to 10^4). The positivity condition `1 ≤ n` excludes `n = 0`, since in `ℕ` we have `0 - 1 = 0 = T 0`.

Iterating `T` without stopping at 1 (as here) gives the same set as the PARI and Mathematica
programs, which stop at the first 1. After 1 the trajectory only visits 4, 2, 1, so the only
extra candidates are `n ∈ {2, 3, 5}`, and these are terms anyway (the trajectories of 3 and 5
reach 2 and 4 before 1).

Question in the entry: "Is this sequence finite?" There are no more terms below 10^9
(D. Johnson, 2013). `main` states the expected answer, that the sequence is finite.
-/

namespace OMA.S_oeis_a070991

/-- The `3x+1` map. -/
def T (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- A070991 is finite. -/
theorem main :
    Set.Finite {n : ℕ | 1 ≤ n ∧ ∃ t : ℕ, 1 ≤ t ∧ T^[t] n = n - 1} := by
  sorry

end OMA.S_oeis_a070991
