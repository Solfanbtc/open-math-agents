import Mathlib

/-!
# A078508: Number of primes between sqrt(n^3) and sqrt((n+1)^3)

Source: https://oeis.org/A078508
Credit: @Solfanbtc

`a(n)` (offset 0) is the number of primes between `√(n^3)` and `√((n+1)^3)`; following the entry's
example (`n = 2`: `[n^(3/2)] = 2`, `[(n+1)^(3/2)] = 5`, "there is 1 prime between 2 and 5 = 3"), the
primes `p` counted are those with `⌊√(n^3)⌋ < p < ⌊√((n+1)^3)⌋`: `0, 0, 1, 1, 0, 1, 1, …` (this
reproduces the 68 data terms checked; the real-interval count would give `2` at `n = 2`).
The entry lists the only `n` with `a(n) = 0`: `0, 1, 4, 10, …, 1006, 1051`.

Conjectures (Cino Hilliard, OEIS comments), stated as the parts of `main`:
1. For `n > 1051`, a prime always exists between `n^1.5` and `(n+1)^1.5`: `a(n) > 0`.
2. For `n > 7295`, more than 2 primes always exist between `n^1.5` and `(n+1)^1.5`: `a(n) > 2`.
(Python: both hold for `n < 60000`, with `1051` and `7295` the last exceptions; the thresholds are
the same for the real-interval count.)
-/

namespace OMA.S_oeis_a078508

/-- A078508: primes strictly between `⌊√(n^3)⌋` and `⌊√((n+1)^3)⌋`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo (Nat.sqrt (n ^ 3)) (Nat.sqrt ((n + 1) ^ 3))).filter Nat.Prime).card

/-- Hilliard's two conjectures. -/
theorem main : (∀ n : ℕ, 1051 < n → 0 < a n) ∧ (∀ n : ℕ, 7295 < n → 2 < a n) := by
  sorry

end OMA.S_oeis_a078508
