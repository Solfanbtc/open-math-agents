import Mathlib

/-!
# A060164: orbits of the conjectured map whose periodic points are counted by A000364

Source: https://oeis.org/A060164 (and https://oeis.org/A000364)
Credit: @Solfanbtc

A000364 are the Euler (secant) numbers `E(0), E(1), E(2), ... = 1, 1, 5, 61, 1385, 50521, ...`
(e.g.f. `sec x`), given here by the recurrence `E(0) = 1`,
`E(n) = ∑_{k<n} (-1)^(n-k-1) binom(2n, 2k) E(k)`.

The entry: "The sequence A000364 seems to record the number of points of period n under a map",
and its example speaks of "the conjectured map whose periodic points are counted by A000364"
(1 fixed point, 61 points of period 3, hence 20 orbits of length 3). A060164(n) is then the number
of orbits of length `n`, `(1/n) ∑_{d | n} μ(d) E(n/d)`: 1, 2, 20, 345, 10104, ...

Conjecture (implicit in the entry): there is a map `T : X → X` whose number of points of period
`n` (points with `T^n x = x`) is `E(n)` for every `n ≥ 1`. We state exactly this existence claim.
(By the standard characterization of such "realizable" sequences, it is equivalent to
`∑_{d | n} μ(d) E(n/d)` being nonnegative and divisible by `n` for every `n ≥ 1`, i.e. to every
term of A060164 being a nonnegative integer.) The count `Set.ncard` is `0` for an infinite set,
and `E(n) > 0`, so each set of periodic points in the statement is finite.

Sanity check (python): the recurrence gives 1, 1, 5, 61, 1385, 50521; Möbius inversion gives all
17 listed terms of A060164; and `∑_{d | n} μ(d) E(n/d)` is nonnegative and divisible by `n` for all
`n ≤ 300`.
-/

namespace OMA.S_oeis_a060164

/-- The Euler (secant) numbers A000364. -/
def E : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1),
      (-1 : ℤ) ^ (n - k.val) * ((2 * (n + 1)).choose (2 * k.val) : ℤ) * E k.val
termination_by n => n
decreasing_by exact k.isLt

/-- The conjecture: some map has exactly `E(n)` points of period `n`, for every `n ≥ 1`. -/
theorem main : ∃ (X : Type) (T : X → X),
    ∀ n : ℕ, 1 ≤ n → (({x : X | T^[n] x = x}.ncard : ℕ) : ℤ) = E n := by
  sorry

end OMA.S_oeis_a060164
