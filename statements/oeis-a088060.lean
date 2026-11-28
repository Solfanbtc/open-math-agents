import Mathlib

/-!
# A088060: smallest Fibonacci F(k) > F(m) with F(m) + F(k) a square.

Source: https://oeis.org/A088060
Credit: @Solfanbtc

For each `m ≥ 1`, look for the smallest Fibonacci number `F(k) > F(m)` such that `F(m) + F(k)`
is a square, and if it exists append it to the sequence: `3, 3, 34, 13, 89, 14930352` (from
`m = 1, 2, 3, 4, 10, 12`). The sequence has one term for each `m` that admits such a `k`, so it
is finite iff the set of these `m` is finite. (`Nat.fib` has `F(1) = F(2) = 1`.)

Conjecture (entry): the sequence is finite. (Joe Silverman's argument in the entry shows that
for each fixed `F(m)` there are only finitely many `k`; that alone does not give finiteness of
the set of `m`.) Checked with python3: for `m < 300` and `k < 400` the only such `m` are
`1, 2, 3, 4, 10, 12`, giving exactly the listed terms.
-/

namespace OMA.S_oeis_a088060

/-- The conjecture: only finitely many `m ≥ 1` have a Fibonacci `F(k) > F(m)` with
`F(m) + F(k)` a square. -/
theorem main : Set.Finite {m : ℕ | 1 ≤ m ∧
    ∃ k : ℕ, Nat.fib m < Nat.fib k ∧ IsSquare (Nat.fib m + Nat.fib k)} := by
  sorry

end OMA.S_oeis_a088060
