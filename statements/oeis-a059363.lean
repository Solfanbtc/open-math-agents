import Mathlib

/-!
# A059363: Lexicographically earliest increasing sequence with Ω(a(i)+a(j)) = Ω(a(i)) + Ω(a(j)).

Source: https://oeis.org/A059363
Credit: @Solfanbtc

`a` (offset 1) is the lexicographically earliest increasing sequence of positive integers such
that `Ω(a(i) + a(j)) = Ω(a(i)) + Ω(a(j))` for all `1 ≤ i < j`, where `Ω = A001222` counts prime
factors with multiplicity. As usual in the OEIS it is built greedily: `a(1) = 1`, and `a(n+1)` is
the least `m > a(n)` with `Ω(a(i) + m) = Ω(a(i)) + Ω(m)` for every `i ≤ n`.
Data: `1, 2, 25, 745, 2306, 7081, 31945, 435866, ...`.

Conjecture (in the entry): `Ω(a(n)) = 2` for all `n > 2` (the values are `0, 1, 2, 2, 2, ...`).

A python3 check: the greedy rule reproduces `a(1..10)`, and `Ω(a(n)) = 2` for `3 ≤ n ≤ 10`.

Conventions: `build k` is the list `[a(1), ..., a(k+1)]`; each new term is `sInf` of the set of
admissible `m`. (If at some stage no admissible `m` existed, `sInf ∅ = 0` would be appended and the
conjecture would fail there: the conjecture includes that the greedy construction never stops.)
-/

namespace OMA.S_oeis_a059363

open ArithmeticFunction

/-- `build k = [a(1), ..., a(k+1)]`. -/
noncomputable def build : ℕ → List ℕ
  | 0 => [1]
  | k + 1 =>
      build k ++ [sInf {m : ℕ | ∀ x ∈ build k, x < m ∧ cardFactors (x + m) = cardFactors x + cardFactors m}]

/-- `a n` for `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ := (build (n - 1)).getD (n - 1) 0

/-- The conjecture: `Ω(a(n)) = 2` for all `n > 2`. -/
theorem main : ∀ n : ℕ, 2 < n → cardFactors (a n) = 2 := by
  sorry

end OMA.S_oeis_a059363
