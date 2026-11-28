import Mathlib

/-!
# A096469: Smallest number m such that the concatenation of n+1 numbers m^0, m^1,..., m^(n-1), m^n is a prime.

Source: https://oeis.org/A096469
Credit: @Solfanbtc

Conjecture (Farideh Firoozbakht, OEIS A096469, %C line): this sequence is infinite, i.e. for
every `n ≥ 1` (offset 1) there is a number `m` such that the decimal concatenation of
`m^0, m^1, ..., m^n` is prime, so that `a(n)` is defined for every `n`.

The other remarks of the same comment are not part of this statement: `a(n) = 1` iff `n + 1`
is in A004023 (the concatenation of `n + 1` ones is the repunit `R_{n+1}`), the terms are odd
and prime to 5, and `a(50) > 11111`.

Formalization.
* `concatList [x₀, ..., x_n]` is the number whose decimal expansion is that of `x₀` followed by
  those of `x₁`, ..., `x_n` (all powers `m^i` with `m ≥ 1` are `≥ 1`, so each has a nonempty
  expansion and no leading zero).
* `m` ranges over positive integers (the "numbers" of the source); `m = 0` would give
  `10^n`, never prime for `n ≥ 1`, so this changes nothing.

Checked with python3 and `#eval`: `concatList ((List.range 4).map (33 ^ ·)) = 133108935937`,
as in the %e example; the least such `m` (Miller-Rabin in python3) reproduces the first 20 listed terms
(1, 3, 33, 23, 237, ..., 523, 21).
-/

namespace OMA.S_oeis_a096469

/-- Decimal concatenation of a list of natural numbers, left to right. -/
def concatList (l : List ℕ) : ℕ :=
  l.foldl (fun acc x => acc * 10 ^ (Nat.digits 10 x).length + x) 0

/-- A096469 is infinite: for every `n ≥ 1` some `m ≥ 1` makes the concatenation
`m^0 m^1 ... m^n` prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ m : ℕ, 1 ≤ m ∧ (concatList ((List.range (n + 1)).map (m ^ ·))).Prime := by
  sorry

end OMA.S_oeis_a096469
