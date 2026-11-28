import Mathlib

/-!
# A061341: Numbers not ending in 0 whose cubes are concatenations of other cubes

Source: https://oeis.org/A061341
Credit: @Solfanbtc

`n` (not ending in `0`) is a term if the decimal representation of `n^3` is the concatenation of
the decimal representations of at least two cubes ("other cubes": not just `n^3` itself). The
pieces are cubes of nonnegative integers written without leading zeros, `0` being written `0`;
e.g. `2272^3 = 11728027648 = 1_1728_0_27_64_8`. With these conventions a Python search reproduces
all data terms below `130000`: `22, 303, 1006, 2272, 3003, 6001, …`.

Conjecture (François Marques, Jul 11 2021, OEIS comment): the last digit of `a(n)` is in
`{1, 2, 3, 4, 5, 6, 8}`, and if it is `3` then there is `k ≥ 2` such that `a(n) = 3·10^k + 3`.
(Python: true for all terms below `130000`.)
-/

namespace OMA.S_oeis_a061341

/-- Decimal digits of `p`, most significant first (`0` is written `0`). -/
def dstr (p : ℕ) : List ℕ := if p = 0 then [0] else (Nat.digits 10 p).reverse

/-- `n` is a term of A061341. -/
def IsTerm (n : ℕ) : Prop :=
  1 ≤ n ∧ ¬ 10 ∣ n ∧ ∃ parts : List ℕ, 2 ≤ parts.length ∧ (∀ p ∈ parts, ∃ c : ℕ, p = c ^ 3) ∧
    parts.flatMap dstr = dstr (n ^ 3)

/-- Marques' conjecture on the last digit of the terms. -/
theorem main : ∀ n : ℕ, IsTerm n →
    n % 10 ∈ ({1, 2, 3, 4, 5, 6, 8} : Finset ℕ) ∧ (n % 10 = 3 → ∃ k ≥ 2, n = 3 * 10 ^ k + 3) := by
  sorry

end OMA.S_oeis_a061341
