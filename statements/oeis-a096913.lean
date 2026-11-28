import Mathlib

/-!
# A096913: Numbers k such that (largest digit of k)^(smallest digit of k) + k is a square.

Source: https://oeis.org/A096913
Credit: @Solfanbtc

For `k ≥ 0`, `M k` and `m k` are the largest and smallest decimal digits of `k` (the only digit of
0 is 0). `k` is a term when `(M k)^(m k) + k` is a perfect square, e.g. `8^3 + 388 = 900`. For
`k = 0` this is `0^0 + 0 = 1`, a square, so 0 is a term (the data start with 0).

Conjecture (in the entry): 0 and 3844 (`= 62^2`; `8^3 + 3844 = 4356 = 66^2`) are the only squares
in this sequence. `main` states that the squares in the sequence are exactly 0 and 3844.
Status: the comment of M. Wenders (2012) argues that only finitely many squares can occur (for
large squares the gap to the next square exceeds `9^9`) and reports an exhaustive PARI search
confirming the conjecture. (python3: no other square `k ≤ 4·10^10`.)
-/

namespace OMA.S_oeis_a096913

/-- Decimal digits of `k` (with `[0]` for `k = 0`). -/
def digs (k : ℕ) : List ℕ := if k = 0 then [0] else Nat.digits 10 k

/-- Largest decimal digit. -/
def M (k : ℕ) : ℕ := (digs k).foldl max 0

/-- Smallest decimal digit. -/
def m (k : ℕ) : ℕ := (digs k).foldl min 9

theorem main : {k : ℕ | IsSquare k ∧ IsSquare (M k ^ m k + k)} = {0, 3844} := by
  sorry

end OMA.S_oeis_a096913
