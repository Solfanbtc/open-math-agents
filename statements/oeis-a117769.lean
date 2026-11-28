import Mathlib

/-!
# A117769: Lucas numbers for which the product of the digits is a Fibonacci number.

Source: https://oeis.org/A117769
Credit: @Solfanbtc

Conjecture (Chai Wah Wu, Mar 12 2016, comment in A117769): all terms `> 18` have a `0` digit,
i.e. are members of A011540.

Formalization.
* Lucas numbers (A000204, offset 1 in this entry): `L 0 = 2`, `L 1 = 1`,
  `L (n+2) = L (n+1) + L n`; the terms of A117769 are the `L n`, `n ≥ 1`, whose product of
  decimal digits is a Fibonacci number `Nat.fib k` (A000045, `0` included). The conjecture only
  concerns terms `> 18`, so the convention for `L 0 = 2` is irrelevant.
* "Has a `0` digit": `0 ∈ Nat.digits 10 (L n)`.

Checked with python3: the definition reproduces all listed %S/%T/%U terms, and among
`L 1, ..., L 3000` every term `> 18` has a digit `0`.
-/

namespace OMA.S_oeis_a117769

/-- The Lucas numbers, `L 0 = 2`, `L 1 = 1`. -/
def L : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => L (n + 1) + L n

/-- The product of the decimal digits. -/
def digitProd (x : ℕ) : ℕ := (Nat.digits 10 x).prod

/-- Every Lucas number `> 18` whose digit product is a Fibonacci number has a digit `0`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 18 < L n → (∃ k, Nat.fib k = digitProd (L n)) →
    0 ∈ Nat.digits 10 (L n) := by
  sorry

end OMA.S_oeis_a117769
