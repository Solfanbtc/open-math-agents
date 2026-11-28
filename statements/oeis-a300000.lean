import Mathlib

/-!
# A300000: The sum of the first n terms of the sequence is the concatenation of the first n digits of the sequence, with a(1) = 1.

Source: https://oeis.org/A300000
Credit: @Solfanbtc

Conjecture (Michael S. Branicky, Dec 07 2020, in the entry): a(n) contains all ten digits for
n >= 4280. (Verified by him through a(169000).)

Conventions.
* Let D be the infinite string of decimal digits of a(1), a(2), a(3), ... written one after
  the other, and c(n) the number whose decimal digits are the first n digits of D. The defining
  property is a(1) + ... + a(n) = c(n). a(1) = 1, and a(2) = 10 is the smallest integer not
  yet present that leads to no contradiction (for 2 ≤ x ≤ 9, 1 + x ≠ 10 + x; for x = 10,
  1 + 10 = 11 = c(2)). For n > 2 (M. F. Hasler's comment) a(n) is then determined recursively:
  c(n) = 10·c(n-1) + D_n, where D_n is the n-th digit of D, which already belongs to the
  digits of a(1), ..., a(n-1); and a(n) = c(n) - c(n-1). This is the recursion used below
  (also the entry's Python program).
* Checked with python3: this reproduces all listed terms, the first appearances of the digits
  given in the entry (1, 0, 9, 8, 2, 7, 3, 6, 5, 4 first in a(1), a(2), a(3), a(12), a(68),
  a(71), a(2280), a(2283), a(2417), a(4280)), and the conjecture for 4280 ≤ n ≤ 6000.
* "a(n) contains all ten digits": every digit 0..9 occurs in the decimal representation of
  a(n).
-/

namespace OMA.S_oeis_a300000

/-- Decimal digits of `m`, most significant first. -/
def decDigits (m : ℕ) : List ℕ := (Nat.digits 10 m).reverse

/-- `state j` describes index `n = j + 2`: the digit string of a(1), ..., a(n), then `c(n)`,
then `a(n)`. -/
def state : ℕ → List ℕ × ℕ × ℕ
  | 0 => ([1, 1, 0], 11, 10)
  | j + 1 =>
    let s := state j
    let n := j + 3
    let c' := 10 * s.2.1 + s.1.getD (n - 1) 0
    let a' := c' - s.2.1
    (s.1 ++ decDigits a', c', a')

/-- A300000, 1-indexed (`a 0 = 0` is an unused placeholder). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (state n).2.2

theorem main : ∀ n : ℕ, 4280 ≤ n → ∀ d : ℕ, d < 10 → d ∈ Nat.digits 10 (a n) := by
  sorry

end OMA.S_oeis_a300000
