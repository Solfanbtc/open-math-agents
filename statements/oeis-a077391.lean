import Mathlib

/-!
# A077391: Smallest n-digit prime which leaves a prime at every step if most significant digit and least significant digit are deleted until a one digit or two digit prime is obtained, or 0 if no such prime exists.

Source: https://oeis.org/A077391
Credit: @Solfanbtc

Conjecture (OEIS entry, %C): no term is zero, i.e. for every `n ≥ 1` there is an `n`-digit prime
which leaves a prime at every step when its most and least significant digits are deleted, until a
one- or two-digit number is obtained.

Conventions:
* Offset 1. `p` is `n`-digit when `(Nat.digits 10 p).length = n` (no leading zero).
* After deleting `j` digits at each end (`2j < n`), the remaining block of `n - 2j` digits is read as
  a number, leading zeros allowed: the example gives `100237 → 0023 = 23 → 02 = 2`. With the
  little-endian list `L = Nat.digits 10 p` this block is `Nat.ofDigits 10 ((L.drop j).take (n - 2j))`
  (leading zeros of the block are trailing zeros of the sublist, and do not change its value).
* The case `j = 0` is `p` itself; the process stops at length `1` or `2`, i.e. `j` ranges over
  `2j < n`.
* Checked in Python: the least such prime for `n = 1, …, 10` is `2, 11, 127, 1021, 10313, 100237,
  1002931, 10002331, 100023331, 1000023337`, matching the data.
-/

namespace OMA.S_oeis_a077391

/-- The number formed by the digits of `p` left after deleting `j` digits at both ends. -/
def core (p j : ℕ) : ℕ :=
  Nat.ofDigits 10 (((Nat.digits 10 p).drop j).take ((Nat.digits 10 p).length - 2 * j))

/-- `p` is an `n`-digit number all of whose successive cores (including `p`) are prime. -/
def Good (n p : ℕ) : Prop :=
  (Nat.digits 10 p).length = n ∧ ∀ j : ℕ, 2 * j < n → (core p j).Prime

/-- The conjecture of A077391: no term is zero. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, Good n p := by
  sorry

end OMA.S_oeis_a077391
