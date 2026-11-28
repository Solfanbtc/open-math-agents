import Mathlib

/-!
# A062518: largest k such that n^k does not contain all ten decimal digits (conjectural)

Source: https://oeis.org/A062518
Credit: @Solfanbtc

A062518(n) is the "conjectural largest exponent k such that n^k does not contain all of the digits
0 through 9 (in decimal notation) or 0 if no such k exists (for example if n is a power of 10)".
Data (offset 1, `n = 1..69`): 0, 168, 106, 84, 65, 64, 61, 56, 53, 0, 41, 51, ...
N. J. A. Sloane: "I do not know how many of these terms have been proved to be correct."

The conjecture is that the listed values are correct. For a listed value `v = a(n) > 0` this
means: `n^v` misses some digit, and `n^k` contains all ten digits for every `k > v`. (The two
terms equal to 0, `n = 1` and `n = 10`, are powers of 10, for which there is no largest such `k`
because every power misses a digit; nothing conjectural there.) We also include the other two
conjectural values recorded in the entry:
* `a(110) = 38` (Christopher J. Smyth): `110^38` misses the digit 2, "while, conjecturally, all
  higher powers of 110 contain all ten digits";
* (Robert G. Wilson v) 1023458769, 1023458967, 1023467895, 1023469875, 1023475986, 1023478695
  satisfy `a(n) = 0` because every power `n^k`, `k ≥ 1`, contains all ten digits.
Wilson's list of first occurrences contains question marks and an open-ended "...", so it is not
included.

Sanity check (python): for each of the 67 positive listed values, `n^v` misses a digit and
`n^k` is pandigital for `v < k < v + 1500`; the same holds for `110` and `38`; Wilson's six numbers
have pandigital `k`-th powers for `1 ≤ k < 400`.
-/

namespace OMA.S_oeis_a062518

/-- `x` contains all ten decimal digits. -/
def Pandigital (x : ℕ) : Prop := ∀ d, d < 10 → d ∈ Nat.digits 10 x

/-- The listed terms `a(1), ..., a(69)`. -/
def data : Fin 69 → ℕ :=
  ![0, 168, 106, 84, 65, 64, 61, 56, 53, 0, 41, 51, 37, 34, 34, 42, 27, 25, 44, 168, 29, 24,
    50, 23, 29, 31, 28, 28, 45, 106, 28, 18, 24, 34, 18, 32, 25, 17, 41, 84, 23, 19, 20, 29,
    39, 32, 15, 29, 16, 65, 29, 29, 30, 18, 17, 33, 19, 31, 27, 64, 26, 19, 24, 28, 17, 15, 21,
    25, 13]

/-- `v` is the largest exponent `k` such that `n^k` is not pandigital. -/
def IsLargestNonPandigitalExp (n v : ℕ) : Prop :=
  ¬ Pandigital (n ^ v) ∧ ∀ k, v < k → Pandigital (n ^ k)

/-- The listed (and the other recorded) values of A062518 are correct. -/
theorem main :
    (∀ i : Fin 69, 0 < data i → IsLargestNonPandigitalExp (i.val + 1) (data i)) ∧
    IsLargestNonPandigitalExp 110 38 ∧
    (∀ w ∈ ({1023458769, 1023458967, 1023467895, 1023469875, 1023475986, 1023478695} :
      Finset ℕ), ∀ k, 1 ≤ k → Pandigital (w ^ k)) := by
  sorry

end OMA.S_oeis_a062518
