import Mathlib

/-!
# A096091: Numbers n with property that largest number formed from digits of n (A004186(n)) is divisible by smallest number formed from digits of n (A004185(n)).

Source: https://oeis.org/A096091
Credit: @Solfanbtc

Conjecture (OEIS A096091, %C line): the numbers `N = d * 10^m * (10^k - 1)/9` (a repdigit
`dd...d` followed by `m` zeros) are all members, since the quotient is `10^m`; there are
infinitely many terms besides these.

Status: proved. Jon E. Schoenfield (Jul 26 2015, comment in A096091) notes that even after
also removing every number whose nonzero digits are all identical and every `10 * k` with `k`
a term, infinitely many terms remain (105, 108, 150, 180, 405, 450, 501, ...; A260461).

Formalization.
* `largest n` (A004186) is the number whose decimal digits are those of `n` sorted in
  decreasing order; `smallest n` (A004185) the one with digits sorted increasingly, leading
  zeros dropped. `Nat.digits` is little-endian, so `largest` uses the increasingly sorted list
  and `smallest` the decreasingly sorted one (zeros then become leading zeros, worth `0`).
* Terms are `n ≥ 1` (offset 1) with `smallest n ∣ largest n`.
* The excluded family: the comment writes `1 < d < 10`, but `d = 1` (`1, 10, 11, 110, ...`)
  is a member for the same reason, and with `d = 1` left out the claim would follow from the
  repunits alone; we take the evident intended reading `1 ≤ d ≤ 9`, `k ≥ 1`, `m ≥ 0`.

Checked with python3: `isTerm` gives exactly the listed %S/%T/%U terms up to 606.
-/

namespace OMA.S_oeis_a096091

/-- A004186: largest number formed from the decimal digits of `n`. -/
def largest (n : ℕ) : ℕ := Nat.ofDigits 10 ((Nat.digits 10 n).insertionSort (· ≤ ·))

/-- A004185: smallest number formed from the decimal digits of `n` (leading zeros dropped). -/
def smallest (n : ℕ) : ℕ := Nat.ofDigits 10 ((Nat.digits 10 n).insertionSort (· ≥ ·))

/-- `n` is a term of A096091. -/
def IsTerm (n : ℕ) : Prop := 1 ≤ n ∧ smallest n ∣ largest n

/-- `n = d * 10^m * (10^k - 1)/9` with `1 ≤ d ≤ 9`, `k ≥ 1`: a repdigit followed by zeros. -/
def IsRepdigitTimesPow (n : ℕ) : Prop :=
  ∃ d k m : ℕ, 1 ≤ d ∧ d ≤ 9 ∧ 1 ≤ k ∧ n = d * 10 ^ m * ((10 ^ k - 1) / 9)

/-- There are infinitely many terms of A096091 that are not a repdigit followed by zeros. -/
theorem main : {n : ℕ | IsTerm n ∧ ¬ IsRepdigitTimesPow n}.Infinite := by
  sorry

end OMA.S_oeis_a096091
