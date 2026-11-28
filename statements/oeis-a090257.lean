import Mathlib

/-!
# A090257: a(1) = 1, then least square such that every partial concatenation is a prime.

Source: https://oeis.org/A090257
Credit: @Solfanbtc

Conjecture (OEIS A090257, %C line): the sequence is infinite.

The sequence (offset 0 in OEIS): `a(0) = 1`, and for `n ≥ 1`, `a(n)` is the least square such
that the decimal concatenation `a(0) a(1) ... a(n)` is prime (11, 1181, 1181729, ... are prime).
The sequence is infinite exactly when this greedy construction never gets stuck, i.e. at every
step some square appended to the current concatenation gives a prime.

Formalization.
* `concat x y = x * 10 ^ (number of decimal digits of y) + y`, the decimal concatenation for
  `y ≥ 1`. Only positive squares `k ^ 2`, `k ≥ 1`, are considered: appending the square `0`
  would really append the digit `0`, giving a multiple of 10, never a prime, so excluding it
  changes nothing (and avoids `Nat.digits 10 0 = []`). The least such square is `k ^ 2` for
  the least such `k`.
* `prefixVal n` is `some` of the concatenation `a(0) ... a(n)` while the sequence is defined,
  and `none` once no square works. The conjecture is `∀ n, (prefixVal n).isSome`.
* The other %C remark (`a(n) ≡ 0 (mod 9)` for `n > 1`) is not part of this statement.

Checked with python3: the greedy construction reproduces all 38 listed %S/%T/%U terms
(1, 1, 81, 729, 441, ..., 1535121, 9018009).
-/

namespace OMA.S_oeis_a090257

/-- Decimal concatenation of `x` followed by `y` (for `y ≥ 1`). -/
def concat (x y : ℕ) : ℕ := x * 10 ^ (Nat.digits 10 y).length + y

open Classical in
/-- `prefixVal n = some (a(0) a(1) ... a(n))` (decimal concatenation) while the sequence is
defined, `none` once no positive square can be appended to give a prime. -/
noncomputable def prefixVal : ℕ → Option ℕ
  | 0 => some 1
  | n + 1 =>
    match prefixVal n with
    | none => none
    | some x =>
      if h : ∃ k : ℕ, 0 < k ∧ (concat x (k ^ 2)).Prime then
        some (concat x (Nat.find h ^ 2))
      else none

/-- A090257 is infinite: the greedy construction is defined at every step. -/
theorem main : ∀ n : ℕ, (prefixVal n).isSome := by
  sorry

end OMA.S_oeis_a090257
