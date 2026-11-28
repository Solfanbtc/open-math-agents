import Mathlib

/-!
# A057896: Nonnegative numbers that can be written as m^k - m (with m and k nonnegative) in more than one way.

Source: https://oeis.org/A057896
Credit: @Solfanbtc

A representation of `x` is a pair `(m, k)` of nonnegative integers with `m^k - m = x` (and
`m^k ≥ m`, so that the difference is nonnegative; `0^0 = 1`). `x` is a term if it has at least
two distinct representations. `0` is a term (`0 = m^1 - m` for every `m`); the other terms are
6, 30, 210, 240, 2184, 8190, 78120, 24299970 (e.g. `30 = 2^5 - 2 = 6^2 - 6`).

Conjecture (Bennett, 2001, as recorded in the entry): the sequence is finite and complete, i.e.
its terms are exactly the nine listed numbers. (The entry: any further term exceeds `10^50`,
Max Alekseyev, 2026.) Checked with python3: among `x ≤ 10^12` the terms are exactly the nine
listed numbers.
-/

namespace OMA.S_oeis_a057896

/-- `(m, k)` is a representation of `x` as `m^k - m`. -/
def IsRep (x : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ≤ p.1 ^ p.2 ∧ p.1 ^ p.2 - p.1 = x

/-- Bennett's conjecture: the listed terms are all the terms of A057896. -/
theorem main : {x : ℕ | ∃ p q : ℕ × ℕ, p ≠ q ∧ IsRep x p ∧ IsRep x q} =
    {0, 6, 30, 210, 240, 2184, 8190, 78120, 24299970} := by
  sorry

end OMA.S_oeis_a057896
