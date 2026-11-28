import Mathlib

/-!
# A025358: Numbers that are the sum of 4 nonzero squares in exactly 2 ways

Source: https://oeis.org/A025358
Credit: @Solfanbtc

`n` is a term iff `A025428(n) = 2`, i.e. there are exactly two multisets `{a, b, c, d}` of
positive integers with `a^2 + b^2 + c^2 + d^2 = n` ("ways" are unordered: counted as
`1 ≤ a ≤ b ≤ c ≤ d`). This reproduces all 54 data terms `31, 34, 36, 37, 39, …, 7424`.

Conjecture (Robert Israel, Nov 03 2017, OEIS comment): the even members of this sequence are all
numbers of the form `k · 4^m` for `k ∈ {9, 17, 29}`, `m ≥ 1`, or `k · 4^m` for
`k ∈ {34, 50, 54, 74, 86, 94}`, `m ≥ 0`. Stated as: for every even `n`, `n` is a term iff it is
of one of these forms. (Python: holds for even `n ≤ 40000`.)
-/

namespace OMA.S_oeis_a025358

/-- `A025428(n)`: the number of `(a, b, c, d)` with `1 ≤ a ≤ b ≤ c ≤ d` and
`a^2 + b^2 + c^2 + d^2 = n`. -/
def ways (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p =>
    p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2.1 ∧ p.2.2.1 ≤ p.2.2.2 ∧
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = n).card

/-- Israel's conjecture on the even terms of A025358. -/
theorem main : ∀ n : ℕ, Even n →
    (ways n = 2 ↔
      ∃ m : ℕ, (1 ≤ m ∧ ∃ k ∈ ({9, 17, 29} : Finset ℕ), n = k * 4 ^ m) ∨
        ∃ k ∈ ({34, 50, 54, 74, 86, 94} : Finset ℕ), n = k * 4 ^ m) := by
  sorry

end OMA.S_oeis_a025358
