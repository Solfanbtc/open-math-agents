import Mathlib

/-!
# A026328: paths of nonnegative integers from 2 to 5 with steps in {-1, 0, 1}

Source: https://oeis.org/A026328
Credit: @Solfanbtc

`a(n)` is the number of sequences `(s(0), ..., s(n))` of nonnegative integers with
`|s(i) - s(i-1)| ≤ 1` for `1 ≤ i ≤ n`, `s(0) = 2` and `s(n) = 5`. Offset 3:
1, 4, 15, 50, 161, 504, ... (`a(3) = 1`).

`paths n s` counts such sequences of length `n` starting at `2` and ending at `s`
(the guard `1 ≤ s` keeps every entry nonnegative).

Conjecture (R. J. Mathar, Jun 23 2013), stated for `n ≥ 7`, so that `a(n-4)` is a term of the
sequence (offset 3):
`-(n+9)(n-3) a(n) + (6n^2+21n-128) a(n-1) + (-9n^2-3n+152) a(n-2) - 4(n+4)(n-1) a(n-3)
 + 12(n-1)(n-2) a(n-4) = 0`.

Sanity check: python reproduces all 27 listed terms from this definition and confirms the
recurrence for `n < 400`; `#eval` in Lean gives the first listed terms.
-/

namespace OMA.S_oeis_a026328

/-- Number of nonnegative integer sequences of length `n` with steps in `{-1, 0, 1}`, from `2`
to `s`. -/
def paths : ℕ → ℕ → ℕ
  | 0, s => if s = 2 then 1 else 0
  | n + 1, s => (if 1 ≤ s then paths n (s - 1) else 0) + paths n s + paths n (s + 1)

/-- A026328. -/
def a (n : ℕ) : ℕ := paths n 5

/-- Mathar's conjectured recurrence for A026328. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    let m : ℤ := n;
    -(m + 9) * (m - 3) * a n + (6 * m ^ 2 + 21 * m - 128) * a (n - 1)
      + (-9 * m ^ 2 - 3 * m + 152) * a (n - 2) - 4 * (m + 4) * (m - 1) * a (n - 3)
      + 12 * (m - 1) * (m - 2) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026328
