import Mathlib

/-!
# A069180: F(n) and n! are relatively prime where F(n) are the Fibonacci numbers.

Source: https://oeis.org/A069180
Credit: @Solfanbtc

The entry (offset 1) lists the positive integers `n` with `gcd(F(n), n!) = 1`:
1, 2, 7, 11, 13, 17, 19, 22, 23, 26, ... (checked against every term of %S, %T, %U).

%F (B. Cloitre, conjecture): `a(n) = C*n*Log(n) + 0(n*Log(n))` with `0,6 < C < 0,7`.
Reading: the decimal commas are `0.6` and `0.7`; the error term `0(n log n)` is read as
little-o, since with big-O the claim would hold for every `C` once `a(n) = O(n log n)`
and the bounds on `C` would carry no content. So the conjecture says there is a constant
`C ∈ (0.6, 0.7)` with `a(n) - C n log n = o(n log n)`, i.e. `a(n) / (n log n) → C`.

Numerically `a(n)/(n log n)` is about 0.666 at n = 1000, 0.640 at n = 10^4 and 0.616 at
n = 59095 (a(n) ≈ 4·10^5), still decreasing; the conjecture is open as far as the entry says.

`a n` below is the `n`-th term for `n ≥ 1` (`Nat.nth` is 0-indexed, hence `n - 1`).
-/

namespace OMA.S_oeis_a069180

/-- `n ≥ 1` with `F(n)` and `n!` coprime. -/
def P (n : ℕ) : Prop := 0 < n ∧ Nat.Coprime (Nat.fib n) n.factorial

/-- The OEIS sequence A069180, offset 1. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

theorem main : ∃ C : ℝ, 0.6 < C ∧ C < 0.7 ∧
    (fun n : ℕ => (a n : ℝ) - C * n * Real.log n) =o[Filter.atTop]
      (fun n : ℕ => (n : ℝ) * Real.log n) := by
  sorry

end OMA.S_oeis_a069180
