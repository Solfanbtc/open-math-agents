import Mathlib

/-!
# A084229: Let b(1)=1, b(2)=2, b(n) = sum of digits of b(1)+b(2)+b(3)+...+b(n-1), sequence gives values of n such that b(n)=3.

Source: https://oeis.org/A084229
Credit: @Solfanbtc

`b` is A084228 (offset 1): `b(1) = 1`, `b(2) = 2` and, for `n ≥ 3`, `b(n)` is the sum of the
decimal digits of `T(n-1) = b(1) + ... + b(n-1)`. A084229 lists, in increasing order
(offset 1), the `n` with `b(n) = 3`; so `a(n) = Nat.nth (fun k => b k = 3) (n - 1)`.
We checked by `#eval` that `b` below gives the terms 3, 5, ..., 159 of %S below 200, and
(with an equivalent loop) all terms 3, 5, ..., 5161 of %S below 6000.

Conjecture (Benoit Cloitre, 2003): `a(n) / n^3` is bounded, i.e. there is `C` with
`a(n) ≤ C n^3` for all `n ≥ 1`. (If there were only finitely many terms, `Nat.nth` would
return 0 for the missing indices.)
-/

namespace OMA.S_oeis_a084229

/-- `T n = b(1) + ... + b(n)`. -/
def T : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | n + 3 => T (n + 2) + (Nat.digits 10 (T (n + 2))).sum

/-- A084228 (offset 1; `b 0` is an unused placeholder). -/
def b : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => (Nat.digits 10 (T (n + 2))).sum

/-- A084229 (offset 1): the `n`-th index `k` with `b k = 3`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => b k = 3) (n - 1)

/-- Cloitre's conjecture: `a(n) / n^3` is bounded. -/
theorem main : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → (a n : ℝ) ≤ C * (n : ℝ) ^ 3 := by
  sorry

end OMA.S_oeis_a084229
