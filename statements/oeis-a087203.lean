import Mathlib

/-!
# A087203: a(n) is the smallest m such that m > A037155(n) and n! - m is prime.

Source: https://oeis.org/A087203
Credit: @Solfanbtc

For `n ≥ 3`, let `M n` be the set of `m > 1` (with `m < n!`) such that `n! - m` is prime.
A037155(n) (`n! - p`, with `p` the largest prime `< n! - 1`) is the least element of `M n`, and
A087203(n) is the least element of `M n` greater than A037155(n), i.e. the second smallest
element. Example: `3! = 6`; `6 - 3 = 3` and `6 - 4 = 2` are prime, so A037155(3) = 3 and
`a(3) = 4`. Checked with python3 against the first 30 terms (`3 ≤ n ≤ 32`).

Conjecture (F. Firoozbakht, 2003; "For 3 < n < 643, a(n) is prime"): except for the first term
`a(3) = 4`, every term is prime. `main` states this for all `n ≥ 4`.
-/

namespace OMA.S_oeis_a087203

/-- The `m > 1` with `m < n!` and `n! - m` prime. -/
def M (n : ℕ) : Set ℕ := {m | 1 < m ∧ m < n.factorial ∧ (n.factorial - m).Prime}

/-- A037155(n): the least element of `M n`. -/
noncomputable def A037155 (n : ℕ) : ℕ := sInf (M n)

/-- A087203(n): the least element of `M n` above A037155(n). -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | m ∈ M n ∧ A037155 n < m}

theorem main : ∀ n : ℕ, 4 ≤ n → (a n).Prime := by
  sorry

end OMA.S_oeis_a087203
