import Mathlib

/-!
# A082844: Start with 3,2 and apply the rule a(a(1)+a(2)+...+a(n)) = a(n), fill in any undefined terms with a(t) = 2 if a(t-1) = 3 and a(t) = 3 if a(t-1) = 2.

Source: https://oeis.org/A082844
Credit: @Solfanbtc

A082844 (offset 1) is defined by its name. `a(1) = 3`, `a(2) = 2`, and for `t ≥ 3`: if
`t = a(1) + ⋯ + a(n)` for some `n` (necessarily `n < t`, and unique since the partial sums
increase strictly), then `a(t) = a(n)`; otherwise `a(t)` is undefined by the rule and is filled
in as `5 - a(t-1)` (2 after a 3, 3 after a 2). `firstTerms t` is the list `[a(1), …, a(t)]`.
A097509 (offset 0): `A097509(n)` is the number of `k ≥ 0` with `⌊k √2⌋ - k = n`.
Checked with python3: `firstTerms` gives the data 3, 2, 3, 2, 2, 3, 2, 3, 2, 2, ..., and
`a(n) = A097509(n+1)` for `1 ≤ n < 6000`.

Conjecture (B. W. J. Irwin, 2016): `a(n) = A097509(n+1)`.

Status: proved. M. Bhargava, K. Kedlaya and L. Ng (solution to Problem B6 of the 81st Putnam
competition, comments of Sep 09 2021 in A082844 and A097509) show that both sequences match the
sequence `c_i` of their first solution.
-/

namespace OMA.S_oeis_a082844

/-- `firstTerms t = [a(1), …, a(t)]`. -/
def firstTerms : ℕ → List ℕ
  | 0 => []
  | 1 => [3]
  | 2 => [3, 2]
  | t + 3 =>
    let l := firstTerms (t + 2)
    match (List.range (t + 2)).find? (fun i => (l.take (i + 1)).sum = t + 3) with
    | some i => l ++ [l.getD i 0]
    | none => l ++ [5 - l.getLastD 0]

/-- A082844(n) (offset 1). -/
def a (n : ℕ) : ℕ := (firstTerms n).getD (n - 1) 0

/-- A097509(n): the number of `k ≥ 0` with `⌊k √2⌋ - k = n`. -/
noncomputable def A097509 (n : ℕ) : ℕ :=
  {k : ℕ | ⌊(k : ℝ) * Real.sqrt 2⌋ - (k : ℤ) = (n : ℤ)}.ncard

theorem main : ∀ n : ℕ, 1 ≤ n → a n = A097509 (n + 1) := by
  sorry

end OMA.S_oeis_a082844
