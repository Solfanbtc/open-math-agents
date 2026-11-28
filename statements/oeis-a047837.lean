import Mathlib

/-!
# A047837: Honaker's triangle problem: form a triangle with base of length n, all entries different, all row sums equal; a(n) gives minimal r

Source: https://oeis.org/A047837 (and https://oeis.org/A047873)
Credit: @Solfanbtc

A Honaker triangle with base `n` has rows of lengths `1, 2, …, n`; its entries are pairwise
distinct positive integers (as in the OEIS examples, e.g. `a(3) = 8`: `8; 2 6; 1 3 4`) and all
row sums are equal. `A047837 n` is the minimal common row sum.

A047873 is the lower bound
`a(n) = max_{r=1..n-1} ⌈t(t(n) - t(r-1)) / (n - r + 1)⌉`, with `t` the triangular numbers
(rows `r..n` hold `t(n) - t(r-1)` distinct positive integers, whose sum is at least
`t(t(n) - t(r-1))`, shared among `n - r + 1` rows).

Conjecture (A047837 comment): A047837 agrees with A047873 for all `n` (verified for `n < 365`).

Minimal fix: the range `r = 1..n-1` is empty for `n = 1`, while both sequences start with
`a(1) = 1`. We take `r = 1..n` instead; the extra term `r = n` is `t(n)`, which never exceeds the
`r = 1` term for `n ≥ 2` (checked numerically for `2 ≤ n < 2000`, and the listed data of A047873
for `n = 1..40` is reproduced), and for `n = 1` it gives `1`.
-/

namespace OMA.S_oeis_a047837

/-- Triangular numbers `t(m) = m(m+1)/2` (A000217). -/
def tri (m : ℕ) : ℕ := m * (m + 1) / 2

/-- `S` is the common row sum of some Honaker triangle with base `n`: an injective filling
`f` of the triangle (row `i : Fin n` has `i + 1` cells) by positive integers, every row
summing to `S`. -/
def IsHonakerRowSum (n S : ℕ) : Prop :=
  ∃ f : (Σ i : Fin n, Fin (i.val + 1)) → ℕ,
    Function.Injective f ∧ (∀ x, 0 < f x) ∧
    ∀ i : Fin n, ∑ j : Fin (i.val + 1), f ⟨i, j⟩ = S

/-- A047837: the minimal row sum of a Honaker triangle with base `n`. -/
noncomputable def a047837 (n : ℕ) : ℕ := sInf {S | IsHonakerRowSum n S}

/-- A047873 (with the range `r = 1..n`, see the module docstring):
`max_{r} ⌈t(t(n) - t(r-1)) / (n - r + 1)⌉`, the ceiling written as `(a + b - 1) / b`. -/
def a047873 (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup fun r =>
    (tri (tri n - tri (r - 1)) + (n - r + 1) - 1) / (n - r + 1)

/-- Conjecture (OEIS A047837): A047837(n) = A047873(n) for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a047837 n = a047873 n := by
  sorry

end OMA.S_oeis_a047837
