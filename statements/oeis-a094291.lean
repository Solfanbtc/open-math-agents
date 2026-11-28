import Mathlib

/-!
# A094291: a(n) = maximal value of C(i, j) * C(n-j, n-i) for 0 <= j <= i <= n.

Source: https://oeis.org/A094291
Credit: @Solfanbtc

`a(n) = max_{0 ≤ j ≤ i ≤ n} C(i, j) C(n-j, n-i)` (`n ≥ 1`; `1, 2, 4, 9, 18, 40, 100, …`).

Conjectures in the entry, stated in `main`:
1. (M. F. Hasler, 2026, %F line) `a(n) = C(n-k(n), j(n)) C(n-j(n), k(n))` where
   `⌊n/4⌋ ≤ j(n) ≤ k(n) ≤ j(n) + 1`, and `j` can increase only when `j = k - 1`, and `k` only when
   `j = k`. (This is the maximum taken at `i = n - k`, `k ∈ {j, j+1}`, which is the comment's
   conjecture.) The functions `j(n), k(n)` are not otherwise specified, so this is stated as
   the existence of such `J, K`. "`j` can increase only when `j = k - 1`" is read as
   `J(n+1) > J(n) → J(n) = K(n) - 1`, and likewise for `k`.
2. (Vaclav Kotesovec, 2026) `lim a(n)^(1/n) = (3 + √5)/2`.
Not stated: the comment's observation that the indices with `k = j + 1` "appear to be" the
disjoint union of A094350 and A081009. It depends on how `j(n)` is chosen when several pairs
attain the maximum, which the entry does not fix.
Checked with python3: the definition reproduces the 23 listed terms. For every `n ≤ 300` the
admissible pairs exist, and a choice of `J, K` satisfying both monotonicity rules exists up to
`n = 300`. Also `a(300)^(1/300) ≈ 2.568` (vs `2.618…`), converging slowly.
-/

namespace OMA.S_oeis_a094291

open Filter Topology

/-- A094291(n). -/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup fun i =>
    (Finset.range (i + 1)).sup fun j => i.choose j * (n - j).choose (n - i)

/-- Hasler's and Kotesovec's conjectures. -/
theorem main :
    (∃ J K : ℕ → ℕ, ∀ n : ℕ, 1 ≤ n →
      n / 4 ≤ J n ∧ J n ≤ K n ∧ K n ≤ J n + 1 ∧
      a n = (n - K n).choose (J n) * (n - J n).choose (K n) ∧
      (J n < J (n + 1) → J n + 1 = K n) ∧ (K n < K (n + 1) → J n = K n)) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 ((3 + Real.sqrt 5) / 2)) := by
  sorry

end OMA.S_oeis_a094291
