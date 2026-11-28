import Mathlib

/-!
# A119350: First differences of A118374.

Source: https://oeis.org/A119350
Credit: @Solfanbtc

Conjecture (John W. Layman, OEIS A119350, %F line): define `g(1) = 1` and, for `i > 1`,
`g(i) = 2 g(i-1) + 2^(i-2)`; also `h(1) = 1`, `h(2) = 4` and, for `i > 2`,
`h(i) = h(i-1) + 2^(i-2)`. Then
`a(n) = h(i)` if `n = g(i)`,
`a(n) = 1` if `g(i) - 2^(i-2) ≤ n < g(i)`, and
`a(n) = a(n - g(i-1))` if `g(i-1) < n < g(i) - 2^(i-2)`.
(Verified there for the first 1000 terms.)

Definitions.
* A118374: `b(1) = 1` and, for `n > 1`, `b(n)` is the smallest integer `> b(n-1)` such that
  `b(n) + b(i)` is not of the form `k 2^k - 1` (`k ≥ 1`) for `i = 1, ..., n-1`.
  `pre n = [b(1), ..., b(n)]`; the step uses classical choice (`Nat.find`), with the junk value
  `0` if no admissible integer existed (one always exists: the forbidden values form finitely
  many translates of the density-zero set `{k 2^k - 1}`).
* A119350 (offset 1): `a(n) = b(n+1) - b(n)`.
* The three rules are stated for every `i ≥ 2` (where `2^(i-2)` is an integer), together with
  `a(1) = h(1)` (the case `i = 1`, `n = g(1) = 1`). The intervals `(g(i-1), g(i)]`, `i ≥ 2`,
  cover all `n ≥ 2`, so this determines `a` completely. Subtraction is in `ℕ`; in each rule
  `n > g(i-1)` or `g(i) - 2^(i-2) = 2 g(i-1) ≥ 1`, so nothing is truncated.

Checked with python3: the greedy definition reproduces all listed %S/%T/%U terms of A119350
and of A118374, and the conjecture holds for all `n ≤ 6000`.
-/

namespace OMA.S_oeis_a119350

/-- `g(1) = 1`, `g(i) = 2 g(i-1) + 2^(i-2)` (`g 0` is an unused placeholder). -/
def g : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | i + 2 => 2 * g (i + 1) + 2 ^ i

/-- `h(1) = 1`, `h(2) = 4`, `h(i) = h(i-1) + 2^(i-2)` (`h 0` is an unused placeholder). -/
def h : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | i + 3 => h (i + 2) + 2 ^ (i + 1)

/-- `x` is of the form `k 2^k - 1` with `k ≥ 1`. -/
def IsForbidden (x : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ x + 1 = k * 2 ^ k

open Classical in
/-- The next term of A118374 after the list `l` of its first terms. -/
noncomputable def nextTerm (l : List ℕ) : ℕ :=
  if hx : ∃ x : ℕ, l.getLastD 0 < x ∧ ∀ y ∈ l, ¬ IsForbidden (x + y) then Nat.find hx else 0

/-- `pre n = [b(1), ..., b(n)]`, the first `n` terms of A118374. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 => pre (n + 1) ++ [nextTerm (pre (n + 1))]

/-- A118374 (offset 1). -/
noncomputable def b (n : ℕ) : ℕ := (pre n).getD (n - 1) 0

/-- A119350 (offset 1): first differences of A118374. -/
noncomputable def a (n : ℕ) : ℕ := b (n + 1) - b n

/-- Layman's conjectured recursive description of A119350. -/
theorem main : a 1 = h 1 ∧ ∀ i : ℕ, 2 ≤ i → ∀ n : ℕ,
    (n = g i → a n = h i) ∧
    (g i - 2 ^ (i - 2) ≤ n → n < g i → a n = 1) ∧
    (g (i - 1) < n → n < g i - 2 ^ (i - 2) → a n = a (n - g (i - 1))) := by
  sorry

end OMA.S_oeis_a119350
