import Mathlib

/-!
# A380317: The lexicographically earliest sequence of positive numbers which is identical to the
run lengths of its first differences.

Source: https://oeis.org/A380317
Credit: @Solfanbtc

`a(1), a(2), ... = 1, 1, 2, 2, 2, 3, 4, 3, 2, ...`; its first differences `a(n+1) - a(n)` are
`0, 1, 0, 0, 1, 1, -1, -1, 0, 0, 0, ...`, whose run lengths are `1, 1, 2, 2, 2, 3, 4, 3, 2, ...`,
the sequence itself. The entry states: "Conjecture: Every positive integer eventually appears"
(34 is the smallest value not among the first 10000 terms). Also `a(n) = A281579(n) - 1`.

Formalization (0-based: `s n = a(n+1)`):
* `RunsEq s`: all terms are positive and the run lengths of the differences `d n = s(n+1) - s n`
  are `s 0, s 1, ...`: with `B k = s 0 + ⋯ + s (k-1)`, the `k`-th run occupies the indices
  `B k ≤ n < B (k+1)`, so `d` is constant there and changes between index `B (k+1) - 1` and
  `B (k+1)` (runs are maximal);
* lexicographic order on sequences: `t < s` iff they agree before some index `n` and `t n < s n`;
* `IsLexEarliest s`: `RunsEq s` and no `t` with `RunsEq t` is lexicographically smaller.
A lexicographically earliest sequence is unique, so we state: it exists (the entry defines the
sequence as this object) and every positive integer occurs in it.
Check (python3): the 87 listed terms satisfy the run conditions for the first 31 runs.
-/

namespace OMA.S_oeis_a380317

/-- First differences `d n = s (n+1) - s n`. -/
def d (s : ℕ → ℕ) (n : ℕ) : ℤ := (s (n + 1) : ℤ) - s n

/-- `B s k = s 0 + ⋯ + s (k-1)`: the index where the `k`-th run of differences starts. -/
def B (s : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, s i

/-- `s` is positive and equals the sequence of run lengths of its first differences. -/
def RunsEq (s : ℕ → ℕ) : Prop :=
  (∀ n, 0 < s n) ∧ ∀ k, (∀ n, B s k ≤ n → n + 1 < B s (k + 1) → d s n = d s (n + 1)) ∧
    d s (B s (k + 1) - 1) ≠ d s (B s (k + 1))

/-- Lexicographic order on sequences. -/
def LexLT (t s : ℕ → ℕ) : Prop := ∃ n, (∀ i < n, t i = s i) ∧ t n < s n

/-- `s` is the lexicographically earliest sequence with `RunsEq`. -/
def IsLexEarliest (s : ℕ → ℕ) : Prop := RunsEq s ∧ ∀ t, RunsEq t → ¬ LexLT t s

/-- The lexicographically earliest such sequence exists and contains every positive integer. -/
theorem main : ∃ s : ℕ → ℕ, IsLexEarliest s ∧ ∀ k : ℕ, 0 < k → ∃ n, s n = k := by
  sorry

end OMA.S_oeis_a380317
