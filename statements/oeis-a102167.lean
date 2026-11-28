import Mathlib

/-!
# A102167: Lightest finite strictly increasing sequence of integers showing once and only once every pair of digits from [00] to [99].

Source: https://oeis.org/A102167
Credit: @Solfanbtc

The terms are written in decimal and concatenated into one digit string (here
`7 19 20 23 ...` gives `71920 23...`). Its adjacent digit pairs, which may straddle two terms
(`[71], [19], [92], [20], [02], [23], ...`), must show each of the 100 pairs `[00]` to `[99]`
exactly once. The weight of such a sequence is the sum of its terms. The listed sequence has
weight 2995 (checked: 47 terms, 101 digits, 100 distinct pairs; `Valid` of the listed terms was
verified in Lean by `decide`).

Conjecture (N. J. A. Sloane, Mar 15 2005: it seems that it is only a conjecture that this
sequence is really the lightest): every such finite strictly increasing sequence has weight at
least 2995. Reading: terms are positive integers written without leading zeros (the entry is
`nonn` and starts at 7); negative terms would make the weight unbounded below.
-/

namespace OMA.S_oeis_a102167

/-- The decimal digits of the terms of `l`, concatenated (most significant digit first). -/
def digitString (l : List ℕ) : List ℕ := l.flatMap (fun n => (Nat.digits 10 n).reverse)

/-- The adjacent pairs of a digit string. -/
def adjPairs (s : List ℕ) : List (ℕ × ℕ) := s.zip s.tail

/-- `l` is a finite strictly increasing sequence of positive integers whose digit string shows
every pair of digits `[de]` exactly once. -/
def Valid (l : List ℕ) : Prop :=
  l.Pairwise (· < ·) ∧ (∀ n ∈ l, 0 < n) ∧
    ∀ d < 10, ∀ e < 10, (adjPairs (digitString l)).count (d, e) = 1

theorem main : ∀ l : List ℕ, Valid l → 2995 ≤ l.sum := by
  sorry

end OMA.S_oeis_a102167
