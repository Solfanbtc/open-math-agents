import Mathlib

/-!
# A058814: Numbers k such that k divides the number of digits of k!.

Source: https://oeis.org/A058814
Credit: @Solfanbtc

Terms: 1, 22, 23, 24, 266, 267, 268, 2712, 2713, 27175, 27176, 271819, 271820, 271821, ...
Apart from the isolated term 1, they come in clusters of consecutive integers near
`10^m · e` (the entry: "For large m, 10^m*C -> 10^m*e").

Conjecture (Robert G. Wilson v, Feb 04 2013): "There exist at least two contiguous terms for each
k > 0, sometimes three contiguous terms, but never four."

Reading: `k` here indexes the clusters, i.e. the powers of ten `10^m` of the preceding sentence
(the cluster near `10^m · e` consists of the terms with `m + 1` digits); `m = 0` (the lone term 1)
is excluded by `k > 0`. So the claim is: for every `m ≥ 1`, the terms in `[10^m, 10^(m+1))` form a
block of 2 or 3 consecutive integers. ("Sometimes three" is witnessed by `m = 1, 2, 5, 8` already
and needs no separate statement; we state the "at least two, never four" content together with
contiguity.)

Sanity check (python): an exact computation for `k ≤ 3000` agrees with the listed terms, and the
listed terms with `m + 1` digits (`1 ≤ m ≤ 8`) are blocks of 2 or 3 consecutive integers.
-/

namespace OMA.S_oeis_a058814

/-- `k` is a term of A058814: `k` divides the number of decimal digits of `k!`. -/
def IsTerm (k : ℕ) : Prop := k ∣ (Nat.digits 10 k.factorial).length

/-- Wilson's conjecture: for each `m ≥ 1`, the terms with `m + 1` digits are 2 or 3 consecutive
integers. -/
theorem main : ∀ m : ℕ, 1 ≤ m →
    ∃ a L : ℕ, 2 ≤ L ∧ L ≤ 3 ∧
      {k : ℕ | 10 ^ m ≤ k ∧ k < 10 ^ (m + 1) ∧ IsTerm k} = Set.Ico a (a + L) := by
  sorry

end OMA.S_oeis_a058814
