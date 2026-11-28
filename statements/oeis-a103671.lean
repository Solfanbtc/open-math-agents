import Mathlib

/-!
# A103671: Smallest m such that the binary representation of n! does not contain m!.

Source: https://oeis.org/A103671
Credit: @Solfanbtc

For `n ≥ 6` (offset 6), `a(n)` is the least `m` such that the binary representation of `m!`
is not a contiguous substring of that of `n!`. `0! = 1! = 1` is always contained.
Containment of binary words is unchanged when both are reversed, so Lean's
least-significant-digit-first `Nat.digits 2` is used.

R. Zumkeller conjectured (at A102730) that this sequence is bounded. C. R. Greathouse IV
(Apr 07 2013, OEIS %C) conjectures the contrary: for every `k` there is `n` with `a(n) > k`.
We state Greathouse's conjecture, the one this entry puts forward; Zumkeller's is its negation.
Since `a(n)` is the least `m` whose factorial is not contained, `a(n) > k` holds iff `m!` is
contained in `n!` for every `m ≤ k`, and that is how the statement is written.

This is stronger than the unboundedness of A102730 (stated as `OMA.S_oeis_a102730.main`):
`a(n) > k` forces at least `k + 1` factorials inside `n!`, but not conversely.
-/

namespace OMA.S_oeis_a103671

/-- The binary representation of `m!` is a contiguous substring of that of `n!`. -/
def Contains (n m : ℕ) : Prop :=
  (Nat.digits 2 m.factorial).IsInfix (Nat.digits 2 n.factorial)

theorem main : ∀ k : ℕ, ∃ n : ℕ, 6 ≤ n ∧ ∀ m ≤ k, Contains n m := by
  sorry

end OMA.S_oeis_a103671
