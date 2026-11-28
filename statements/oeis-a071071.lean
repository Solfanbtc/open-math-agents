import Mathlib

/-!
# A071071: Minimal "powers of 2" set in base 10

Source: https://oeis.org/A071071 (J. Shallit, "The Prime Game", Recursivity, Dec 2006;
J.-P. Delahaye, Pour la Science, June 2002)
Credit: @Solfanbtc

The minimal set of a set `L` of numbers (Shallit) is the set of elements `x ∈ L` such that no
other element of `L` can be obtained from `x` by striking out digits, i.e. no other `y ∈ L` has
its decimal digit string as a (not necessarily contiguous) subsequence of that of `x`. Every
element of `L` then contains some minimal element as a subsequence of its digits. For
`L = {2^k : k ≥ 0}` the known minimal elements are 1, 2, 4, 8, 65536.

Conjecture (J. Shallit): this list is complete, i.e. the minimal set of the powers of 2 is exactly
`{1, 2, 4, 8, 65536}`. (Equivalently, given that these five are minimal: every power of 2 has a
decimal digit 1, 2, 4 or 8, or contains 6, 5, 5, 3, 6 as a subsequence of its digits.)

Encoding: `Nat.digits 10` lists the digits least significant first; reversing both lists does not
change the sublist (subsequence) relation, so `List.Sublist` on `Nat.digits 10` is the subsequence
relation on decimal strings (as in upstream `FormalConjectures/Wikipedia/MinimalPrime.lean`).

Sanity check (python): every `2^k` with `k < 20000` contains 1, 2, 4, 8 or 65536 as a digit
subsequence (and in this range never 65536 as a subsequence without also as a substring), and no
power of 2 other than 65536 is a subsequence of 65536.
-/

namespace OMA.S_oeis_a071071

/-- The powers of 2. -/
def PowersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

/-- `y`'s decimal digits form a subsequence of `x`'s decimal digits. -/
def IsDigitSubseq (y x : ℕ) : Prop := (Nat.digits 10 y).Sublist (Nat.digits 10 x)

/-- The minimal set of `L`: elements of `L` containing no other element of `L` as a digit
subsequence. -/
def MinimalSet (L : Set ℕ) : Set ℕ := {x | x ∈ L ∧ ∀ y ∈ L, IsDigitSubseq y x → y = x}

/-- Shallit's conjecture: the minimal set of the powers of 2 in base 10 is `{1, 2, 4, 8, 65536}`. -/
theorem main : MinimalSet PowersOfTwo = {1, 2, 4, 8, 65536} := by
  sorry

end OMA.S_oeis_a071071
