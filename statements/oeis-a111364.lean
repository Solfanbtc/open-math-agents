import Mathlib

/-!
# A111364: Index of first occurrence of n in A033093 (or 0 if not present).

Source: https://oeis.org/A111364
Credit: @Solfanbtc

Conjecture (Franklin T. Adams-Watters, OEIS A111364, %C line): the sequence contains no zeros;
that is, A033093 is onto the nonnegative integers.

Definitions.
* A033093 (offset 1): `z(n)` is the number of `0` digits of `n` written in base `b`, summed over
  `2 ≤ b ≤ n + 1`.
* A111364(m) is the least `n ≥ 1` with `z(n) = m`, or `0` if there is none; "no zeros" means that
  every `m ≥ 0` is a value `z(n)`, `n ≥ 1`.

Formalization. The statement is the surjectivity of `z` on `n ≥ 1`. (The other remarks of the
comment, about the divisibility of the values and `a(7)` being the last odd value, are
observations, not part of this statement.)

Checked with python3: the least `n` with `z(n) = m` reproduces all listed %S/%T/%U terms of
A111364 (`m ≤ 53`).
-/

namespace OMA.S_oeis_a111364

/-- A033093: the total number of zero digits of `n` in the bases `2, ..., n + 1`. -/
def z (n : ℕ) : ℕ :=
  ∑ b ∈ Finset.Icc 2 (n + 1), ((Nat.digits b n).filter (· = 0)).length

/-- A033093 takes every nonnegative integer value. -/
theorem main : ∀ m : ℕ, ∃ n : ℕ, 1 ≤ n ∧ z n = m := by
  sorry

end OMA.S_oeis_a111364
