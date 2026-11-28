import Mathlib

/-!
# A092878: Number of initial odd numbers in class n of the iterated phi function.

Source: https://oeis.org/A092878
Credit: @Solfanbtc

Conjecture (recorded in A092878, after Shapiro; R. K. Guy, Unsolved Problems in Number
Theory, B41): the smallest number in class `n` is always odd.

Class `n`, for `n > 0`, contains all numbers `k` such that `n` iterations of the Euler `φ`
function applied to `k` yield `2`; class `0` contains only `1` and `2`.

Formalization.
* Class `n ≥ 1` is `{k | φ^[n] k = 2}`. Since `φ 2 = φ 1 = 1` and `φ 0 = 0`, an orbit that hits
  `2` never returns to it, so these classes are disjoint, as in the source (e.g. class 2 begins
  `5, 7, 8, 9, 10, 12, 14, 18`).
* Class `n ≥ 1` is nonempty (`φ^[n] (2^(n+1)) = 2`), so it has a least element, and the
  conjecture is that this least element is odd. Class `0 = {1, 2}` has least element `1`,
  odd, so it is left out; the formula `{k | φ^[0] k = 2} = {2}` does not describe class 0.

Checked with python3: the least elements of classes `1..20` are
`3, 5, 11, 17, 41, 83, 137, 257, 641, ..., 1114129`, all odd (Shapiro: class `n` lies in
`[2^n, 2^(n+1)]`, so a search up to `2^21` is exhaustive for these classes).
-/

namespace OMA.S_oeis_a092878

/-- Class `n` (`n ≥ 1`) of the iterated totient: the `k` with `φ^[n] k = 2`. -/
def phiClass (n : ℕ) : Set ℕ := {k : ℕ | Nat.totient^[n] k = 2}

/-- The smallest number in every class `n ≥ 1` is odd. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, IsLeast (phiClass n) m ∧ Odd m := by
  sorry

end OMA.S_oeis_a092878
