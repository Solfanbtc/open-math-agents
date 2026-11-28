import Mathlib

/-!
# A000926: Euler's "numerus idoneus" (or "numeri idonei", or idoneal, or suitable, or convenient numbers).

Source: https://oeis.org/A000926
Credit: @Solfanbtc

Conjecture (A000926): the list of 65 idoneal numbers given there is complete. (Chowla showed
that the list is finite and Weinberger that there are at most two further terms; see Kani (2011),
Corollary 23 and Remark 24.)

Idoneality is expressed through Euler's equivalent criterion, the one used upstream in
`FormalConjectures/Wikipedia/IdonealCompleteness.lean`: a positive integer `n` is idoneal iff it
cannot be written as `ab + bc + ca` with `0 < a < b < c`. A python check confirms that the
positive integers up to 5000 with no such representation are exactly the 65 listed numbers.
The statement says the idoneal numbers are exactly these 65 (each listed number is idoneal is
the easy, checkable half; the content is that there are no others). It is the same claim as
`Idoneal.idoneal_numbers_completeness` upstream.
-/

namespace OMA.S_oeis_a000926

/-- Euler's criterion: `n > 0` is idoneal iff `n ≠ ab + bc + ca` for all `0 < a < b < c`. -/
def IsIdoneal (n : ℕ) : Prop :=
  0 < n ∧ ¬ ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c

/-- The 65 terms of A000926. -/
def known : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24, 25, 28,
   30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72, 78, 85, 88, 93, 102, 105,
   112, 120, 130, 133, 165, 168, 177, 190, 210, 232, 240, 253, 273, 280, 312,
   330, 345, 357, 385, 408, 462, 520, 760, 840, 1320, 1365, 1848}

theorem main : ∀ n : ℕ, IsIdoneal n ↔ n ∈ known := by
  sorry

end OMA.S_oeis_a000926
