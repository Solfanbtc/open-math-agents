import Mathlib

/-!
# A070788: Positive integers n such that the Reverse and Add! trajectory of n (presumably) does not join the trajectory of any m < n.

Source: https://oeis.org/A070788
Credit: @Solfanbtc

Conjecture (OEIS A070788): the trajectories of the terms of this sequence do not join (checked to
1200 steps for any two terms, 10000 steps for pairs from 1, 3, 5, 7, 9, 100, 102, 106), i.e. each
listed n has a Reverse and Add! trajectory that does not join the trajectory of any m < n.

`main`: for 1 <= n <= 1037 (the listed range), n has this property iff n is one of the 53 listed
terms. The "if" direction is the conjecture; the "only if" direction says that every unlisted n
in the range does join a smaller trajectory (a finite check: within 40 steps numerically).

Conventions: R(x) = x + reverse(x), the reversal of the decimal digits; the trajectory of x is
x, R(x), R(R(x)), ... (including x itself); two trajectories join if they have a common element.
Checked numerically with 40-step trajectories: the n <= 1037 not joining any smaller trajectory are
exactly the listed terms.
-/

namespace OMA.S_oeis_a070788

/-- Reverse and Add!: `x + reverse(x)` in base 10. -/
def revAdd (x : ℕ) : ℕ := x + Nat.ofDigits 10 (Nat.digits 10 x).reverse

/-- The trajectories of `a` and `b` join. -/
def Joins (a b : ℕ) : Prop := ∃ i j : ℕ, revAdd^[i] a = revAdd^[j] b

/-- The listed terms. -/
def terms : Finset ℕ :=
  {1, 3, 5, 7, 9, 100, 102, 106, 108, 111, 112, 113, 114, 116, 117, 118, 119, 122, 124, 128, 133,
   135, 137, 138, 166, 184, 186, 196, 199, 359, 399, 459, 539, 659, 679, 739, 759, 779, 799, 859,
   879, 919, 939, 959, 979, 999, 1000, 1006, 1011, 1013, 1022, 1033, 1037}

theorem main : ∀ n : ℕ, 1 ≤ n → n ≤ 1037 →
    ((∀ m : ℕ, 1 ≤ m → m < n → ¬ Joins n m) ↔ n ∈ terms) := by
  sorry

end OMA.S_oeis_a070788
