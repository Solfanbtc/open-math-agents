import Mathlib

/-!
# A068891: a(1) = 1; a(n) = smallest nontrivial n-th power with property that digits alternate in parity individually as well as in concatenation with previous terms.

Source: https://oeis.org/A068891
Credit: @Solfanbtc

`a(1) = 1`, and for `n ≥ 2`, `a(n)` is the smallest nontrivial `n`-th power `j^n` (`j ≥ 2`) such
that the decimal digits of the concatenation `a(1) a(2) ⋯ a(n)` alternate in parity (which
includes the digits of each term individually). Data: `1, 4, 125, 81` (`1412581`).
The sequence stops as soon as no admissible `n`-th power exists.

Conjecture (in the entry): the sequence is finite.
Status: resolved. Sean A. Irvine (Mar 22 2024, in the entry): "Certainly finite because a(10)
does not exist (see A068890)", i.e. no 10th power has digits alternating in parity. It is stated
here faithfully all the same.

A python3 check: the greedy rule gives `a(2) = 4`, `a(3) = 125`, `a(4) = 81`, and no admissible
fifth power `j^5` with `j < 2·10^5`; no 10th power `j^10` with `j < 2·10^5` has alternating
digits.

Conventions: `build k = some [a(1), ..., a(k+1)]` while the terms exist, `none` afterwards;
"finite" means `build k = none` for some `k`. Digits are read most significant first
(`(Nat.digits 10 x).reverse`), and parity alternation is `List.Chain'` of `x % 2 ≠ y % 2`.
-/

namespace OMA.S_oeis_a068891

/-- The decimal digits of the concatenation of the terms of `L`. -/
def concatDigits (L : List ℕ) : List ℕ := (L.map fun x => (Nat.digits 10 x).reverse).flatten

/-- The digits alternate in parity. -/
def Alternates (ds : List ℕ) : Prop := ds.Chain' fun x y => x % 2 ≠ y % 2

/-- The admissible values for the next term, an `n`-th power, after the terms `L`. -/
def admissible (L : List ℕ) (n : ℕ) : Set ℕ :=
  {m | ∃ j : ℕ, 2 ≤ j ∧ m = j ^ n ∧ Alternates (concatDigits (L ++ [m]))}

open Classical in
/-- `build k = some [a(1), ..., a(k+1)]`, or `none` once the sequence has stopped. -/
noncomputable def build : ℕ → Option (List ℕ)
  | 0 => some [1]
  | k + 1 => (build k).bind fun L =>
      if (admissible L (k + 2)).Nonempty then some (L ++ [sInf (admissible L (k + 2))])
      else none

/-- The conjecture (resolved, see the docstring): the sequence is finite. -/
theorem main : ∃ k : ℕ, build k = none := by
  sorry

end OMA.S_oeis_a068891
