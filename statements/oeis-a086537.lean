import Mathlib

/-!
# A086537: Beginning with 1, the smallest number not yet seen such that every partial sum has a distinct prime signature.

Source: https://oeis.org/A086537
Credit: @Solfanbtc

The prime signature of `m ≥ 1` is the multiset of the exponents in its prime factorization
(`1` has the empty signature). Offset 1: `a(1) = 1` and `a(n)` is the smallest positive
integer, not among `a(1), ..., a(n-1)`, such that the partial sum `a(1) + ... + a(n)` has a
prime signature different from those of all earlier partial sums `a(1) + ... + a(k)`, `k < n`
(this is the definition as corrected by Robert Israel, matching his Maple program).
We checked by computer that this rule reproduces all 63 terms of %S, %T, %U.

Conjecture (Amarnath Murthy, 2003): this is a rearrangement of the positive integers, i.e.
every positive integer is a term.
-/

namespace OMA.S_oeis_a086537

/-- The prime signature of `m`: the multiset of exponents of its prime factorization. -/
noncomputable def sig (m : ℕ) : Multiset ℕ := m.primeFactors.val.map fun p => m.factorization p

/-- The signatures of the partial sums of the list `l`. -/
noncomputable def partialSigs (l : List ℕ) : List (Multiset ℕ) :=
  (List.range l.length).map fun i => sig (l.take (i + 1)).sum

/-- The next term after the terms `l`. -/
noncomputable def next (l : List ℕ) : ℕ :=
  sInf {x : ℕ | 0 < x ∧ x ∉ l ∧ sig (l.sum + x) ∉ partialSigs l}

/-- `terms n = [a(1), ..., a(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | n + 1 => terms n ++ [next (terms n)]

/-- `a(n)`, offset 1. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

/-- Every positive integer is a term of A086537. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a086537
