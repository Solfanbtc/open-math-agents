import Mathlib

/-!
# A083762: concatenations of the first terms, followed by 1, are prime

Source: https://oeis.org/A083762
Credit: @Solfanbtc

Rearrangement of the natural numbers such that the concatenation of the terms, beginning with the
first one, with a `1` appended as least significant digit, is a prime: `11, 131, 1321, 13241, …`
are primes. Constructed greedily: `a(1) = 1` (`11` is prime), and each next term is the smallest
positive integer not yet used such that `a(1) ‖ a(2) ‖ ⋯ ‖ a(n) ‖ 1` is prime: `1, 3, 2, 4, 9, 5, 13,
20, …` (this rule reproduces the first 60 data terms). Below `terms k = [a(1), …, a(k+1)]`.

Conjecture (OEIS comment): every natural number belongs to this sequence (so that it is indeed a
rearrangement of the positive integers).
-/

namespace OMA.S_oeis_a083762

/-- Decimal concatenation `x ‖ m`. -/
def concat (x m : ℕ) : ℕ := x * 10 ^ (Nat.digits 10 m).length + m

/-- The concatenation of the elements of a list, in order. -/
def concatList (l : List ℕ) : ℕ := l.foldl concat 0

/-- The greedy next term after the terms `l`. -/
noncomputable def next (l : List ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ m ∉ l ∧ (concat (concat (concatList l) m) 1).Prime}

/-- `terms k = [a(1), …, a(k+1)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => terms k ++ [next (terms k)]

/-- Every positive integer occurs in A083762. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∃ k : ℕ, m ∈ terms k := by
  sorry

end OMA.S_oeis_a083762
