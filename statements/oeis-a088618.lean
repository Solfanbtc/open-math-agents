import Mathlib

/-!
# A088618: Rearrangement of odd numbers such that every concatenation of at least two terms is composite

Source: https://oeis.org/A088618
Credit: @Solfanbtc

The concatenations meant are those of at least two consecutive terms (the example: `15, 513, 133,
315, 1513, 5133, 13315, 15133, …` are all composite). The sequence is built greedily: `a(1) = 1`,
and each next term is the smallest odd number not used before such that every concatenation
`a(i) ‖ a(i+1) ‖ ⋯ ‖ a(n)`, `i < n`, ending with the new term is composite:
`1, 5, 13, 3, 15, 9, 17, 7, 23, …` (this greedy rule reproduces all 66 data terms). Below
`terms k = [a(1), …, a(k+1)]`.

Conjecture (OEIS comment): the sequence is infinite, and every odd number is a member. Both are
stated: at every stage an admissible next term exists, and every odd `m` occurs.
-/

namespace OMA.S_oeis_a088618

/-- Decimal concatenation `x ‖ m`. -/
def concat (x m : ℕ) : ℕ := x * 10 ^ (Nat.digits 10 m).length + m

/-- The concatenation of the elements of a list, in order. -/
def concatList (l : List ℕ) : ℕ := l.foldl concat 0

/-- `m` can follow the terms `l`: odd, unused, and every concatenation of a (nonempty) final block
of `l` followed by `m` is composite. -/
def Admissible (l : List ℕ) (m : ℕ) : Prop :=
  Odd m ∧ m ∉ l ∧ ∀ i < l.length, 1 < concat (concatList (l.drop i)) m ∧
    ¬ (concat (concatList (l.drop i)) m).Prime

/-- The greedy next term. -/
noncomputable def next (l : List ℕ) : ℕ := sInf {m : ℕ | Admissible l m}

/-- `terms k = [a(1), …, a(k+1)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => terms k ++ [next (terms k)]

/-- A088618 is infinite and contains every odd number. -/
theorem main : (∀ k : ℕ, ∃ m : ℕ, Admissible (terms k) m) ∧
    (∀ m : ℕ, Odd m → ∃ k : ℕ, m ∈ terms k) := by
  sorry

end OMA.S_oeis_a088618
