import Mathlib

/-!
# A088093: Beginning with 2, smallest palindrome >= the previous term such that every concatenation is a prime.

Source: https://oeis.org/A088093
Credit: @Solfanbtc

`a(1) = 2`, and `a(n+1)` is the least (decimal) palindrome `p ≥ a(n)` such that the decimal
concatenation `a(1) a(2) … a(n) p` is prime. (So every concatenation `a(1) … a(m)` is prime.)
This reproduces all 35 terms of %S, %T, %U (Python).

We track the state `(a(n), C(n))`, with `C(n)` the concatenation `a(1) … a(n)` as a number.
`next` picks the least admissible `p` (meaningful only when one exists), so
`a(n) = (step^[n-1] (2, 2)).1`.

Conjectures (Amarnath Murthy, in the entry):
1. The sequence is infinite: at every stage an admissible palindrome exists.
2. Two successive terms are not equal for `n > 5`: `a(n) ≠ a(n+1)` for all `n > 5`.
-/

namespace OMA.S_oeis_a088093

/-- `n` is a positive decimal palindrome. -/
def IsPal (n : ℕ) : Prop := 0 < n ∧ (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- Decimal concatenation of `c` and `p`. -/
def conc (c p : ℕ) : ℕ := c * 10 ^ (Nat.digits 10 p).length + p

/-- Admissible next terms from the state `(last term, concatenation so far)`. -/
def Adm (st : ℕ × ℕ) : Set ℕ := {p : ℕ | IsPal p ∧ st.1 ≤ p ∧ (conc st.2 p).Prime}

/-- One step of the construction. -/
noncomputable def step (st : ℕ × ℕ) : ℕ × ℕ := (sInf (Adm st), conc st.2 (sInf (Adm st)))

/-- `a(n)`, `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ := (step^[n - 1] (2, 2)).1

theorem main : (∀ n : ℕ, (Adm (step^[n] (2, 2))).Nonempty) ∧
    (∀ n : ℕ, 5 < n → a n ≠ a (n + 1)) := by
  sorry

end OMA.S_oeis_a088093
