import Mathlib

/-!
# A073846: odd-indexed terms nonprime, even-indexed terms prime

Source: https://oeis.org/A073846
Credit: @Solfanbtc

`a(1) = 1`; thereafter every even-indexed term is prime and every odd-indexed term is composite,
each taken in increasing order: `a(2n-1) = A018252(n)` (the nonprimes 1, 4, 6, 8, 9, ...) and
`a(2n) = prime(n)`: 1, 2, 4, 3, 6, 5, 8, 7, 9, 11, ... This is a permutation of the positive
integers, so the orbit `n, a(n), a(a(n)), ...` of each `n ≥ 1` is either a finite cycle or
contains infinitely many distinct values.

Conjectures recorded in the entry (stated as a conjunction):
1. (Chayim Lowen, Aug 12 2015) the orbits of 34, 42, 50, 60, 74, 82, 86, 88 and 98 are infinite,
   i.e. not periodic ("I conjecture that the latter is the case");
2. (Michel Marcus, Mar 07 2021) the integers that belong to a finite cycle are exactly
   1, 2, ..., 33, 35, 37, 39, 41, 43, 47, 53, 62, 84, 87, 92, 121, 127, 132, 135, 181, 199, 205,
   317 (52 numbers).
(2 implies 1, as none of Lowen's numbers is in Marcus's list.)

`n` belongs to a finite cycle iff `a^[m] n = n` for some `m ≥ 1`.

Sanity check (python): the definition gives all 69 listed terms; among `n ≤ 1000`, exactly
Marcus's 52 numbers return to themselves before the orbit exceeds `10^6`, with cycle lengths
as reported by Lowen (`1, 2, 9`: 1; `3`: 2; `14`: 3; `92`: 6; `18`: 22); Lowen's nine orbits do not.
-/

namespace OMA.S_oeis_a073846

/-- A073846 (indexed from 1; the value at 0 is unused). -/
noncomputable def a (n : ℕ) : ℕ :=
  if n % 2 = 0 then Nat.nth Nat.Prime (n / 2 - 1)
  else Nat.nth (fun m => 0 < m ∧ ¬ m.Prime) ((n + 1) / 2 - 1)

/-- `n` lies on a finite cycle of `a`. -/
def IsPeriodic (n : ℕ) : Prop := ∃ m : ℕ, 1 ≤ m ∧ a^[m] n = n

/-- Marcus's list of the integers on finite cycles. -/
def cycleList : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
   26, 27, 28, 29, 30, 31, 32, 33, 35, 37, 39, 41, 43, 47, 53, 62, 84, 87, 92, 121, 127, 132,
   135, 181, 199, 205, 317}

/-- Lowen's and Marcus's conjectures. -/
theorem main :
    (∀ n ∈ ({34, 42, 50, 60, 74, 82, 86, 88, 98} : Finset ℕ), ¬ IsPeriodic n) ∧
    {n : ℕ | 1 ≤ n ∧ IsPeriodic n} = (cycleList : Set ℕ) := by
  sorry

end OMA.S_oeis_a073846
