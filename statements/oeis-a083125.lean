import Mathlib

/-!
# A083125: successive products are palindromes

Source: https://oeis.org/A083125
Credit: @Solfanbtc

`a(1) = 1`; then `a(n)` is the smallest positive integer not occurring earlier such that
`a(n-1) · a(n)` is a palindrome (in decimal): 1, 2, 3, 11, 4, 22, 28, 9, 19, 17, 16, ...
(No multiple of 10 can occur, since a product ending in 0 is not a palindrome.)

Conjecture (Reinhard Zumkeller, May 02 2003): except for multiples of 10, all natural numbers
belong to this sequence, i.e. every positive integer not divisible by 10 is some `a(n)`.

Encoding: `terms n` is the list `[a(1), ..., a(n)]`; each new term is the `sInf` of the set of
admissible candidates (the set is nonempty, as every number not divisible by 10 has infinitely
many palindromic multiples; in any case `sInf ∅ = 0` would only make the claim harder).

Sanity check (python): the definition reproduces all 45 listed terms; after 3000 terms every
non-multiple of 10 below 300 has appeared except 81, 162, 237, 243.
-/

namespace OMA.S_oeis_a083125

/-- `x` is a palindrome in base 10. -/
def IsPal (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

/-- The first `n` terms `[a(1), ..., a(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let l := terms (n + 1)
    l ++ [sInf {m | 0 < m ∧ m ∉ l ∧ IsPal (l.getLastD 1 * m)}]

/-- A083125, `a(n)` for `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getLastD 0

/-- Zumkeller's conjecture. -/
theorem main : ∀ m : ℕ, 0 < m → ¬ 10 ∣ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a083125
