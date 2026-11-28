import Mathlib

/-!
# A108763: every number of prime factors occurs among p + 2 (p ≢ 7 mod 8) and p - 6 (p ≡ 7 mod 8)

Source: https://oeis.org/A108763
For `n ≥ 2` (offset 2) with `p = prime(n)`: if `p = 8m+1` then `a(n) = 8m+3`, if `p = 8m+3` then
`a(n) = 8m+5`, if `p = 8m+5` then `a(n) = 8m+7`, and if `p = 8m+7` then `a(n) = 8m+1`; that is,
`a(n) = p + 2` unless `p ≡ 7 (mod 8)`, when `a(n) = p - 6` (formula section). Data: 5, 7, 1, 13, ...
Conjecture of the entry: "for any whole number k, there exists at least one a(n) with exactly k
prime factors (for k = 3, for instance, 8*20 + 3 = 163 which is prime and the sequence includes
8*20 + 5 = 3 x 5 x 11)."

We state: for every `k ≥ 0` there is `n ≥ 2` with `Ω(a(n)) = k`.
Conventions. "Exactly k prime factors" is read as counted with multiplicity (`Ω`,
`ArithmeticFunction.cardFactors`; the example `3*5*11` has 3 under either reading). "Whole
number" includes `k = 0`, which holds with `a(4) = 1` (`prime(4) = 7`). The other remarks in the
comment (asymptotics, gaps, a conditional statement) are not conjectures and are not stated.
Indexing: `prime n` here is `Nat.nth Nat.Prime (n - 1)`, so `prime 1 = 2`.
Checked with python3: the definition reproduces the 59 listed terms, and for each
`k = 0, ..., 15` some `a(n)` with `prime(n) < 3·10^7` has `Ω(a(n)) = k`
(least values 1, 5, 15, 45, 315, 243, 1215, 3645, 15309, 19683, 255879, ...).

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a108763

/-- A108763 (`n ≥ 2`). -/
noncomputable def a (n : ℕ) : ℕ :=
  let p := Nat.nth Nat.Prime (n - 1)
  if p % 8 = 7 then p - 6 else p + 2

theorem main : ∀ k : ℕ, ∃ n : ℕ, 2 ≤ n ∧ ArithmeticFunction.cardFactors (a n) = k := by
  sorry

end OMA.S_oeis_a108763
