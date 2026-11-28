import Mathlib

/-!
# A083760: Rearrangement of even numbers such that concatenation of terms beginning with the first with a 1 as the least significant digit is a prime.

Source: https://oeis.org/A083760
Credit: @Solfanbtc

The sequence is greedy: `a(n)` is the least positive even number, not among `a(1), …, a(n-1)`,
such that the decimal concatenation `a(1) a(2) ⋯ a(n)` followed by the digit 1 is prime. For
example 41, 421, 4261 are prime (2 is skipped at the start because 21 is composite).
`concat l` is the number whose decimal digits are those of the entries of `l`, in order, and
`firstTerms n = [a(1), …, a(n)]`. Checked with python3: this reproduces the 60 listed terms
4, 2, 6, 16, 18, 24, 14, 36, 12, 34, 134, ...

Conjecture (A. Murthy and M. Srikanth): every (positive) even number is a member. `main` states
this.
-/

namespace OMA.S_oeis_a083760

/-- Decimal concatenation of the entries of `l`. -/
def concat (l : List ℕ) : ℕ := l.foldl (fun acc x => acc * 10 ^ (Nat.digits 10 x).length + x) 0

/-- `firstTerms n = [a(1), …, a(n)]`. -/
noncomputable def firstTerms : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let l := firstTerms n
    l ++ [sInf {x : ℕ | 0 < x ∧ Even x ∧ x ∉ l ∧ (concat (l ++ [x]) * 10 + 1).Prime}]

/-- `a n`: the `n`-th term (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := (firstTerms n).getD (n - 1) 0

theorem main : ∀ m : ℕ, 0 < m → Even m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a083760
