import Mathlib

/-!
# A089758: Primes arising in A089757.

Source: https://oeis.org/A089758
Credit: @Solfanbtc

A089757 is greedy (C. Ronaldo's Maple program): each term `a(n)` is the least multiple of 3
greater than `a(n-1)` such that the decimal concatenation `a(n) a(n-1) ⋯ a(1) 1` is prime. A089758
lists these primes: 31, 631, 9631, 129631, 27129631, ... In `state n = (a(n), p(n))` the second
component is the `n`-th prime of A089758 (`p(0) = 1`, `a(0) = 0`). The next term is
prepended: `p(n+1) = a(n+1) · 10^(digits of p(n)) + p(n)`. Checked with python3: this
reproduces the 13 listed primes.

Conjecture (A. Murthy): the sequence is infinite, i.e. the greedy construction never gets
stuck: at every stage some admissible next term exists. `main` states this.
-/

namespace OMA.S_oeis_a089758

/-- Admissible next terms after the state `(last term, current concatenation)`. -/
def Candidates (s : ℕ × ℕ) : Set ℕ :=
  {x | s.1 < x ∧ 3 ∣ x ∧ (x * 10 ^ (Nat.digits 10 s.2).length + s.2).Prime}

/-- `state n = (a(n), n-th prime of A089758)`, starting from `(0, 1)`. -/
noncomputable def state : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 =>
    let s := state n
    let x := sInf (Candidates s)
    (x, x * 10 ^ (Nat.digits 10 s.2).length + s.2)

theorem main : ∀ n : ℕ, (Candidates (state n)).Nonempty := by
  sorry

end OMA.S_oeis_a089758
