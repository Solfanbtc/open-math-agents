import Mathlib

/-!
# A060254: Primes which are the sum of two consecutive composite numbers.

Source: https://oeis.org/A060254
Credit: @Solfanbtc

Conjecture (Charles R Greathouse IV, OEIS A060254, comment, Apr 29 2015): a(n) ~ n log n.

Conventions:
* A term is a prime p = c + (c + 1) with c and c + 1 both composite (an integer > 1 that is
  not prime), i.e. p odd with (p-1)/2 and (p+1)/2 composite: 17, 19, 29, 31, 41, ...
* a(n) (offset 1) is the n-th term, `Nat.nth IsTerm (n - 1)`; "a(n) ~ n log n" means
  a(n) / (n log n) → 1 in ℝ. (If there were only finitely many terms the ratio would tend to 0,
  so the statement includes that the sequence is infinite.)
* Checked in Python: the definition reproduces %S; for terms below 4·10^6 the ratio
  a(n)/(n log n) is 1.44, 1.34, 1.27, 1.26 at n = 10^3, 10^4, 10^5, 255192, decreasing slowly
  as for the primes themselves.
-/

namespace OMA.S_oeis_a060254

open Filter Topology

/-- `c` is composite. -/
def IsComposite (c : ℕ) : Prop := 1 < c ∧ ¬ c.Prime

/-- `p` is a prime that is the sum of two consecutive composite numbers. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ ∃ c, IsComposite c ∧ IsComposite (c + 1) ∧ p = c + (c + 1)

/-- A060254: the `n`-th such prime (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Greathouse's conjecture: `a(n) ~ n log n`. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a060254
