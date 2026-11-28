import Mathlib

/-!
# A035363: Number of partitions of n into even parts.

Source: https://oeis.org/A035363
Credit: @Solfanbtc

Empirical formula (Simon Plouffe, Sep 15 2025, OEIS A035363):
  Sum_{n>=0} a(n) / exp(n Pi) = exp(-Pi/12) sqrt(2) Gamma(3/4) / Pi^(1/4)  (= A388406).
Status: the entry adds (Peter Bala, Jun 09 2026) that this conjecture follows easily from the
known value eta(i) = Gamma(1/4) / (2 Pi^(3/4)) of the Dedekind eta function, so it is a known
result; it is stated here faithfully.

a(n) is the number of partitions of n all of whose parts are even (`Nat.Partition n`, offset 0).
The series has nonnegative terms and converges (a(n) <= p(n), which grows subexponentially), so
the sum is stated with `HasSum`. Checked numerically: both sides are 1.0018744370146...
-/

namespace OMA.S_oeis_a035363

/-- Number of partitions of `n` into even parts. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Nat.Partition n => ∀ i ∈ p.parts, Even i).card

theorem main :
    HasSum (fun n : ℕ => (a n : ℝ) / Real.exp (n * Real.pi))
      (Real.exp (-Real.pi / 12) * Real.sqrt 2 * Real.Gamma (3 / 4) / Real.pi ^ (1 / 4 : ℝ)) := by
  sorry

end OMA.S_oeis_a035363
