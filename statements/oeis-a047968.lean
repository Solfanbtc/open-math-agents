import Mathlib

/-!
# A047968: a(n) = Sum_{d|n} p(d), where p(d) = A000041 = number of partitions of d.

Source: https://oeis.org/A047968
Credit: @Solfanbtc

Conjecture (Franklin T. Adams-Watters, Apr 19 2014, OEIS A047968): for n > 6, a(n) is strictly
increasing, i.e. a(n) < a(n+1) for every n > 6 (the sequence decreases at n = 4 -> 5, 8 -> 8,
and at n = 6 -> 7, 17 -> 16).

Here p(d) = `Fintype.card (Nat.Partition d)` and a(n) = Σ_{d ∣ n} p(d) over the positive
divisors of n (offset 1). Checked numerically: the listed terms are reproduced and
a(n) < a(n+1) holds for 6 < n < 3000 (the only failures below 3000 are n = 4 and n = 6).
-/

namespace OMA.S_oeis_a047968

/-- a(n) = Σ_{d ∣ n} p(d). -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors, Fintype.card (Nat.Partition d)

theorem main : ∀ n : ℕ, 6 < n → a n < a (n + 1) := by
  sorry

end OMA.S_oeis_a047968
