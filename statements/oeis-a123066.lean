import Mathlib

/-!
# A123066: (Number of numbers <= n with an odd number of distinct prime factors) - (number of numbers <= n with an even number of distinct prime factors).

Source: https://oeis.org/A123066
Credit: @Solfanbtc

Conjecture (entry comment, Franklin T. Adams-Watters): the sequence changes sign infinitely
often. (Known sign changes: at n = 52 and at n = 7954, Harvey P. Dale.)

Definition. As in the Maple program of the entry: a(1) = 0 and
a(n) = a(n-1) + (1 if ω(n) is odd, -1 otherwise) for n ≥ 2, i.e.
a(n) = Sum_{k=2..n} (-1)^(ω(k)+1), with ω(k) = number of distinct prime factors. (The number 1
is not counted, matching a(1) = 0 and the data 0, 1, 2, 3, 4, 3, ...; `#eval`.)

"changes sign infinitely often": the sequence is positive for arbitrarily large n and negative
for arbitrarily large n.
-/

namespace OMA.S_oeis_a123066

/-- A123066(n). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 2 n, (-1 : ℤ) ^ (k.primeFactors.card + 1)

theorem main :
    (∀ N : ℕ, ∃ n > N, 0 < a n) ∧ (∀ N : ℕ, ∃ n > N, a n < 0) := by
  sorry

end OMA.S_oeis_a123066
