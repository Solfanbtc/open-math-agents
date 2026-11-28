import Mathlib

/-!
# A074944: number of k ≤ n with gcd(n, k) = tau(k)

Source: https://oeis.org/A074944
Credit: @Solfanbtc

`a(n)` is the number of `k` with `1 ≤ k ≤ n` and `gcd(n, k) = τ(k)`, `τ` the number of divisors
(A000005): 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, ... (offset 1).

Conjecture (entry, formula section): `∑_{i=1..n} a(i)` "seems to be asymptotic to c*n*log(n) with
0.5 < c < 0.6". We state it as: there is a constant `c` with `0.5 < c < 0.6` such that
`∑_{i ≤ n} a(i) ~ c n log n`.

Status: the entry adds "The above conjecture seems to be wrong. See the graph in the Links
section." (Amiram Eldar, Mar 10 2026). Our python computation agrees: the ratio
`∑_{i ≤ n} a(i) / (n log n)` is about 0.80 at `n = 10^3`, 2.86 at `10^4`, 15.4 at `10^5` and
46.5 at `4·10^5`, so the statement is expected to be false (a target for a disproof).

Sanity check (python): the definition gives all 68 listed terms.
-/

namespace OMA.S_oeis_a074944

open Filter Asymptotics

/-- A074944. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun k => Nat.gcd n k = k.divisors.card)).card

/-- The (doubtful) conjecture: `∑_{i ≤ n} a(i) ~ c n log n` for some `c ∈ (0.5, 0.6)`. -/
theorem main : ∃ c : ℝ, 0.5 < c ∧ c < 0.6 ∧
    (fun n : ℕ => ((∑ i ∈ Finset.Icc 1 n, a i : ℕ) : ℝ)) ~[atTop]
      fun n : ℕ => c * n * Real.log n := by
  sorry

end OMA.S_oeis_a074944
