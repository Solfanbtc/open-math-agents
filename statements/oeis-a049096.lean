import Mathlib

/-!
# A049096: the numbers k with 2^k + 1 not squarefree have a(n)/n → C with 4 < C < 9/2

Source: https://oeis.org/A049096
Credit: @Solfanbtc

A049096 (offset 1): the numbers `k` such that `2^k + 1` is divisible by a square `> 1`.
Data 3, 9, 10, 15, 21, 27, 30, 33, 39, 45, 50, …

Conjecture (B. Cloitre, Aug 20 2002): "lim n -> infinity a(n)/n = C exists and 4 < C < 9/2."
(The second part of that comment, about the primes `p` with `p^2` never dividing `2^x + 1`, is
the sequence A072936 and is not stated here.) `main` states: there is `C` with `4 < C < 9/2`
such that `a(n)/n → C`.

Definitions. `a(n)` is the `n`-th (from 1) positive `k` with `2^k + 1` not squarefree
(`Nat.nth`, which is `0` if there are fewer than `n` such `k`; the sequence is infinite, since
every odd multiple of 3 is a term). Checked with python3 (terms below `3·10^5` via R. Israel's
characterization in the entry: `gcd(k, 2^k + 1) > 1`, or `k` an odd multiple of 182, from the
Wieferich prime 1093): the data match, and `a(n)/n` is 4.137, 4.139, 4.135 at
`n = 1000, 10000, 72548`.
-/

namespace OMA.S_oeis_a049096

/-- A049096: the `n`-th positive `k` with `2^k + 1` not squarefree. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => 1 ≤ k ∧ ¬ Squarefree (2 ^ k + 1)) (n - 1)

open Filter Topology in
/-- Cloitre's conjecture. -/
theorem main : ∃ C : ℝ, 4 < C ∧ C < 9 / 2 ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 C) := by
  sorry

end OMA.S_oeis_a049096
