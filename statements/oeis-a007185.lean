import Mathlib

/-!
# A007185: Automorphic numbers ending in digit 5: a(n) = 5^(2^n) mod 10^n.

Source: https://oeis.org/A007185
Credit: @Solfanbtc

Conjecture (Eric M. Schmidt, Aug 01 2012, in the entry): For any m coprime to 10 and for any k,
the density of n such that a(n) == k (mod m) is 1/m.

Conventions.
* a(n) = 5^(2^n) mod 10^n for n ≥ 1 (the data start 5, 25, 625, 625, 90625, ... at n = 1).
* "Density" is natural (asymptotic) density over the indices n ≥ 1:
  #{1 ≤ n ≤ N : a(n) ≡ k (mod m)} / N → 1/m as N → ∞.
* m ranges over positive integers coprime to 10 and k over all integers (only k mod m matters).
* Checked with python3 (via the entry's recursion a(n+1) = a(n)^2 mod 10^(n+1)): the listed
  terms, and residue frequencies for m = 3, 7, 9, 11 over n ≤ 3000 are all within about 15% of
  1/m.
-/

namespace OMA.S_oeis_a007185

open Filter Topology

/-- A007185: `a n = 5^(2^n) mod 10^n`. -/
def a (n : ℕ) : ℕ := 5 ^ (2 ^ n) % 10 ^ n

theorem main : ∀ m : ℕ, 0 < m → Nat.Coprime m 10 → ∀ k : ℤ,
    Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter fun n => (a n : ℤ) ≡ k [ZMOD m]).card : ℝ) / N)
      atTop (𝓝 (1 / (m : ℝ))) := by
  sorry

end OMA.S_oeis_a007185
