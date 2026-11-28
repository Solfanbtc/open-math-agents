import Mathlib

/-!
# A098348: Triangular array read by rows: T(n, k) = number of ordered factorizations of a "hook-type" number with n total prime factors and k distinct prime factors. "Hook-type" means that only one prime can have multiplicity > 1.

Source: https://oeis.org/A098348
Credit: @Solfanbtc

Conjecture (Peter Bala, Apr 20 2012): "The following conjectural formula for the triangle
entries agrees with the values listed above: T(n,k) = Sum_{j=0..n-k} 2^(n-k-j)*binomial(n-k,j)*
a(k,j), where a(k,j) = 2^j*Sum_{i=j+1..k} binomial(i,j+1)*(i-1)!*Stirling2(k,i)."
(Later formulas by Ridouane Oudra, 2026, are also given in the entry, without proof.)

Definitions.
* An ordered factorization of `m` is a list of integers `≥ 2` with product `m`; `H m` counts
  them (A074206; `H 1 = 1`, the empty list).
* A hook-type number with `n` prime factors counted with multiplicity and `k` distinct ones
  (`1 ≤ k ≤ n`) has prime signature `(n - k + 1, 1, ..., 1)`; the number of ordered
  factorizations depends only on the signature, and we use the representative
  `2^(n-k+1) * 3 * 5 * ... * p_k` (the product of the 2nd, ..., k-th primes), as in
  David Wasserman's formula T(n,k) = A074206(2^(n+1-k)*A070826(k)).
* Range: `1 ≤ k ≤ n` (offset 1, triangle). python3 (ordered factorizations computed by prime
  signature) reproduces the 45 data terms and confirms the conjectured formula for n ≤ 12;
  the right-hand side is evaluated on the data with `#eval`.
-/

namespace OMA.S_oeis_a098348

/-- Number of ordered factorizations of `m` (A074206). -/
noncomputable def H (m : ℕ) : ℕ := {l : List ℕ | (∀ x ∈ l, 2 ≤ x) ∧ l.prod = m}.ncard

/-- T(n, k): ordered factorizations of `2^(n-k+1) * p_2 * ... * p_k`. -/
noncomputable def T (n k : ℕ) : ℕ :=
  H (2 ^ (n - k + 1) * ∏ i ∈ Finset.Ico 1 k, Nat.nth Nat.Prime i)

/-- Bala's a(k, j). -/
def A (k j : ℕ) : ℕ :=
  2 ^ j * ∑ i ∈ Finset.Icc (j + 1) k, i.choose (j + 1) * (i - 1).factorial * Nat.stirlingSecond k i

/-- The conjectured closed form. -/
def F (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n - k + 1), 2 ^ (n - k - j) * (n - k).choose j * A k j

theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n → T n k = F n k := by
  sorry

end OMA.S_oeis_a098348
