import Mathlib

/-!
# A036845: a(n) = min_k T(n,k), T(n,k) the "phi/sigma tug-of-war sequence with seed n".

Source: https://oeis.org/A036845
Credit: @Solfanbtc

Conjectures (OEIS A036845, comments):
1. The sequence {T(n,k)} is eventually periodic for every n, so a(n) can be computed in finite
   time.
2. a(n) -> infinity as n -> infinity.

Conventions:
* T(n,1) = phi(n), and for k ≥ 2, T(n,k) = phi(T(n,k-1)) if k is odd and sigma(T(n,k-1)) if
  k is even (the name), with Euler's totient `Nat.totient` and sigma = `σ 1`. Example: T(5,k)
  is 4, 7, 6, 12, 4, 7, 6, 12, ...
* a(n) = min_{k ≥ 1} T(n,k), offset 1; the minimum of a nonempty set of natural numbers always
  exists (`sInf`), whether or not conjecture 1 holds. Checked in Python (minimum over the first
  200 terms of each trajectory): all 75 listed terms of %S/%T/%U.
* "Eventually periodic for every n" is stated for every seed n ≥ 1: there are N ≥ 1 and a
  period p ≥ 1 with T(n, k + p) = T(n, k) for all k ≥ N.
* "a(n) -> infinity" is `Tendsto a atTop atTop`.
-/

namespace OMA.S_oeis_a036845

open Filter

/-- The phi/sigma tug-of-war sequence: `T n k` for `k ≥ 1` (`T n 0 = n` is the seed). -/
def T (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => if Even k then Nat.totient (T n k) else ArithmeticFunction.sigma 1 (T n k)

/-- A036845: `a(n) = min_{k ≥ 1} T(n,k)`. -/
noncomputable def a (n : ℕ) : ℕ := sInf (Set.range fun k : ℕ => T n (k + 1))

/-- The two conjectures of the entry. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ N p : ℕ, 1 ≤ N ∧ 1 ≤ p ∧ ∀ k : ℕ, N ≤ k → T n (k + p) = T n k) ∧
    Tendsto a atTop atTop := by
  sorry

end OMA.S_oeis_a036845
