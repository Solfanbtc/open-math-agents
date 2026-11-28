import Mathlib

/-!
# A030052: Smallest number whose n-th power is a sum of distinct smaller positive n-th powers.

Source: https://oeis.org/A030052
Credit: @Solfanbtc

Conjecture (OEIS A030052, formula section, M. F. Hasler, May 25 2020):
a(n) >= A332101(n) = A078607(n)+2 (conjectured).

Here
* A030052(n) is the least s such that s^n is a sum of distinct n-th powers of positive
  integers smaller than s;
* A332101(n) is the least m such that m^n <= Sum_{0<k<m} k^n;
* A078607(n) is the least positive integer x such that 2*x^n > (x+1)^n.

The inequality a(n) >= A332101(n) is immediate (A332101 notes it is obviously a lower
bound), so the conjectured content is the equality A332101(n) = A078607(n) + 2, together
with the resulting bound a(n) >= A078607(n) + 2; both are stated. The bound on a(n) is
stated for every s whose n-th power is such a sum, which is the same as a bound on the
least such s.

Minimal fix of the range: A030052 has offset 1, but at n = 1 the claim fails
(A332101(1) = 3, A078607(1) + 2 = 4, and a(1) = 3 since 3 = 2 + 1). The statement is
therefore made for n >= 2, the range n > 1 used in A332101. Checked in Python: the equality
holds for 2 <= n < 200, and a(n) >= A078607(n) + 2 for every listed term (n = 2..17).

Note: A332101 itself records the equality as holding for almost all n > 1 and mentions
n = 777451915729368 as a possible exception (to it or to the formula
round(n/log 2) + 2); this statement follows the unrestricted claim made in A030052.
-/

namespace OMA.S_oeis_a030052

/-- `s ^ n` is a sum of distinct `n`-th powers of positive integers smaller than `s`. -/
def IsSumDistinctSmallerPowers (n s : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.Ico 1 s ∧ s ^ n = ∑ k ∈ S, k ^ n

/-- A332101(n): the least `m` with `m ^ n ≤ ∑_{0 < k < m} k ^ n`. -/
noncomputable def A332101 (n : ℕ) : ℕ :=
  sInf {m : ℕ | m ^ n ≤ ∑ k ∈ Finset.Ico 1 m, k ^ n}

/-- A078607(n): the least positive integer `x` with `2 * x ^ n > (x + 1) ^ n`. -/
noncomputable def A078607 (n : ℕ) : ℕ :=
  sInf {x : ℕ | 0 < x ∧ (x + 1) ^ n < 2 * x ^ n}

/-- Conjecture: for `n ≥ 2`, `A332101(n) = A078607(n) + 2`, and every `s` whose `n`-th power
is a sum of distinct smaller positive `n`-th powers satisfies `s ≥ A078607(n) + 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    A332101 n = A078607 n + 2 ∧
      ∀ s : ℕ, IsSumDistinctSmallerPowers n s → A078607 n + 2 ≤ s := by
  sorry

end OMA.S_oeis_a030052
