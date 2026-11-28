import Mathlib

/-!
# A060715: Number of primes between n and 2n exclusive.

Source: https://oeis.org/A060715
Credit: @Solfanbtc

Conjecture (Vladimir Shevelev, Jun 27 2013, OEIS A060715): for prime n, a(n) = A226859(n).

Definitions.
* A060715(n): the number of primes q with n < q < 2n.
* A226770 / A226859 (from their names): a proper divisor of m is a divisor d with 1 < d < m.
  Start with the proper divisors of n + 1; for every divisor d obtained, add the proper divisors
  of n + d; repeat until nothing new appears. `Reached n d` says that d is obtained, i.e. d lies in
  the least set containing the proper divisors of n + 1 and closed under d ↦ proper divisors of
  n + d. The sums of the process are n + 1 and the n + d for d obtained; A226859(n) is the number
  of distinct primes among them (e.g. A226859(n) = 1 when n + 1 is prime: the only sum is n + 1).
  Every obtained d satisfies d <= n (a proper divisor of n + d is at most (n + d)/2), so the sets
  are finite and `Set.ncard` counts them.
Checked numerically: these definitions reproduce the listed terms of A226770 and A226859, and the
conjecture holds for all primes below 1500.
-/

namespace OMA.S_oeis_a060715

/-- `d` is a proper divisor of `m`: `d ∣ m` and `1 < d < m`. -/
def IsProperDiv (d m : ℕ) : Prop := d ∣ m ∧ 1 < d ∧ d < m

/-- `d` is obtained in the process of A226770 started from `n`. -/
def Reached (n d : ℕ) : Prop :=
  ∀ S : Set ℕ, (∀ e, IsProperDiv e (n + 1) → e ∈ S) →
    (∀ c ∈ S, ∀ e, IsProperDiv e (n + c) → e ∈ S) → d ∈ S

/-- A226859(n): the number of primes among the sums n + 1 and n + d, d obtained. -/
noncomputable def A226859 (n : ℕ) : ℕ :=
  {q : ℕ | q.Prime ∧ (q = n + 1 ∨ ∃ d, Reached n d ∧ q = n + d)}.ncard

/-- A060715(n): the number of primes strictly between n and 2n. -/
noncomputable def A060715 (n : ℕ) : ℕ := {q : ℕ | q.Prime ∧ n < q ∧ q < 2 * n}.ncard

theorem main : ∀ p : ℕ, p.Prime → A060715 p = A226859 p := by
  sorry

end OMA.S_oeis_a060715
