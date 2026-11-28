import Mathlib

/-!
# A072532: a(0)=1; for n>0, a(n) = smallest prime of the form k*a(n-1)-1 with k>1.

Source: https://oeis.org/A072532
Credit: @Solfanbtc

Conjecture (OEIS A072532): if a(n) = k a(n-1) - 1 then k < a(n-1).

Minimal fix: the claim fails for the first two terms: a(1) = 2 = 3 * a(0) - 1 with k = 3 > a(0) = 1,
and a(2) = 3 = 2 * a(1) - 1 with k = 2 = a(1). It is stated for n >= 3 (it holds for 3 <= n < 80
numerically; the largest k seen there is 964).

Definition: a(0) = 1 and, for n > 0, a(n) is the least prime of the form k a(n-1) - 1 with k > 1
(such primes exist by Dirichlet's theorem, as the entry notes). `main` quantifies over every
sequence satisfying this specification (exactly one does). Since a(n-1) > 0, the k with
a(n) = k a(n-1) - 1 is unique.
-/

namespace OMA.S_oeis_a072532

/-- The defining specification of A072532. -/
def Spec (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ ∀ n : ℕ, 1 ≤ n →
    IsLeast {p : ℕ | p.Prime ∧ ∃ k : ℕ, 1 < k ∧ p = k * a (n - 1) - 1} (a n)

theorem main : ∀ a : ℕ → ℕ, Spec a → ∀ n : ℕ, 3 ≤ n → ∀ k : ℕ,
    a n = k * a (n - 1) - 1 → k < a (n - 1) := by
  sorry

end OMA.S_oeis_a072532
