import Mathlib

/-!
# A073602: a(n) is the smallest prime different from a(k) for k < n such that sum(a(j), j=1..n) is a multiple of the n-th prime.

Source: https://oeis.org/A073602
Credit: @Solfanbtc

Conjecture (OEIS A073602): every prime belongs to this sequence.
(Zak Seidov, Jun 12 2015: among the first 10^6 terms the first missing primes are 5, 13, 41, ...;
the conjecture is the statement of the entry.)

Definition (offset 1): a(n) is the least prime p, different from a(1), ..., a(n-1), such that
prime(n) divides a(1) + ... + a(n-1) + p (such p exist by Dirichlet's theorem). `main` quantifies
over every sequence satisfying this specification (exactly one does); `a 0` is unconstrained and
unused. prime(n) = `Nat.nth Nat.Prime (n - 1)`.
Checked numerically: the specification reproduces all 53 listed terms 2, 7, 11, 29, 17, 103, ...
-/

namespace OMA.S_oeis_a073602

/-- The defining specification of A073602. -/
def Spec (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    IsLeast {p : ℕ | p.Prime ∧ (∀ k, 1 ≤ k → k < n → p ≠ a k) ∧
      Nat.nth Nat.Prime (n - 1) ∣ (∑ j ∈ Finset.Ico 1 n, a j) + p} (a n)

theorem main : ∀ a : ℕ → ℕ, Spec a → ∀ q : ℕ, q.Prime → ∃ n : ℕ, 1 ≤ n ∧ a n = q := by
  sorry

end OMA.S_oeis_a073602
