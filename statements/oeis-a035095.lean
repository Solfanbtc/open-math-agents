import Mathlib

/-!
# A035095: Smallest prime congruent to 1 (mod prime(n)).

Source: https://oeis.org/A035095
Credit: @Solfanbtc

The entry records two conjectures about a(n), the smallest prime congruent to 1 modulo the
n-th prime p = prime(n):

1. (Long-standing conjecture, Wagstaff 1979, recorded by Franklin T. Adams-Watters, Jun 18 2010)
   a(n) <= prime(n)^2 + 1.
2. (Thomas Ordowski, Aug 06 2017) a(n) is the smallest prime q such that gpf(q - 1) = prime(n),
   where gpf is the greatest prime factor (A006530).

The entry notes that 1 implies 2; `main` states their conjunction, quantifying over the primes
p directly (n ↦ prime(n) is a bijection from the indices n >= 1 onto the primes).

Conventions: `leastPrimeOneMod p` is the infimum of the primes q ≡ 1 (mod p), which exist by
Dirichlet's theorem; `IsGpf p m` says that p is the greatest prime factor of m.
Conjecture 2 is stated literally as an equality of the two least elements (`sInf`).
Checked numerically for all primes p < 3000.
-/

namespace OMA.S_oeis_a035095

/-- The smallest prime congruent to 1 modulo `p` (a(n) for `p = prime(n)`). -/
noncomputable def leastPrimeOneMod (p : ℕ) : ℕ :=
  sInf {q : ℕ | q.Prime ∧ q ≡ 1 [MOD p]}

/-- `p` is the greatest prime factor of `m`. -/
def IsGpf (p m : ℕ) : Prop :=
  p.Prime ∧ p ∣ m ∧ ∀ s : ℕ, s.Prime → s ∣ m → s ≤ p

theorem main :
    (∀ p : ℕ, p.Prime → leastPrimeOneMod p ≤ p ^ 2 + 1) ∧
    (∀ p : ℕ, p.Prime →
      leastPrimeOneMod p = sInf {q : ℕ | q.Prime ∧ IsGpf p (q - 1)}) := by
  sorry

end OMA.S_oeis_a035095
