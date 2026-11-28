import Mathlib

/-!
# A058853: Primes p such that x^43 = 2 has a solution mod p.

Source: https://oeis.org/A058853
Credit: @Solfanbtc

Conjectures (Jianing Song, Mar 07 2021, in the entry); `main` is their conjunction:
1. this sequence has density 42/43 over all the primes;
2. in general, for a prime p and an integer a that is not a p-th power, the density of the
   prime factors of x^p - a (i.e. of the primes q such that x^p ≡ a (mod q) has a solution)
   over all the primes is 1 - 1/p ("well-known to be correct for p = 2").
(2 implies 1, as 2 is not a 43rd power; both are stated as in the source. The entry's
consequence a(n) ~ 43/42 n log n and its reformulation via primes ≡ 1 mod p are not included.)

Conventions.
* "Density over all the primes" is the natural relative density:
  #{q ≤ N prime : q has the property} / #{q ≤ N prime} → δ as N → ∞.
* "x^p = a has a solution mod q": ∃ x : ZMod q, x^p = a. "a is not a p-th power": there is no
  integer b with b^p = a.
* Data remark: Song's table gives 97674723 terms among the first 10^8 primes
  (0.976747...; 42/43 = 0.976744...).
-/

namespace OMA.S_oeis_a058853

open scoped Classical in
/-- Relative density of the primes q with ∃ x, x^p ≡ a (mod q), counted up to N. -/
noncomputable def ratio (p : ℕ) (a : ℤ) (N : ℕ) : ℝ :=
  (((Finset.range (N + 1)).filter fun q => q.Prime ∧ ∃ x : ZMod q, x ^ p = (a : ZMod q)).card : ℝ) /
    ((Finset.range (N + 1)).filter Nat.Prime).card

theorem main :
    Filter.Tendsto (ratio 43 2) Filter.atTop (nhds (42 / 43)) ∧
    ∀ (p : ℕ) (a : ℤ), p.Prime → (¬ ∃ b : ℤ, b ^ p = a) →
      Filter.Tendsto (ratio p a) Filter.atTop (nhds (1 - 1 / (p : ℝ))) := by
  sorry

end OMA.S_oeis_a058853
