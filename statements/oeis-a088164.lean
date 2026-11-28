import Mathlib

/-!
# A088164: Wolstenholme primes: primes p such that binomial(2p-1,p-1) == 1 (mod p^4).

Source: https://oeis.org/A088164
Credit: @Solfanbtc

Open claims recorded in the entry:
1. (Romeo Mestrovic, Congruences for Wolstenholme primes, 2012, Conjecture 2.10, via a comment
   of Felix Fröhlich, May 20 2015) p is a Wolstenholme prime if and only if
   S_(p-2)(p) ≡ 0 (mod p^3), where S_k(i) = 1^k + 2^k + ... + (i-1)^k.
2. (Stanislav Sykora, Aug 26 2014) among 1 < m ≤ 278000, binomial(2m,m) ≡ 2 (mod m^4) holds
   only when m is a Wolstenholme prime; "one might therefore wonder whether this is true in
   general".
3. (Felix Fröhlich, Feb 21 2018) whether every integer n with binomial(2n-1,n-1) ≡ 1 (mod n^4)
   is prime (a converse of Wolstenholme's theorem) "is an open problem".
`main` is the conjunction of 1, 2 and 3 (the questions 2 and 3 in their affirmative form).
Not restated: the infinitude of Wolstenholme primes and the Bernoulli/harmonic criteria are
upstream (FormalConjectures/Wikipedia/WolstenholmePrime.lean).

Conventions:
* `IsWolstenholme p`: p prime and binomial(2p-1, p-1) ≡ 1 (mod p^4). (Upstream also requires
  p > 7; no prime p ≤ 7 satisfies the congruence, so the two agree.)
* In 1, p ranges over all primes; S_(p-2)(p) = Σ_{1 ≤ i < p} i^(p-2).
* In 2 and 3, m and n range over the integers > 1 (n = 1 satisfies the congruence of 3
  trivially, modulo 1).
* Checked in Python: no prime p < 4000 satisfies either side of 1, and both known Wolstenholme
  primes 16843 and 2124679 satisfy p^3 | S_(p-2)(p); for 1 < m < 3000 neither congruence of 2
  or 3 holds.
-/

namespace OMA.S_oeis_a088164

/-- `p` is a Wolstenholme prime. -/
def IsWolstenholme (p : ℕ) : Prop :=
  p.Prime ∧ (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4]

/-- Mestrovic's criterion, Sykora's question and the converse of Wolstenholme's theorem. -/
theorem main :
    (∀ p : ℕ, p.Prime → (IsWolstenholme p ↔ p ^ 3 ∣ ∑ i ∈ Finset.Ico 1 p, i ^ (p - 2))) ∧
    (∀ m : ℕ, 1 < m → (2 * m).choose m ≡ 2 [MOD m ^ 4] → IsWolstenholme m) ∧
    (∀ n : ℕ, 1 < n → (2 * n - 1).choose (n - 1) ≡ 1 [MOD n ^ 4] → n.Prime) := by
  sorry

end OMA.S_oeis_a088164
