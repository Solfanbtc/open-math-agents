import Mathlib

/-!
# A051222: Numbers k such that Bernoulli number B_{k} has denominator 6.

Source: https://oeis.org/A051222
Credit: @Solfanbtc

Conjecture (Richard R. Forberg, Apr 07 2025, comment in A051222): "When the expression
(p+q^b)/2 is required to be prime, p is prime, and q is a prime >= 5, then all p values are prime
congruent to 1 (mod 12) (A068228), if and only if the exponent b is a member of this set."

Reading. For an exponent `b`, the "p values" are the primes `p` for which some prime `q ≥ 5`
makes `(p + q^b)/2` a prime, i.e. `p + q^b = 2r` with `r` prime (an odd `p + q^b` gives a
non-integer, which is not prime). The conjecture says that this set of primes is exactly A068228,
the primes `≡ 1 (mod 12)`, if and only if `b` is in A051222, i.e. the Bernoulli number `B_b` has
denominator `6`. The set must be read as *equal to* A068228, not merely contained in it: e.g. for
`b = 4` every such `p` is `≡ 1 (mod 12)` as well (since `q^4 ≡ 1 (mod 24)`), yet `4` is not in
A051222; what fails there is that the primes `p ≡ 4 (mod 5)`, such as `229`, never occur. A
python check (p < 400, q < 1500, extended to q < 20000 for the few misses) agrees: equality for
`b = 2, 14, 26, 34`, and failures for `b = 1, 3, 4, 6, 10, 18`.

Mathlib's `bernoulli` uses `B_1 = -1/2`; denominators are the same in either convention.

The companion comment (Apr 25 2025) about "additional exponential expressions ... for several
known prime subsequences" is not stated precisely in the entry and is not formalized here.
-/

namespace OMA.S_oeis_a051222

/-- The primes `p` such that `(p + q^b)/2` is prime for some prime `q ≥ 5`. -/
def pValues (b : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ ∃ r : ℕ, r.Prime ∧ 2 * r = p + q ^ b}

/-- Forberg's conjecture: the `p` values for the exponent `b` are exactly the primes
`≡ 1 (mod 12)` if and only if the Bernoulli number `B_b` has denominator `6`. -/
theorem main : ∀ b : ℕ,
    pValues b = {p : ℕ | p.Prime ∧ p % 12 = 1} ↔ (bernoulli b).den = 6 := by
  sorry

end OMA.S_oeis_a051222
