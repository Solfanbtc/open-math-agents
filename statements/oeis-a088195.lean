import Mathlib

/-!
# A088195: Distance (A088192) of primes from the largest quadratic residues modulo the primes (A088190), where the latter is non-monotonic.

Source: https://oeis.org/A088195
Credit: @Solfanbtc

`LQR(p)` (A088190) is the largest nonzero quadratic residue modulo the prime `p`
(`LQR(2) = 1`). Write `p_i = Nat.nth Nat.Prime i` (so `p_0 = 2`). Following the PARI programs
of A088194 and A088195, for each `i ≥ 1` with `LQR(p_i) ≤ LQR(p_{i-1})` ("non-monotonic"),
A088194 records `D = LQR(p_i) - LQR(p_{i-1})` and A088195 records `M = p_i - LQR(p_i)`.
We checked by computer that this reproduces all listed terms of A088194 and A088195, except
the first term of A088195 (p = 3: 3 - LQR(3) = 3 - 1 = 2, while the data says 3; the
conjecture below holds in both cases since there D = 0).

Conjecture (Ferenc Adorjan, 2003): if `D(n) = -1` then `M(n) = 7`, and if `M(n) = 3` then
`D(n) = 0`. Stated for every index `i ≥ 1` at which the sequence of largest quadratic
residues is non-monotonic (these are exactly the indices listed by A088194/A088195).
We checked it for the first 30000 primes (1650 such indices).
-/

namespace OMA.S_oeis_a088195

/-- The largest nonzero quadratic residue modulo `p` (A088190 when `p` is prime). -/
def LQR (p : ℕ) : ℕ :=
  ((Finset.range p).filter fun r => 0 < r ∧ ∃ j ∈ Finset.range p, j ^ 2 % p = r).sup id

/-- Adorjan's conjecture. -/
theorem main : ∀ i : ℕ, 1 ≤ i →
    LQR (Nat.nth Nat.Prime i) ≤ LQR (Nat.nth Nat.Prime (i - 1)) →
    (((LQR (Nat.nth Nat.Prime i) : ℤ) - LQR (Nat.nth Nat.Prime (i - 1)) = -1 →
        Nat.nth Nat.Prime i - LQR (Nat.nth Nat.Prime i) = 7) ∧
      (Nat.nth Nat.Prime i - LQR (Nat.nth Nat.Prime i) = 3 →
        LQR (Nat.nth Nat.Prime i) = LQR (Nat.nth Nat.Prime (i - 1)))) := by
  sorry

end OMA.S_oeis_a088195
