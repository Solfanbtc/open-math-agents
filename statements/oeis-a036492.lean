import Mathlib

/-!
# A036492: Offsets for the Atkin Partition Congruence theorem.

Source: https://oeis.org/A036492
Credit: @Solfanbtc

Statement (OEIS A036492, %C): let T = 5^a * 7^b * 11^c (A036490) and
Q = 5^a * 7^floor((b+2)/2) * 11^c (A036491). If 24*g ≡ 1 (mod T), then p(g) ≡ 0 (mod Q), where
p(g) is the number of integer partitions of g.
Status: this is a theorem, not an open problem. It is Ramanujan's conjectured congruences for
the moduli 5^a 7^b 11^c, with the exponent of 7 corrected; the entry cites G. E. Andrews, The
Theory of Partitions, 1976, pp. 159-161, and Ramanujan's papers (1919). The powers of 5 and 7
are due to G. N. Watson (1938), the powers of 11 to A. O. L. Atkin (1967). It is stated here
faithfully as recorded in the entry.

Minimal fix: for b = 0 the formula floor((b+2)/2) = 1 would require 7 | p(g) for every g
(e.g. a = b = c = 0, g = 1, p(1) = 1), which is false. The entry's own A036491 uses the factor
7^0 = 1 when b = 0 (A036491(1) = 5 for T = 5), so the exponent of 7 is floor((b+2)/2) for
b ≥ 1 and 0 for b = 0.

Conventions:
* `p g = Fintype.card (Nat.Partition g)`; a, b, c, g range over all natural numbers.
* Checked in Python: for all T = 5^a 7^b 11^c ≤ 30000 and all g ≤ 30000 with 24g ≡ 1 (mod T)
  (48098 cases), Q divides p(g); the least such g reproduces the first 20 terms of A036492.
-/

namespace OMA.S_oeis_a036492

/-- The number of partitions of `g`. -/
def p (g : ℕ) : ℕ := Fintype.card (Nat.Partition g)

/-- The modulus `Q = 5^a 7^⌊(b+2)/2⌋ 11^c` of A036491 (with `7^0` when `b = 0`). -/
def Q (a b c : ℕ) : ℕ := 5 ^ a * 7 ^ (if b = 0 then 0 else (b + 2) / 2) * 11 ^ c

/-- The Atkin-Watson partition congruences. -/
theorem main :
    ∀ a b c g : ℕ, 24 * g ≡ 1 [MOD 5 ^ a * 7 ^ b * 11 ^ c] → Q a b c ∣ p g := by
  sorry

end OMA.S_oeis_a036492
