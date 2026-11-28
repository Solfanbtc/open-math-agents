import Mathlib

/-!
# A072779: a(n) = sigma_2(n) + phi(n) * sigma(n).

Source: https://oeis.org/A072779
Credit: @Solfanbtc

Claims (OEIS A072779, comment):
(1) a(n) >= 2 n^2, with equality only when n is prime (or 1);
(2) a(n) = 2 + 2*n^2 if and only if n is the product of two distinct primes;
twin primes: let n = m^2 - 1, then m-1 and m+1 are twin primes iff a(n) = 2 + 2*n^2;
Goldbach: let n = m^2 - r^2, then m-r and m+r are primes that add to 2m iff a(n) = 2 + 2*n^2.

All four are stated, for n >= 1 (offset 1). Clause (1) is stated as written: equality
implies n = 1 or n prime (the converse also holds; checked for n < 3000 in Python, as were
(1), (2) and the twin-prime remark for 2 <= m < 50).

Minimal fix in the Goldbach remark: as written it fails
* for r = 0, e.g. m = 3, n = 9: m - r = m + r = 3 are primes but 9 is not a product of two
  distinct primes, so a(9) is not 2 + 2*81;
* for m - r = 1, e.g. m = 8, r = 7, n = 15 = 3 * 5: a(15) = 2 + 2*15^2 but m - r = 1 is not
  prime.
It is therefore stated for 1 <= r <= m - 2 (two distinct primes m - r < m + r, both >= 2),
where it holds for all m < 50 (Python check). The twin-prime remark is stated for m >= 2
(so that n = m^2 - 1 >= 3 is in the range of the sequence).
-/

namespace OMA.S_oeis_a072779

open ArithmeticFunction

/-- A072779(n) = sigma_2(n) + phi(n) * sigma(n). -/
def a (n : ℕ) : ℕ := sigma 2 n + Nat.totient n * sigma 1 n

/-- `n` is the product of two distinct primes. -/
def IsProdTwoDistinctPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q

/-- The four claims of the comment (the Goldbach remark with `1 ≤ r ≤ m - 2`). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → 2 * n ^ 2 ≤ a n ∧ (a n = 2 * n ^ 2 → n = 1 ∨ n.Prime)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n = 2 + 2 * n ^ 2 ↔ IsProdTwoDistinctPrimes n)) ∧
    (∀ m : ℕ, 2 ≤ m →
      ((m - 1).Prime ∧ (m + 1).Prime ↔ a (m ^ 2 - 1) = 2 + 2 * (m ^ 2 - 1) ^ 2)) ∧
    (∀ m r : ℕ, 1 ≤ r → r + 2 ≤ m →
      ((m - r).Prime ∧ (m + r).Prime ↔ a (m ^ 2 - r ^ 2) = 2 + 2 * (m ^ 2 - r ^ 2) ^ 2)) := by
  sorry

end OMA.S_oeis_a072779
