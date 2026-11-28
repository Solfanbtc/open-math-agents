import Mathlib

/-!
# A002596: Numerators in expansion of sqrt(1+x).

Source: https://oeis.org/A002596
Credit: @Solfanbtc

Observation/conjecture (Dimitri Papadopoulos, Oct 28 2016): if a term of this sequence is
divisible by a prime p, then that term is in a block of exactly (p^k-3)/2 consecutive terms all
of which are divisible by p. Furthermore, if a(n) is the term preceding such a block then
a(p*n-(p-1)/2) also precedes a block of (p^(k+1)-3)/2 terms all divisible by p.
Example: a(4) = -5 is in a block of (5^1-3)/2 = 1 term divisible by 5 (preceded by a(3)), and
a(5*3-(5-1)/2) = a(13) = 52003 precedes a block of exactly (5^2-3)/2 = 11 terms divisible by 5.

Conventions:
* `a n` is the numerator, in lowest terms, of the coefficient of x^n in sqrt(1+x), i.e. of
  binomial(1/2, n) = (1/2)(1/2-1)...(1/2-n+1)/n!. So a = 1, 1, -1, 1, -5, 7, -21, 33, -429, ...
  (signed, as in the OEIS data; divisibility does not depend on the sign).
* A block is a maximal run of consecutive divisible terms: `IsBlock p a n L` says that
  a(n+1), ..., a(n+L) are divisible by p while a(n) and a(n+L+1) are not. a(n) is the term
  preceding the block, and "exactly" in the source means the run is maximal.
* "A block of (p^k-3)/2 terms" is written `2 * L + 3 = p ^ k`, which avoids natural-number
  subtraction. The second part is stated for genuine blocks (L > 0, i.e. blocks that contain a
  term divisible by p), which are the blocks the first sentence speaks of.
* p = 2 never divides a term (the denominators are powers of 2), so the statement is vacuous
  there.
Checked with python3 for all primes 3 <= p < 40 and indices up to about 1300.
-/

namespace OMA.S_oeis_a002596

/-- The coefficient of `x ^ n` in the expansion of `sqrt (1 + x)`, i.e. `binomial(1/2, n)`. -/
def coeff (n : ℕ) : ℚ :=
  (∏ i ∈ Finset.range n, ((1 : ℚ) / 2 - i)) / n.factorial

/-- A002596: the numerator of the coefficient of `x ^ n` in `sqrt (1 + x)`. -/
def a (n : ℕ) : ℤ := (coeff n).num

/-- `a (n + 1), ..., a (n + L)` are divisible by `p`, and `a n`, `a (n + L + 1)` are not:
a maximal block of `L` consecutive terms divisible by `p`, preceded by `a n`. -/
def IsBlock (p n L : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ a n ∧ (∀ i ∈ Finset.Icc (n + 1) (n + L), (p : ℤ) ∣ a i) ∧
    ¬ (p : ℤ) ∣ a (n + L + 1)

theorem main : ∀ p : ℕ, p.Prime →
    (∀ j : ℕ, (p : ℤ) ∣ a j →
      ∃ n L k : ℕ, n < j ∧ j ≤ n + L ∧ IsBlock p n L ∧ 2 * L + 3 = p ^ k) ∧
    (∀ n L k : ℕ, 0 < L → IsBlock p n L → 2 * L + 3 = p ^ k →
      ∃ M : ℕ, 2 * M + 3 = p ^ (k + 1) ∧ IsBlock p (p * n - (p - 1) / 2) M) := by
  sorry

end OMA.S_oeis_a002596
