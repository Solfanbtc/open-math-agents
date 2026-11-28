import Mathlib

/-!
# A056240: Smallest number whose prime divisors (taken with multiplicity) add to n.

Source: https://oeis.org/A056240
Credit: @Solfanbtc

Conjecture (David James Sycamore and Michel Marcus, OEIS A056240, comments, Jun 2017):
for even composite n, let P_n denote the largest prime < n-1 such that n-P_n is prime (except
if n = 6); for odd composite n, let P_n denote the largest prime < n-1 such that n-3-P_n is
prime. Then a(n) = min { q*a(n-q) : q prime, P_n <= q < n-1 }.

Conventions:
* a(n) is the least m ≥ 1 whose prime factors with multiplicity (`Nat.primeFactorsList`) sum
  to n (offset 2), written with `sInf`; for n ≥ 2 the set is nonempty (2^k or 2^k·3).
* n ranges over composite numbers (n ≥ 4, not prime), except n = 6 as in the source (for n = 6,
  P_6 = 3 and the formula would give 3·a(3) = 9 ≠ a(6) = 8).
* The conjecture presupposes that P_n exists (for even n this is Goldbach for n, for odd n
  Goldbach for n - 3); `main` asserts its existence (`IsGreatest`), so it includes these
  instances of Goldbach. The minimum is `IsLeast` of the set of the `q * a(n - q)`.
* Checked in Python for 4 ≤ n ≤ 3000: `a` reproduces %S; P_n exists and the formula holds for
  every composite n ≠ 6; a(875) = 30205 as in the example.
-/

namespace OMA.S_oeis_a056240

/-- Sum of the prime factors of `m`, with multiplicity (A001414). -/
def sopfr (m : ℕ) : ℕ := (Nat.primeFactorsList m).sum

/-- A056240: the least `m ≥ 1` with `sopfr m = n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ sopfr m = n}

/-- The condition defining `P_n`: `n - P` prime (even `n`), `n - 3 - P` prime (odd `n`). -/
def Cond (n P : ℕ) : Prop := if n % 2 = 0 then (n - P).Prime else (n - 3 - P).Prime

/-- The Sycamore-Marcus recursion. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n → ¬ n.Prime → n ≠ 6 →
      ∃ P : ℕ, IsGreatest {P : ℕ | P.Prime ∧ P < n - 1 ∧ Cond n P} P ∧
        IsLeast {v : ℕ | ∃ q : ℕ, q.Prime ∧ P ≤ q ∧ q < n - 1 ∧ v = q * a (n - q)} (a n) := by
  sorry

end OMA.S_oeis_a056240
