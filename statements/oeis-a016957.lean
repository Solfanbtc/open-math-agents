import Mathlib

/-!
# A016957: a(n) = 6*n + 4.

Source: https://oeis.org/A016957
Credit: @Solfanbtc

Conjecture (John Tyler Rascoe, OEIS A016957, comment, Jul 09 2022): this sequence contains
some but not all, even numbers with odd abundance A088827. They appear in this sequence at
indices A186424(n) - 1.

Definitions, taken from the OEIS entries:
* A016957 (offset 0): a(n) = 6n + 4.
* A088827: even numbers k ≥ 1 whose abundance sigma(k) - 2k is odd (computed in `ℤ`).
* A186421 (offset 0): even numbers interleaved with repeated odd numbers, i.e. a(n) = n for n
  even and 2*floor(n/4) + 1 for n odd (formula of that entry): 0, 1, 2, 1, 4, 3, 6, 3, ...
* A186423 (offset 0): partial sums of A186421: 0, 1, 3, 4, 8, 11, 17, ...
* A186424: the odd terms of A186423: 1, 3, 11, 17, 33, 43, 67, ...

Reading of the conjecture: (1) some even number with odd abundance is a term 6n+4; (2) some
even number with odd abundance is not of the form 6n+4; (3) the indices n (offset 0) at which
6n+4 has odd abundance are exactly the numbers A186424(j) - 1, i.e. the n with n + 1 an odd
term of A186423. Checked in Python for n < 600: the indices are 0, 2, 10, 16, 32, 42, 66, ...
-/

namespace OMA.S_oeis_a016957

/-- A088827: even positive numbers with odd abundance `sigma(k) - 2k`. -/
def IsEvenOddAbundant (k : ℕ) : Prop :=
  0 < k ∧ Even k ∧ Odd ((ArithmeticFunction.sigma 1 k : ℤ) - 2 * k)

/-- A186421: even numbers interleaved with repeated odd numbers. -/
def A186421 (n : ℕ) : ℕ := if Even n then n else 2 * (n / 4) + 1

/-- A186423: partial sums of A186421. -/
def A186423 (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), A186421 i

/-- The terms of A186424: the odd terms of A186423. -/
def InA186424 (m : ℕ) : Prop := Odd m ∧ ∃ j, A186423 j = m

/-- Rascoe's conjecture on the even numbers with odd abundance among the terms 6n+4. -/
theorem main :
    (∃ n : ℕ, IsEvenOddAbundant (6 * n + 4)) ∧
    (∃ k : ℕ, IsEvenOddAbundant k ∧ ∀ n : ℕ, k ≠ 6 * n + 4) ∧
    (∀ n : ℕ, IsEvenOddAbundant (6 * n + 4) ↔ InA186424 (n + 1)) := by
  sorry

end OMA.S_oeis_a016957
