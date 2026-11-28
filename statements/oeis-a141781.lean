import Mathlib

/-!
# A141781: Composite terms of A120292: a(n) = A120292(A141779(n)).

Source: https://oeis.org/A141781
Credit: @Solfanbtc

A120292(n) (offset 1) is the absolute value of the numerator of the determinant of the
`n × n` rational matrix `M` with `M[i,i] = prime(i)/(1 + prime(i))` and `M[i,j] = 1` for `i ≠ j`.
A141781 lists the composite terms of A120292 (terms `> 1` that are not prime), in order of `n`
(indices A141779: 58, 282, 367, 743, ...).

Conjecture (A. Adamchuk, OEIS A141781; also stated in A120292 and A141779): all terms are
semiprime, i.e. every composite value of A120292 is a product of exactly two primes (counted
with multiplicity). Here: for every `n ≥ 1`, if `A120292(n) > 1` is not prime, then it has
exactly two prime factors with multiplicity.

`prime(i)` for the 1-indexed row `i` is `Nat.nth Nat.Prime i` for the 0-indexed `i : Fin n`.
Checked with python3: the determinant (exact rationals, n ≤ 24) and the closed form
`|1 - Σ (prime(k)+1)| / Π (prime(k)+1)` (reduced) reproduce the 67 listed terms of A120292;
for `n < 5000` the composite values are exactly the 24 listed terms of A141781
(3599, 118477, ..., 55183769) followed by one more, and all are semiprimes.
-/

namespace OMA.S_oeis_a141781

/-- A120292(n) = |numerator(det M_n)|, `M_n[i,i] = p_i/(1+p_i)`, `M_n[i,j] = 1` (`i ≠ j`). -/
noncomputable def A120292 (n : ℕ) : ℕ :=
  (Matrix.det (Matrix.of fun i j : Fin n =>
    if i = j then ((Nat.nth Nat.Prime i : ℕ) : ℚ) / (1 + (Nat.nth Nat.Prime i : ℕ)) else 1)).num.natAbs

/-- Conjecture: every composite term of A120292 (i.e. every term of A141781) is semiprime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 1 < A120292 n → ¬ (A120292 n).Prime →
    (A120292 n).primeFactorsList.length = 2 := by
  sorry

end OMA.S_oeis_a141781
