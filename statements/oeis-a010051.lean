import Mathlib

/-!
# A010051: Characteristic function of primes: 1 if n is prime, else 0.

Source: https://oeis.org/A010051
Credit: @Solfanbtc

Conjecture (Gary Detlefs, Sep 12 2010, formula section of A010051): "It appears that
a(n) = (H(n)*H(n + 1)) mod n, where H(n) = n!*Sum_{k=1..n} 1/k = A000254(n)."

Formalization.
* `H` is A000254, defined by its recurrence `H(0) = 0`, `H(n+1) = (n+1)·H(n) + n!`, which is
  equivalent to `H(n) = n!·Σ_{k=1}^{n} 1/k` (data 0, 1, 3, 11, 50, 274, ...).
* The offset of A010051 is 1, so `n ≥ 1`; `a(n)` is `1` if `n` is prime and `0` otherwise.
  At `n = 1` both sides are `0`. A python check confirms the identity for all `n < 3000`.
* Detlefs' related conjectures in A000254 are stated separately (statements/oeis-a000254.lean);
  this product formula is not among them.

Not stated: A. Cicuttin's remark (Aug 23 2020) that the Fourier spectra of the partial sequences
"exhibit a remarkable symmetry" which "appears ... grows with n"; it gives no precise claim.
-/

namespace OMA.S_oeis_a010051

/-- A000254: `H(0) = 0`, `H(n+1) = (n+1)·H(n) + n!`, i.e. `H(n) = n!·Σ_{k=1}^{n} 1/k`. -/
def H : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) * H n + n.factorial

/-- Detlefs' conjecture: for `n ≥ 1`, `(H(n)·H(n+1)) mod n` is `1` if `n` is prime and `0`
otherwise. -/
theorem main : ∀ n : ℕ, 1 ≤ n → H n * H (n + 1) % n = if n.Prime then 1 else 0 := by
  sorry

end OMA.S_oeis_a010051
