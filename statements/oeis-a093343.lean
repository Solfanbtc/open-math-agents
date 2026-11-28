import Mathlib

/-!
# A093343: Primes of form (prime(n)^2 + prime(n+1)^2)/2.

Source: https://oeis.org/A093343
Credit: @Solfanbtc

Conjecture (Thomas Ordowski, Jul 25 2013, %F line of A093343; also stated in A224888):
`a(n) ~ A224888(n)`, where

* A093343 lists, in increasing order, the primes `r` with `r = (p_k^2 + p_{k+1}^2)/2`
  for some pair of consecutive primes `p_k < p_{k+1}`
  (17, 37, 229, 2029, 14449, 22501, ...);
* A224888 lists, in increasing order, the primes of the form `p_k^2 + (p_{k+1} - p_k)^2`
  for consecutive primes `p_k < p_{k+1}` (5, 13, 29, 293, 997, 6257, ...).

Conventions.
* `(p^2 + q^2)/2` is read as an exact quotient: we require `2 * r = p^2 + q^2`
  (for `p = 2, q = 3` the sum is odd and gives no term; floor division would only add
  the non-prime value 6, so nothing changes, but the exact reading is the intended one).
* `p_k = Nat.nth Nat.Prime k` (0-indexed: `p_0 = 2`), and the `n`-th term of each sequence
  is `Nat.nth` of its set (0-indexed). Both sequences use the same index shift, which does
  not affect `~`.
* `~` is `Asymptotics.IsEquivalent` as `n → ∞`, i.e. `a(n)/A224888(n) → 1`.
* The conjecture presupposes that both sequences are infinite (OEIS indexes `a(n)` for all
  `n ≥ 1`); `Nat.nth` returns `0` past the end of a finite set, which would make the
  equivalence vacuous if both were finite, so we state the infinitude explicitly as part
  of the conjecture. Both infinitudes are open.

The listed terms of both sequences (all %S/%T/%U terms) were checked against these
definitions with python3.
-/

namespace OMA.S_oeis_a093343

open Asymptotics Filter

/-- The set of terms of A093343: primes `r` with `2 r = p_k^2 + p_{k+1}^2` for consecutive
primes `p_k, p_{k+1}`. -/
def A093343Set : Set ℕ :=
  {r | r.Prime ∧ ∃ k : ℕ, 2 * r = Nat.nth Nat.Prime k ^ 2 + Nat.nth Nat.Prime (k + 1) ^ 2}

/-- The set of terms of A224888: primes of the form `p_k^2 + (p_{k+1} - p_k)^2` for
consecutive primes `p_k, p_{k+1}` (the subtraction is exact since `p_k < p_{k+1}`). -/
def A224888Set : Set ℕ :=
  {r | r.Prime ∧ ∃ k : ℕ,
    r = Nat.nth Nat.Prime k ^ 2 + (Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k) ^ 2}

/-- `a n` = A093343(n+1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∈ A093343Set) n

/-- `b n` = A224888(n+1). -/
noncomputable def b (n : ℕ) : ℕ := Nat.nth (· ∈ A224888Set) n

/-- Ordowski's conjecture: A093343(n) ~ A224888(n) (both sequences being infinite). -/
theorem main : A093343Set.Infinite ∧ A224888Set.Infinite ∧
    IsEquivalent atTop (fun n : ℕ => (a n : ℝ)) (fun n : ℕ => (b n : ℝ)) := by
  sorry

end OMA.S_oeis_a093343
