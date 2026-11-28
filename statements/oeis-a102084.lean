import Mathlib

/-!
# A102084: a(1) = 0; for n>0, write 2n=p+q (p, q prime), p*q maximal; then a(n)=p*q (see A073046).

Source: https://oeis.org/A102084
Credit: @Solfanbtc

`a(n)` is the largest `p·q` with `p, q` prime and `p + q = 2n`, and `0` if there is none
(`n = 1`). The first comment (for `n > 1`, the largest semiprime whose prime factors sum to
`2n`) is this definition read under the Goldbach conjecture, which is stated upstream
(`goldbach`, FormalConjectures/Wikipedia/GoldbachConjecture.lean). It adds nothing to state.

Stated here is T. D. Noe's claim (Apr 27 2011, OEIS %C): `a(n)` is also the greatest integer
`x` such that `x' = 2n`, or `0` if there is no such `x`, where `x'` is the arithmetic derivative
(A003415: `0' = 1' = 0`, `p' = 1`, `(uv)' = u'v + uv'`). This is not proved in the entry and
does not follow from Goldbach alone. A non-semiprime antiderivative with `Ω(x) = k ≥ 3` only
satisfies `x ≤ (2n/k)^(k/(k-1))`, so one would also need a Goldbach partition `p + q = 2n` with
`p q` that large. Checked by exhaustive search for `n ≤ 1000` (every `x` with `x' = 2n` is
`≤ n²`, since `x' ≥ 2√x` for composite `x`).
-/

namespace OMA.S_oeis_a102084

/-- The arithmetic derivative A003415. -/
def arithDeriv (x : ℕ) : ℕ := ∑ p ∈ x.primeFactors, x.factorization p * (x / p)

/-- `a n = max {p q : p, q prime, p + q = 2n}`, or `0` if there is no such pair. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter (fun p => p.Prime ∧ (2 * n - p).Prime)).sup
    (fun p => p * (2 * n - p))

theorem main : ∀ n : ℕ, 1 ≤ n →
    ((∃ x : ℕ, arithDeriv x = 2 * n) → IsGreatest {x : ℕ | arithDeriv x = 2 * n} (a n)) ∧
    ((¬ ∃ x : ℕ, arithDeriv x = 2 * n) → a n = 0) := by
  sorry

end OMA.S_oeis_a102084
