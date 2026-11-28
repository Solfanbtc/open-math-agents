import Mathlib

/-!
# A001177: Sum_{d|n} phi(d) * (Fibonacci entry point of d) = A232656(n)

Source: https://oeis.org/A001177
Credit: @Solfanbtc

A001177: `a(n)` is the least `k ≥ 1` such that `n` divides the Fibonacci number `F_k`
(the Fibonacci entry point; offset 1).

Conjecture (L. J. Kleinwaks, Oct 28 2017, in the entry): `Sum_{d|n} phi(d) * a(d) = A232656(n)`.

A232656 (offset 1): "The number of pairs of numbers below n that, when generating a
Fibonacci-like sequence modulo n, contain zeros": the number of pairs `(x, y)` with
`0 ≤ x, y < n` such that the sequence `s_0 = x`, `s_1 = y`, `s_{k+2} = s_{k+1} + s_k (mod n)`
has some term equal to `0` (the initial terms count, so every pair with `x = 0` counts).

The entry's other conjecture (Wall's: `a(p^e) = p^(e-1) a(p)`, i.e. there are no Wall-Sun-Sun
primes) is already stated upstream (`FormalConjectures/Wikipedia/WallSunSun.lean`) and is not
repeated here.

Checked with python3: this definition of A232656 reproduces its 21 listed terms, and the
identity holds for `1 ≤ n < 120`.
-/

namespace OMA.S_oeis_a001177

/-- A001177: the least `k ≥ 1` with `n ∣ F_k`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ n ∣ Nat.fib k}

/-- The Fibonacci-like sequence modulo `n` with initial terms `x, y`. -/
def gen (n x y : ℕ) : ℕ → ℕ
  | 0 => x % n
  | 1 => y % n
  | k + 2 => (gen n x y k + gen n x y (k + 1)) % n

/-- A232656: the number of pairs `(x, y)` with `x, y < n` whose Fibonacci-like sequence modulo
`n` contains a zero. -/
noncomputable def a232656 (n : ℕ) : ℕ :=
  {p : ℕ × ℕ | p.1 < n ∧ p.2 < n ∧ ∃ k, gen n p.1 p.2 k = 0}.ncard

/-- Kleinwaks' conjecture: `Sum_{d|n} phi(d) a(d) = A232656(n)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∑ d ∈ n.divisors, d.totient * a d = a232656 n := by
  sorry

end OMA.S_oeis_a001177
