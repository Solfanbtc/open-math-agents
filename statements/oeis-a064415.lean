import Mathlib

/-!
# A064415: a(1) = 0, a(n) = iter(n) if n is even, a(n) = iter(n)-1 if n is odd.

Source: https://oeis.org/A064415
Credit: @Solfanbtc

`iter(n) = A003434(n)` is the least number of iterations of Euler's totient `φ` taking `n` to `1`.
`a(1) = 0`, and for `n ≥ 2`, `a(n) = iter(n)` if `n` is even, `iter(n) - 1` if `n` is odd.
Data: `0, 1, 1, 2, 2, 2, 2, 3, 2, 3, ...`.

`A309243` is the completely multiplicative function `b` with `b(p) = p · b(p-1)` for every prime
`p` (so `b(1) = 1`, `b(2) = 2`, `b(3) = 6`, `b(5) = 20`, ...).

Claim stated (Rémy Sigrist's conjecture in A309243: "Apparently, A007814(a(n)) = A064415(n)";
recorded in A064415 as `a(n) = A007814(A309243(n))`): for every `n ≥ 1`, the 2-adic valuation of
`A309243(n)` is `A064415(n)`.
Status: Antti Karttunen (May 13 2020, in the entry) notes that it reduces to the formula
`a(n) = ∑_{p | n} a(p-1)` (`n > 2`, primes with multiplicity), so that it "holds also"; that
formula rests on the additivity of `a` (Shapiro's theorem on iterated totients). It is stated
here faithfully all the same.

A python3 check: the definitions reproduce the data of A064415 and A309243, and the claim holds
for `1 ≤ n ≤ 10^5`.

Conventions: `B fuel n` computes `b(n)` from the factorization of `n`, recursing on `p - 1 < n`;
fuel `n` suffices (each recursive call lowers the argument), so `b n = B n n`.
-/

namespace OMA.S_oeis_a064415

/-- `iter n = A003434(n)`: least `k` with `φ^[k] n = 1`. -/
noncomputable def iter (n : ℕ) : ℕ := sInf {k : ℕ | Nat.totient^[k] n = 1}

/-- `A064415(n)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 1 then 0 else if Even n then iter n else iter n - 1

/-- Fuelled computation of the completely multiplicative `b` with `b(p) = p · b(p - 1)`. -/
def B : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f + 1, n => ∏ p ∈ n.primeFactors, (p * B f (p - 1)) ^ (n.factorization p)

/-- `A309243(n)`. -/
def b (n : ℕ) : ℕ := B n n

/-- Sigrist's claim: `A007814(A309243(n)) = A064415(n)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → padicValNat 2 (b n) = a n := by
  sorry

end OMA.S_oeis_a064415
