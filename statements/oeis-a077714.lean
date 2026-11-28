import Mathlib

/-!
# A077714: repeatedly prefix d0...0 to get the smallest prime

Source: https://oeis.org/A077714
Credit: @Solfanbtc

`a(1) = 1`; thereafter `a(n)` is the smallest prime obtained by prefixing `a(n-1)` with a number
of the form `d·10^k`, `0 < d < 10`, `k ≥ 0` (i.e. the decimal string `d 0...0 a(n-1)` with `k`
zeros), or 0 if no such prime exists: 1, 11, 211, 4211, 34211, 234211, 4234211, 304234211, ...
Numerically, the candidates for `a(n)` are the numbers `d·10^(L+k) + a(n-1)`, where `L` is the
number of decimal digits of `a(n-1)`.

Conjecture (entry): "d*10^k always exists", i.e. at every step some candidate is prime (so no
term is 0).

Encoding: `a 1 = 1`, `a (n+1)` is the least prime candidate built from `a n` (`sInf` of the set
of prime candidates, which is `0` if that set is empty); the conjecture says that for every
`n ≥ 1` the set of prime candidates built from `a n` is nonempty.

Sanity check (python): the construction reproduces all 14 listed terms, and the first 26 terms
(up to 52 digits) exist.
-/

namespace OMA.S_oeis_a077714

/-- The prime candidates obtained by prefixing `m` with `d 0...0`. -/
def candidates (m : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ d k : ℕ, 0 < d ∧ d < 10 ∧ p = d * 10 ^ ((Nat.digits 10 m).length + k) + m}

/-- A077714 (indexed from 1; the value at 0 is unused). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => sInf (candidates (a (n + 1)))

/-- The conjecture: at every step a prime candidate exists. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (candidates (a n)).Nonempty := by
  sorry

end OMA.S_oeis_a077714
