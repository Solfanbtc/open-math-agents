import Mathlib

/-!
# A109280: n such that z(n) and z(n+1) are both prime

Source: https://oeis.org/A109280
`z(n) = a^d + b^d + c^d + ...`, where `a*b*c*...` is the prime factorization of `n` (prime factors
with multiplicity) and `d` is the largest decimal digit of `n`; e.g. `567 = 3^4 * 7` and
`z(567) = 4 * 3^7 + 7^7 = 832291`. A109280 lists the `n` such that `z(n)` and `z(n+1)` are both
prime: 10, 11, 567, 1209, 2034, ...
Conjecture of the entry: "Sequence is infinite."

Conventions. `Nat.primeFactorsList n` lists the prime factors of `n` with multiplicity; for
`n = 1` the factorization is empty and `z(1) = 0` (not prime), so `n = 0, 1` are never terms.
Checked: the Lean `z` gives `z(10) = 7`, `z(11) = 11`, `z(567) = 832291`,
`z(568) = 645753531246529` (as in the example); with python3 (Miller-Rabin) the terms below
70000 are exactly the 36 listed.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a109280

/-- `z(n)`: the sum of `p^d` over the prime factors `p` of `n` (with multiplicity), where `d` is
the largest decimal digit of `n`. -/
def z (n : ℕ) : ℕ :=
  (n.primeFactorsList.map (· ^ (Nat.digits 10 n).foldr max 0)).sum

theorem main : {n : ℕ | (z n).Prime ∧ (z (n + 1)).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a109280
