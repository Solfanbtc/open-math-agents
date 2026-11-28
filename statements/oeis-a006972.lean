import Mathlib

/-!
# A006972: Lucas-Carmichael numbers: squarefree composite numbers k such that p | k => p+1 | k+1.

Source: https://oeis.org/A006972
Credit: @Solfanbtc

A Lucas–Carmichael number is a squarefree composite `k` such that `p + 1 ∣ k + 1` for every prime
`p ∣ k` (data: `399 = 3 · 7 · 19, 935, 2015, …`).

Conjecture (Davide Rotondo, Dec 23 2020): if `k = p q r` with `p, q, r` distinct odd primes,
`d = gcd(p + 1, q + 1, r + 1)`, `p = a d - 1`, `q = b d - 1`, `r = c d - 1`, and `a b c d ∣ k + 1`,
then `k` is a Lucas–Carmichael number.

(Remark: this follows directly, since `p + 1 = a d ∣ a b c d`, and likewise for `q` and `r`;
`k` is squarefree and composite as a product of three distinct primes. It is stated faithfully
as recorded in the entry.)
-/

namespace OMA.S_oeis_a006972

/-- `k` is a Lucas–Carmichael number. -/
def IsLucasCarmichael (k : ℕ) : Prop :=
  Squarefree k ∧ 1 < k ∧ ¬ k.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ k → p + 1 ∣ k + 1

/-- Rotondo's conjecture (OEIS A006972). -/
theorem main : ∀ p q r a b c d : ℕ,
    p.Prime → q.Prime → r.Prime → p ≠ 2 → q ≠ 2 → r ≠ 2 → p ≠ q → p ≠ r → q ≠ r →
    d = Nat.gcd (Nat.gcd (p + 1) (q + 1)) (r + 1) →
    p = a * d - 1 → q = b * d - 1 → r = c * d - 1 →
    a * b * c * d ∣ p * q * r + 1 →
    IsLucasCarmichael (p * q * r) := by
  sorry

end OMA.S_oeis_a006972
