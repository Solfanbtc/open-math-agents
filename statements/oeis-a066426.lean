import Mathlib

/-!
# A066426: least k with phi(n+k) = phi(n) + phi(k)

Source: https://oeis.org/A066426
Credit: @Solfanbtc

"Conjectured values for `a(n)` = least natural number `k` such that `φ(n+k) = φ(n) + φ(k)`, if
`k` exists; otherwise `0`" (offset 1): `2, 1, 0, 4, 4, 4, 14, …` (R. K. Guy, UPINT B36).

Conjectural content of the entry, stated as the two parts of `main`:
1. "The values of `a(3)`, `a(15)` and `a(21)` listed above, namely `0`, are conjectural. There is no
   natural number `k < 10^6` satisfying … `φ(n+k) = φ(n) + φ(k)` for `n = 3, 15, 21`": for
   `n ∈ {3, 15, 21}` no `k ≥ 1` satisfies the equation.
2. (T. D. Noe, Jul 15 2005) "For `n ≡ 1 (mod 3)` or `n ≡ 2 (mod 3)`, it appears that the least
   solution `k` satisfies `k ≤ 2n`": for every such `n ≥ 1` there is a solution with
   `1 ≤ k ≤ 2n`.
(Python: 2 holds for `n < 3000`; for `n = 3, 15, 21` there is no solution with `k < 2·10^5`.)
-/

namespace OMA.S_oeis_a066426

/-- The "homomorphic condition" `φ(n+k) = φ(n) + φ(k)`. -/
def Hom (n k : ℕ) : Prop := Nat.totient (n + k) = Nat.totient n + Nat.totient k

/-- The two conjectures recorded in A066426. -/
theorem main :
    (∀ n ∈ ({3, 15, 21} : Finset ℕ), ∀ k : ℕ, 1 ≤ k → ¬ Hom n k) ∧
    (∀ n : ℕ, 1 ≤ n → n % 3 ≠ 0 → ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 * n ∧ Hom n k) := by
  sorry

end OMA.S_oeis_a066426
