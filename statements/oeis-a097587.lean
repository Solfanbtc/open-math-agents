import Mathlib

/-!
# A097587: floor of the Fortunate number over the prime, conjectured always < 8

Source: https://oeis.org/A097587 (with https://oeis.org/A005235)
A005235 (offset 1): the Fortunate number `F(n)` is the least `m > 1` such that `m + p_n#` is
prime, where `p_n` is the `n`-th prime and `p_n#` is the product of all primes `≤ p_n`
(3, 5, 7, 13, 23, 17, ...). A097587 (offset 1) is `a(n) = ⌊F(n) / p_n⌋`.
Conjecture of the entry: "a(n) is always < 8" (the same bound appears in A005235 as a conjecture
of Pierre Cami: "a(n)/prime(n) < 8 for all n").

We state: for every `n ≥ 1`, `⌊F(n) / p_n⌋ < 8` (natural-number division is the floor).
Indexing: `Nat.nth Nat.Prime (n - 1)` is `p_n` (so `p_1 = 2`), and `primorial p` is the product
of the primes `≤ p`.
Checked with python3: `⌊F(n)/p_n⌋` for `n = 1..105` agrees with the listed data except at
`n = 44` and `n = 70`, where the entry lists 2 but the definition gives 3 (`F(44) = 751` from
A005235 and `p_44 = 193`, `⌊751/193⌋ = 3`); the maximum over this range is 4 (`n = 33`), so the
data errors do not affect the conjecture.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a097587

/-- The `n`-th prime, `n ≥ 1` (`p 1 = 2`). -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A005235: the least `m > 1` such that `m + p_n#` is prime. -/
noncomputable def F (n : ℕ) : ℕ := sInf {m : ℕ | 1 < m ∧ (m + primorial (p n)).Prime}

theorem main : ∀ n : ℕ, 1 ≤ n → F n / p n < 8 := by
  sorry

end OMA.S_oeis_a097587
