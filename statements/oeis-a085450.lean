import Mathlib

/-!
# A085450: a(n) is the smallest m > 1 such that m divides Sum_{k=1..m} prime(k)^n.

Source: https://oeis.org/A085450
Credit: @Solfanbtc

`prime(k)` is the `k`-th prime (`prime(1) = 2`), i.e. `Nat.nth Nat.Prime (k - 1)`, so
`Sum_{k=1..m} prime(k)^n = ∑_{i < m} (Nat.nth Nat.Prime i)^n`. Offset 1 (`n ≥ 1`).
We checked by computer the terms a(n) for n = 1, ..., 8, 10, ..., 13, 15 of %S.

Conjectures (Alexander Adamchuk, 2008): `a(n)` exists for all `n`, and `a(n) ≥ 17`.
The second one is proved in the entry for every `n` such that `a(n)` exists (Paul W. Dyson,
2025: an `a(n) < 17` would recur with period at most 12 and would be seen among the first
15 terms, which are all at least 17); it is stated here as the entry states it, i.e. no
`m` with `1 < m < 17` has the property. a(656) is unknown (> 10^12, Dyson 2024).
-/

namespace OMA.S_oeis_a085450

/-- `m` divides `Sum_{k=1..m} prime(k)^n`. -/
def Divides (n m : ℕ) : Prop := m ∣ ∑ i ∈ Finset.range m, (Nat.nth Nat.Prime i) ^ n

/-- Adamchuk's conjectures: for every `n ≥ 1`, some `m > 1` has the property (so `a(n)`
exists), and no `m` with `1 < m < 17` has it (so `a(n) ≥ 17`). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (∃ m : ℕ, 1 < m ∧ Divides n m) ∧ (∀ m : ℕ, 1 < m → m < 17 → ¬ Divides n m) := by
  sorry

end OMA.S_oeis_a085450
