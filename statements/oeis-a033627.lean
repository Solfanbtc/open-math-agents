import Mathlib

/-!
# A033627: numbers of steps until the last n digits repeat under m ↦ m^2 + 1

Source: https://oeis.org/A033627
Credit: @Solfanbtc

A033627 (offset 1): the 0-additive sequence 1, 2, 4, 7, 10, 13, 16, …; by the entry's formula it
is 2 together with the numbers `3k + 1` (A016777), i.e. `a(1) = 1`, `a(2) = 2` and
`a(k) = 3k - 5` for `k ≥ 3`. We use this closed form as the definition.

Conjecture (Ya-Ping Lu, Oct 19 2021): "a(n+1) is the number of distinct numbers of steps
required for the last n digits of integers to repeat themselves by iterating the map
m -> m^2 + 1."

Reading. For `n ≥ 1` and a residue `x` modulo `10^n` (the last `n` digits), iterate
`f(m) = m^2 + 1` modulo `10^n`; the number of steps required for the last `n` digits to repeat is
the least `j ≥ 1` such that `f^j(x) ≡ f^i(x) (mod 10^n)` for some `i < j` (it exists by
pigeonhole, `j ≤ 10^n`). The conjecture says that the number of distinct such `j`, over all
`x < 10^n`, is `a(n+1)`. Checked with python3: this count is 2, 4, 7, 10, 13, 16 for
`n = 1, …, 6`, matching `a(2), …, a(7)`.
-/

namespace OMA.S_oeis_a033627

/-- A033627: `1, 2`, then `3k - 5` for `k ≥ 3`. -/
def a (k : ℕ) : ℕ := if k = 1 then 1 else if k = 2 then 2 else 3 * k - 5

/-- The map `m ↦ m^2 + 1`. -/
def f (m : ℕ) : ℕ := m ^ 2 + 1

/-- The number of steps until the last `n` digits of the orbit of `x` under `f` repeat. -/
noncomputable def steps (n x : ℕ) : ℕ :=
  sInf {j : ℕ | 1 ≤ j ∧ ∃ i < j, f^[j] x % 10 ^ n = f^[i] x % 10 ^ n}

/-- Lu's conjecture: for `n ≥ 1`, the number of distinct values of `steps n x` over
`0 ≤ x < 10^n` is `a(n+1)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    {j : ℕ | ∃ x < 10 ^ n, steps n x = j}.ncard = a (n + 1) := by
  sorry

end OMA.S_oeis_a033627
