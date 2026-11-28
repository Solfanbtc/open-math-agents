import Mathlib

/-!
# A127789: 993 has the largest Collatz residue 2^h / (3^t n)

Source: https://oeis.org/A127789
For the `3x + 1` map (`x ↦ x/2` for even `x`, `x ↦ 3x + 1` for odd `x`), let `h(n)` and `t(n)` be
the numbers of halving and tripling steps of the trajectory of `n` down to 1. A127789 lists the
record indices of `2^h(n) / (3^t(n) n)`: 1, 3, 7, 9, 505, 559, 745, 993.
Comment (T. D. Noe, Apr 08 2007): "Eric Roosendaal calls 2^j / (n*3^k) the residue of n and
conjectures that 993 yields the highest residue." (M. F. Hasler: the next record, if any, is
`> 2^32`.)

We state: for every `n ≥ 1` whose trajectory reaches 1, its residue is at most that of 993.
Formalization. `m` is the first time the trajectory reaches 1 (`step^[m] n = 1` and
`step^[i] n ≠ 1` for `i < m`); `h` and `t` count the even resp. odd values among
`step^[i] n`, `i < m`. The hypothesis that `n` reaches 1 avoids presupposing the Collatz
conjecture (as Hasler notes, unreached `n` are irrelevant to the records). For 993: `h = 61`,
`t = 32`.
Checked with python3 (exact fractions): the records for `n < 2·10^5` are exactly the 8 listed
terms, ending with 993 (residue ≈ 1.25314).

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a127789

/-- The `3x + 1` map. -/
def step (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- The residue `2^h / (3^t n)` of `n`, given that its trajectory first reaches 1 at time `m`. -/
noncomputable def residue (n m : ℕ) : ℝ :=
  (2 : ℝ) ^ ((Finset.range m).filter (fun i => step^[i] n % 2 = 0)).card /
    ((3 : ℝ) ^ ((Finset.range m).filter (fun i => step^[i] n % 2 = 1)).card * n)

/-- `n` first reaches 1 at time `m`. -/
def FirstHit (n m : ℕ) : Prop := step^[m] n = 1 ∧ ∀ i < m, step^[i] n ≠ 1

theorem main : ∀ n m m₀ : ℕ, 1 ≤ n → FirstHit n m → FirstHit 993 m₀ →
    residue n m ≤ residue 993 m₀ := by
  sorry

end OMA.S_oeis_a127789
