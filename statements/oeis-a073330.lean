import Mathlib

/-!
# A073330: Let c(1)=n and c(k+1)=floor(c(k)/Pi) if c(k) is even, or c(k+1)=floor(Pi*c(k)) otherwise; sequence gives the smallest value a(n) such that c(a(n))=0.

Source: https://oeis.org/A073330
Credit: @Solfanbtc

For `n ≥ 1` (offset 1): `c(1) = n`, `c(k+1) = ⌊c(k)/π⌋` if `c(k)` is even and `⌊π c(k)⌋` if
`c(k)` is odd; `a(n)` is the least `k ≥ 1` with `c(k) = 0`. With `step` the map above,
`c(k) = step^[k-1] n`. Example: `c = 1, 3, 9, 28, 8, 2, 0`, so `a(1) = 7`. The definition
reproduces every term of %S, %T, %U (checked in Python with 80-digit π).

Conjecture (B. Cloitre, %F):
1. the sequence always exists: for every `n ≥ 1` some `c(k)` is `0`;
2. there is a constant `C = 2.8...` such that `Σ_{k=1..n} a(k)` is asymptotic to `C n log n`.
   `C = 2.8...` is read as a constant whose decimal expansion begins `2.8`, i.e. `2.8 ≤ C < 2.9`;
   asymptotic is `~` (ratio tending to 1).

The entry's parenthetical examples `a(123456789) = 61, a(2^30) = 70` are not part of the
statement: exact computation (300-digit π) gives `a(123456789) = 61` but `a(2^30) = 71`.
Numerically `Σ_{k≤n} a(k) / (n log n)` is about 3.06 at `n = 10^4` and 3.07 at `n = 2·10^5`.
-/

namespace OMA.S_oeis_a073330

open Real

/-- One step of the map: `⌊m/π⌋` for even `m`, `⌊π m⌋` for odd `m`. -/
noncomputable def step (m : ℕ) : ℕ :=
  if Even m then ⌊(m : ℝ) / π⌋₊ else ⌊π * (m : ℝ)⌋₊

/-- `a(n)`: the least `k ≥ 1` with `c(k) = step^[k-1] n = 0` (meaningful once such `k` exists). -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ step^[k - 1] n = 0}

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ step^[k - 1] n = 0) ∧
    ∃ C : ℝ, 2.8 ≤ C ∧ C < 2.9 ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (a k : ℝ))
        (fun n : ℕ => C * n * Real.log n) := by
  sorry

end OMA.S_oeis_a073330
