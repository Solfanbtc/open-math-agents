import Mathlib

/-!
# A066861: For x > 0 let f(x) = x/2 if x is even, f(x) = (3*x+1)/2 if x is odd (3x+1 or Collatz problem). Sequence gives numbers such that k-1 applications of f lead to k for some k > 0.

Source: https://oeis.org/A066861
Credit: @Solfanbtc

`f(x) = x/2` for even `x`, `f(x) = (3x+1)/2` for odd `x`. A positive `n` is a term iff
`f^(k-1)(n) = k` for some `k > 0` (e.g. `11`: seven applications of `f` lead to `8`).
Terms: 1, 3, 4, 10, 11, 12, 18, … (offset 1, so `a(1) = 1`; with `Nat.nth`, which is 0-indexed,
`a(n) = Nat.nth IsTerm (n - 1)`).

Conjecture (Benoit Cloitre, 2002): `a(n) ~ n log n` (natural logarithm), i.e.
`a(n) / (n log n) → 1`. (This presupposes that the sequence is infinite; if it were finite,
`Nat.nth` would be eventually `0` and the statement false.) Checked with python3: the
definition reproduces the listed terms; numerically `a(n)/(n log n)` is about 1.18 at
`n = 143207` (`a(n) ≈ 2·10^6`), decreasing slowly.
-/

namespace OMA.S_oeis_a066861

open Filter Topology

/-- The map `f` of the Collatz problem (shortcut form). -/
def f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- `n` is a term of A066861. -/
def IsTerm (n : ℕ) : Prop := 0 < n ∧ ∃ k : ℕ, 0 < k ∧ f^[k - 1] n = k

/-- Cloitre's conjecture: `a(n) ~ n log n`, with `a(n) = Nat.nth IsTerm (n - 1)`. -/
theorem main :
    Tendsto (fun n : ℕ => (Nat.nth IsTerm (n - 1) : ℝ) / (n * Real.log n)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a066861
