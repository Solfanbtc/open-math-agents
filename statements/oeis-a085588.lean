import Mathlib

/-!
# A085588: Eventual period of a single cell in rule 150 cellular automaton in a cyclic universe of width n.

Source: https://oeis.org/A085588
Credit: @Solfanbtc

Rule 150 on a cycle of `n` cells (`n ≥ 3`, offset 3): every cell becomes the sum mod 2 of
itself and its two neighbours. Starting from a single live cell, the orbit is eventually
periodic; `a(n)` is its eventual period, the least `p > 0` with `x_{t+p} = x_t` for some `t`.
A309786(n) is the length of the cycle reached by the trajectory of `1/n` under
`f(x) = min(2x, 2 - 2x)` (same notion of eventual period), A007814(n) = `padicValNat 2 n`,
and A115770 is the set of `k` with `7k = 11 ⊗ k`, `⊗` the carryless base-2 product.
We checked by computer that these definitions give a(3..44) as in %S, %T.

Conjectures (Roman Khrabrov, 2024):
1. "It appears that 2^A007814(n) * (2^A309786(n) - 1) divides a(n)." Read literally this
   fails already at n = 4 (a(4) = 2, while 2^2 (2^1 - 1) = 4), and at every exception listed in
   the next comment of the entry (powers of 2, 6·2^k, 13·2^k, 37·2^k, ...). The intended claim
   (as for rule 90 in Martin–Odlyzko–Wolfram, Theorem 3.5, where the period divides this
   number, with equality except for the listed exceptions) is the converse divisibility:
   a(n) divides 2^A007814(n) * (2^A309786(n) - 1). Minimal fix used here: that direction. We
   checked it for 3 ≤ n ≤ 44 (equality fails exactly at n = 4, 6, 8, 12, 13, 16, 24, 26, 32,
   37, matching the entry's list of exceptions).
2. a(n) = n only if n belongs to A115770.
(The remaining remarks — the incomplete list of exceptions "and so on" and the 2D rule 34
observations about another automaton — are not part of this statement.)
-/

namespace OMA.S_oeis_a085588

/-- One step of rule 150 on `n` cells arranged in a cycle. -/
def step (n : ℕ) (s : ZMod n → ZMod 2) : ZMod n → ZMod 2 :=
  fun i => s (i - 1) + s i + s (i + 1)

/-- A single live cell. -/
def single (n : ℕ) : ZMod n → ZMod 2 := fun i => if i = 0 then 1 else 0

/-- `a(n)`: the eventual period of the orbit of a single cell. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | 0 < p ∧ ∃ t : ℕ, (step n)^[t + p] (single n) = (step n)^[t] (single n)}

/-- The map `f(x) = min(2x, 2 - 2x)`. -/
def f (x : ℚ) : ℚ := min (2 * x) (2 - 2 * x)

/-- A309786(n): the length of the cycle of the trajectory of `1/n` under `f`. -/
noncomputable def cycleLength (n : ℕ) : ℕ :=
  sInf {p : ℕ | 0 < p ∧ ∃ t : ℕ, f^[t + p] (1 / (n : ℚ)) = f^[t] (1 / (n : ℚ))}

/-- Carryless base-2 product (A048720). -/
def clmul (b c : ℕ) : ℕ :=
  (List.range (c + 1)).foldl (fun acc i => if c.testBit i then acc ^^^ (b <<< i) else acc) 0

/-- Khrabrov's conjectures (1 with the divisibility in the corrected direction). -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n ∣ 2 ^ padicValNat 2 n * (2 ^ cycleLength n - 1) ∧
    (a n = n → 7 * n = clmul 11 n) := by
  sorry

end OMA.S_oeis_a085588
