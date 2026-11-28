import Mathlib

/-!
# A008687: Number of 1's in 2's complement representation of -n

Source: https://oeis.org/A008687
Credit: @Solfanbtc

`a(n)` (offset 0) is the number of 1's in the two's complement representation of `-n`, written
with the least number of bits: for `n ≥ 1` this is `w = ⌈log₂ n⌉ + 1` bits (the least `w` with
`-2^(w-1) ≤ -n`), and the bit pattern is the binary expansion of `2^w - n`; `a(0) = 0`.
E.g. `-3 = 101₂` (`w = 3`), so `a(3) = 2`. This reproduces all 96 data terms and agrees with the
entry's recurrence `a(n) = a(⌈n/2⌉) + n mod 2` (`n ≥ 2`) for `n < 3000`.

Stern–Brocot (Farey) tree fractions `A007305(n)/A007306(n)` (offset 0):
`0/1, 1/1, 1/2, 1/3, 2/3, 1/4, 2/5, 3/5, 3/4, …`. For `n ≥ 2` they are the nodes of the
Stern–Brocot subtree of `(0, 1)` in breadth-first order: write `n - 1` in binary as `1 b₁ … b_r`;
start from the bounds `0/1`, `1/1` and the node `1/2` (their mediant), and for each bit `bᵢ`
replace the upper bound (`bᵢ = 0`, left child) or the lower bound (`bᵢ = 1`, right child) by the
current node, the new node being the mediant of the bounds. This reproduces all listed terms of
A007305 and A007306 (as reduced fractions).

Hirzebruch (negative) continued fraction: `x = b₁ - 1/(b₂ - 1/(⋯ - 1/b_k))` with integers
`bᵢ`, `bᵢ ≥ 2` for `i ≥ 2`. Every rational has exactly one such expansion (the tail value is
`> 1`, so `b₁ = ⌈x⌉` and so on), and its length is `k`.

Conjecture (Andrei Zabolotskii, Apr 17 2020, OEIS comment): `a(n) + 1` is the length of the
Hirzebruch continued fraction of `A007305(n)/A007306(n)`.

Minimal fix: the claim fails at the trivial index `n = 1`: the fraction is `1/1 = [1]`, of length
`1`, while `a(1) + 1 = 2`. It holds for `n = 0` (`0 = [0]`, `a(0) + 1 = 1`) and, by a Python
check, for every `2 ≤ n < 3000`. So it is stated for all `n ≠ 1`. The statement asserts that an
expansion of length `a(n) + 1` exists and that every expansion has that length.
-/

namespace OMA.S_oeis_a008687

/-- Number of 1's in the binary expansion of `m`. -/
def popcount (m : ℕ) : ℕ := (Nat.digits 2 m).count 1

/-- A008687: number of 1's in the (minimal-width) two's complement representation of `-n`. -/
def a (n : ℕ) : ℕ := if n = 0 then 0 else popcount (2 ^ (Nat.clog 2 n + 1) - n)

/-- One step down the Stern–Brocot tree: `(lo, hi, node)` and a bit. -/
def step (s : ℚ × ℚ × ℚ) (b : ℕ) : ℚ × ℚ × ℚ :=
  let lo := if b = 0 then s.1 else s.2.2
  let hi := if b = 0 then s.2.2 else s.2.1
  (lo, hi, ((lo.num + hi.num : ℤ) : ℚ) / ((lo.den + hi.den : ℕ) : ℚ))

/-- The Stern–Brocot tree fraction `A007305(n)/A007306(n)`. -/
def sb (n : ℕ) : ℚ :=
  if n = 0 then 0 else if n = 1 then 1 else
    -- binary digits of `n - 1` below the leading `1`, most significant first
    (((Nat.digits 2 (n - 1)).reverse.drop 1).foldl step ((0 : ℚ), (1 : ℚ), (1 / 2 : ℚ))).2.2

/-- Value of the negative continued fraction `b₁ - 1/(b₂ - 1/(⋯ - 1/b_k))`. -/
def hjEval : List ℤ → ℚ
  | [] => 0
  | [b] => b
  | b :: l => b - 1 / hjEval l

/-- An admissible Hirzebruch expansion: nonempty, all entries after the first are `≥ 2`. -/
def Admissible (l : List ℤ) : Prop := l ≠ [] ∧ ∀ b ∈ l.tail, 2 ≤ b

/-- Zabolotskii's conjecture, for `n ≠ 1` (it fails at `n = 1`, see the module docstring). -/
theorem main : ∀ n : ℕ, n ≠ 1 →
    (∃ l : List ℤ, Admissible l ∧ hjEval l = sb n ∧ l.length = a n + 1) ∧
    (∀ l : List ℤ, Admissible l → hjEval l = sb n → l.length = a n + 1) := by
  sorry

end OMA.S_oeis_a008687
