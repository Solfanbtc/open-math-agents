import Mathlib

/-!
# A054978: Gilbreath transform of the lucky numbers

Source: https://oeis.org/A054978
Credit: @Solfanbtc

A054978 is obtained from the sequence of lucky numbers (A000959) by taking iterated absolute
value differences of terms and extracting the leading diagonal (offset 0):
`a(n) = d^n(0)`, where `d^0(i) = L(i)` is the `i`-th lucky number (0-indexed, `L(0) = 1`) and
`d^(k+1)(i) = |d^k(i+1) - d^k(i)|`.

Conjecture (N. J. A. Sloane, May 07 2023, OEIS comment): apart from the initial term, all the
other terms are 0 or 2, i.e. `a(n) ∈ {0, 2}` for every `n ≥ 1`. (This is the lucky-number
analog of the Gilbreath–Proth conjecture, A036262.)

Lucky numbers (sieve): start from the odd numbers `1, 3, 5, 7, …` (stage `0`). At stage `k`,
let `r` be the element of index `k + 1` (0-indexed) of the current list and delete every `r`-th
element (1-indexed positions `r, 2r, …`); this gives stage `k + 1`. Each stage is encoded as a
function `ℕ → ℕ` listing its elements in increasing order: the `j`-th surviving element
(0-indexed) after deleting every `r`-th one is the element of old index `j + j / (r - 1)`.
Since `r ≥ 2k + 3`, stage `k + 1` agrees with stage `k` on indices `≤ 2k + 1`, so the element of
index `i` is final from stage `i` on, and `lucky i = stage i i` is the `i`-th lucky number.
`lucky 0..9 = 1, 3, 7, 9, 13, 15, 21, 25, 31, 33` as in A000959, and the transform below
reproduces all 105 data terms `a(0..104) = 1, 2, 2, 0, 0, 0, 2, 2, 2, 0, …` (checked with a
Python implementation of the same definitions).
-/

namespace OMA.S_oeis_a054978

/-- Stage `k` of the lucky sieve, as the increasing enumeration of the surviving numbers. -/
def stage : ℕ → ℕ → ℕ
  | 0 => fun i => 2 * i + 1
  | k + 1 => fun j => stage k (j + j / (stage k (k + 1) - 1))

/-- The `i`-th lucky number (A000959), 0-indexed: `lucky 0 = 1, lucky 1 = 3, lucky 2 = 7, …`. -/
def lucky (i : ℕ) : ℕ := stage i i

/-- Iterated absolute differences of the lucky numbers: `d 0 = lucky`,
`d (k+1) i = |d k (i+1) - d k i|`. -/
def d : ℕ → ℕ → ℕ
  | 0 => lucky
  | k + 1 => fun i => Int.natAbs ((d k (i + 1) : ℤ) - d k i)

/-- A054978: the leading diagonal `a(n) = d^n(0)`. -/
def a (n : ℕ) : ℕ := d n 0

/-- Sloane's conjecture: every term of A054978 after the initial one is `0` or `2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 0 ∨ a n = 2 := by
  sorry

end OMA.S_oeis_a054978
