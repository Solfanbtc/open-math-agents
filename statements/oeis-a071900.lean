import Mathlib

/-!
# A071900: 1/4 times the number of n X n 0..7 matrices with MM' mod 8 = I.

Source: https://oeis.org/A071900
Credit: @Solfanbtc

A071900(n) is `1/4` times the number of `n × n` matrices `M` over `ZMod 8` (entries `0..7`) with
`M * Mᵀ = 1` (that is, `MM' mod 8 = I`), and A071303(n) is `1/2` times the number of `n × n`
matrices over `ZMod 4` with `M * Mᵀ = 1`.

Conjecture (Michel Marcus, 2022): `A071900(n) = 2^(n(n-1)/2) * A071303(n)` for `n ≥ 1`.
The quotients are taken in `ℚ`, exactly as the definitions say (`1/4` and `1/2` times a count).
Checked: the listed data `1, 16, 1536, 786432, 2013265920` of A071900 and
`1, 8, 192, 12288, 1966080` of A071303 satisfy the identity for `n = 1..5`, and `#eval` of
`orthCount` gives `orthCount 8 1 = 4`, `orthCount 4 1 = 2`, `orthCount 4 2 = 16`,
`orthCount 8 2 = 64`, matching `4 a(1)`, `2 A071303(1)`, `2 A071303(2)`, `4 a(2)`.
-/

namespace OMA.S_oeis_a071900

/-- The number of `n × n` matrices `M` over `ZMod m` with `M * Mᵀ = 1`. -/
def orthCount (m n : ℕ) [NeZero m] : ℕ :=
  (Finset.univ.filter fun M : Matrix (Fin n) (Fin n) (ZMod m) => M * M.transpose = 1).card

/-- A071900(n). -/
def a (n : ℕ) : ℚ := (orthCount 8 n : ℚ) / 4

/-- A071303(n). -/
def b (n : ℕ) : ℚ := (orthCount 4 n : ℚ) / 2

/-- The conjecture: `A071900(n) = 2^(n(n-1)/2) * A071303(n)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 2 ^ (n * (n - 1) / 2) * b n := by
  sorry

end OMA.S_oeis_a071900
