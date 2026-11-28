import Mathlib

/-!
# A093875: Denominators in Kepler's tree of harmonic fractions.

Source: https://oeis.org/A093875
Credit: @Solfanbtc

Kepler's tree: begin with `1/1`, and give every node `i/j` two descendants `i/(i+j)` and
`j/(i+j)`. In breadth-first (heap) order node `1` is `1/1` and node `n` has children `2n`
(labelled `i/(i+j)`) and `2n+1` (labelled `j/(i+j)`), as in the entry's Mathematica program.
`a(n)` (offset 1) is the denominator of node `n`; the numerators are A093873.

A071585 (offset 0): `A071585(0) = 1`, and for `n ≥ 1`, `A071585(n)` is the numerator (in lowest
terms) of the continued fraction `[d_1; d_2, …, d_k]` where `4n = 2^{b_1} + ⋯ + 2^{b_k}` with
`b_1 > ⋯ > b_k`, `d_j = b_j - b_{j+1}` for `j < k` and `d_k = b_k` (the entry's %N, %C and
Mathematica program; e.g. `4·37 = 2^7 + 2^4 + 2^2`, `[3;2,2] = 17/5`, `A071585(37) = 17`).

Conjecture (Yosu Yurramendi, Jun 22 2016, %F of A093875; "conjecture of the comment in detail"):
`a(2n+1) = a(2n)` for `n > 0`; `a(2n+1) = A071585(n)` for `n ≥ 0`;
`a(2n) = A071585(n)` for `n > 0`.

Checked with `#eval`: `a(1..34)` and `A071585(0..40)` agree with the OEIS data.
-/

namespace OMA.S_oeis_a093875

/-- Node `n` of Kepler's tree as `(numerator, denominator)`; node `1` is `1/1`
(node `0` is not part of the tree; its value is irrelevant). -/
def node : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | 1 => (1, 1)
  | n + 2 =>
    let p := node ((n + 2) / 2)
    if (n + 2) % 2 = 0 then (p.1, p.1 + p.2) else (p.2, p.1 + p.2)
decreasing_by omega

/-- A093875: denominator of node `n` of Kepler's tree (`n ≥ 1`). -/
def a (n : ℕ) : ℕ := (node n).2

/-- Value of the finite continued fraction `[d_1; d_2, …, d_k]`. -/
def cfValue : List ℕ → ℚ
  | [] => 0
  | [d] => d
  | d :: e :: rest => d + 1 / cfValue (e :: rest)

/-- The partial quotients for `n`: differences of the binary exponents of `4n` (descending),
followed by the last exponent. -/
def quotients (n : ℕ) : List ℕ :=
  let b := (Nat.bitIndices (4 * n)).reverse
  (List.zipWith (fun x y => x - y) b b.tail) ++ [b.getLast?.getD 0]

/-- A071585 (offset 0). -/
def A071585 (n : ℕ) : ℤ :=
  if n = 0 then 1 else (cfValue (quotients n)).num

/-- Yurramendi's conjecture relating A093875 and A071585. -/
theorem main :
    (∀ n : ℕ, 0 < n → a (2 * n + 1) = a (2 * n)) ∧
    (∀ n : ℕ, (a (2 * n + 1) : ℤ) = A071585 n) ∧
    (∀ n : ℕ, 0 < n → (a (2 * n) : ℤ) = A071585 n) := by
  sorry

end OMA.S_oeis_a093875
