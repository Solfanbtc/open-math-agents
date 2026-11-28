import Mathlib

/-!
# A088519: 2-Golomb's sequence G(n,2).

Source: https://oeis.org/A088519
Credit: @Solfanbtc

A088519 is the earliest positive increasing sequence starting with `(1, 2)` such that the length
of the `n`-th run equals the `n`-th partial sum `A(n) = a(1) + … + a(n)`. Equivalently
(alternative definition in the entry): `a(1) = 1`, `a(2) = 2`, and `a(m) = n` for
`A(1) + … + A(n-1) < m ≤ A(1) + … + A(n)`. So `a(m)` is the least `n ≥ 1` with
`m ≤ S(n) := Σ_{j=1}^n A(j)`. For `m ≥ 3` this `n` is `< m` (`S(1) = 1`, `S(2) = 4`, and `S`
increases by at least 1 each step), so `a(m)` only depends on earlier terms. `L m` is the list
`[a(1), …, a(m)]`, built term by term.

The runs are `1, 2^3, 3^5, 4^7, 5^10, 6^13, 7^16, 8^19, 9^22, …` (example in the entry:
`a(1)+a(2)+a(3) = 5`, so the third run has five 3's). NOTE: the entry's data contains seventeen
7's, while the definition (both forms) gives `A(7) = 1+2+2+2+3+3+3 = 16`. The data has no
b-file, and the runs before and after (`8^19`, `9^22`) agree with the definition, so this looks
like a typo in the data. The statement follows the definition.

Conjecture (entry): `a(n) = (2+√2)^(1/(2+√2)) n^(√2-1) + O(1)`. (The asymptotic equivalence
`a(n) ~ (2+√2)^(1/(2+√2)) n^(√2-1)` is given as a formula.) Numerics with python3, from the
definition up to `n = 3·10^7`: `a(n) - (2+√2)^(1/(2+√2)) n^(√2-1)` stays in `[-0.6, 0.7]` for
`n ≤ 10^6`, but reaches about `-1.5` by `10^7` and `-2.3` by `3·10^7`. So the `O(1)` claim may
fail, but the numerics do not settle it.
-/

namespace OMA.S_oeis_a088519

open Asymptotics Filter

/-- `S_L(n) = Σ_{j=1}^n Σ_{i=1}^j a(i)`, computed from the list `L = [a(1), …]`. -/
def S (L : List ℕ) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range (j + 1), L.getD i 0

/-- `L m = [a(1), …, a(m)]`. -/
def L : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 2]
  | m + 3 =>
    let l := L (m + 2)
    l ++ [((List.range (m + 2)).map (· + 1) |>.find? (fun n => m + 3 ≤ S l n)).getD 0]

/-- A088519(m), for `m ≥ 1`. -/
def a (m : ℕ) : ℕ := (L m).getLastD 0

/-- The conjecture: `a(n) - (2+√2)^(1/(2+√2)) n^(√2-1)` is bounded. -/
theorem main :
    (fun n : ℕ => (a n : ℝ) -
      (2 + Real.sqrt 2) ^ (1 / (2 + Real.sqrt 2)) * (n : ℝ) ^ (Real.sqrt 2 - 1))
      =O[atTop] (fun _ => (1 : ℝ)) := by
  sorry

end OMA.S_oeis_a088519
