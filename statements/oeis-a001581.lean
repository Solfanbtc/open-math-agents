import Mathlib

/-!
# A001581: Winning moves in Fibonacci nim.

Source: https://oeis.org/A001581
Credit: @Solfanbtc

The game: a pile of `n` stones; a move removes a positive Fibonacci number of stones
(`1, 2, 3, 5, 8, ...`); the last player to move wins. A001581 lists the positive positions
`n` that are losses for the player to move (zeros of the nim function A014588), i.e. the
winning positions to move to: `4, 10, 14, 20, 24, ..., 138, 150, 160, ...` (offset 1).

Conjecture (Simon Plouffe, 1992 dissertation, as recorded in the entry): the generating function
`∑_{n ≥ 0} A001581(n+1) z^n` equals
`2(1 + z)(3z^5 + 2z^3 + z^2 + z + 2) / ((z^6 + z^5 + z^4 + z^3 + z^2 + z + 1)(z - 1)^2)`.

Status: REFUTED in the entry itself (Boon Suan Ho, Oct 07 2023): the expansion agrees up to
`138 z^26` but its coefficient of `z^27` is `144`, while `A001581(28) = 150`. A python3 check
confirms this (rational function coefficients 4, 10, ..., 132, 138, 144, 148, ...). The claim is
stated here exactly as conjectured, so that it can be disproved.

Conventions:
* `a n` is 0-indexed: `a n = A001581(n + 1)`, so `a 0 = 4`; the generating function uses
  `z^n ↦ a n`, matching "138z^26" for `A001581(27) = 138`.
* The rational function is written without division: the formal power series `A` of `a`
  satisfies `A * D = N` in `ℚ⟦X⟧`, where `D` and `N` are the denominator and numerator. Since `D`
  has constant coefficient `1`, this is equivalent to `A = N / D`.
-/

namespace OMA.S_oeis_a001581

/-- `d` is a positive Fibonacci number (`Nat.fib k` for some `k`; `fib (d + 1) ≥ d` bounds `k`). -/
def isFib (d : ℕ) : Bool := (List.range (d + 2)).any fun k => Nat.fib k == d

/-- `lose n`: the player to move from a pile of `n` stones loses (a P-position):
no move `n ↦ m` with `m < n` and `n - m` a positive Fibonacci number reaches a P-position. -/
def lose (n : ℕ) : Bool :=
  (List.range n).attach.all fun ⟨m, hm⟩ =>
    have : m < n := List.mem_range.mp hm
    !(isFib (n - m) && lose m)
termination_by n

/-- `a n = A001581(n + 1)`: the `n`-th (0-indexed) positive P-position. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => 0 < m ∧ lose m = true) n

/-- Denominator `(z^6 + z^5 + z^4 + z^3 + z^2 + z + 1)(z - 1)^2`. -/
noncomputable def D : PowerSeries ℚ :=
  (PowerSeries.X ^ 6 + PowerSeries.X ^ 5 + PowerSeries.X ^ 4 + PowerSeries.X ^ 3 +
    PowerSeries.X ^ 2 + PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2

/-- Numerator `2(1 + z)(3z^5 + 2z^3 + z^2 + z + 2)`. -/
noncomputable def N : PowerSeries ℚ :=
  2 * (1 + PowerSeries.X) *
    (3 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 2 + PowerSeries.X + 2)

/-- Plouffe's conjectured generating function for A001581 (refuted: coefficient of `z^27`). -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) * D = N := by
  sorry

end OMA.S_oeis_a001581
