import Mathlib

/-!
# A130287: a(n) = A121296(n) - A121263(n).

Source: https://oeis.org/A130287
Credit: @Solfanbtc

Descending dungeons (Applegate, LeBrun, Sloane, arXiv:math/0611293). Write `N_b` for the decimal
expansion of `N` read in base `b`, i.e. `Nat.ofDigits b (Nat.digits 10 N)` (all bases here are
`≥ 10`, so every decimal digit is a valid base-`b` digit).
* A121263(n) (alpha, offset 10) is `10_(11_(12_(..._n)))`, evaluated from the bottom upwards:
  start with `n` and, for `i = n-1, n-2, ..., 10`, replace the current value `b` by `i_b`
  (the step `i = 10` is harmless since `10_b = b`, as in the OEIS Maple program).
* A121296(n) (delta, offset 10) is `((n_(n-1))_(n-2))..._10`, read from the top downwards:
  start with `n` and, for `i = n-1, ..., 10`, replace the current value `t` by `t_i`
  (the OEIS Maple program of A121296).

A130287(n) = A121296(n) - A121263(n), offset 10.
Conjecture (OEIS A130287): all terms are `≥ 0`, i.e. `A121263(n) ≤ A121296(n)` for every `n ≥ 10`.
We state it as this inequality of natural numbers, since truncated subtraction on `ℕ` would make
`a(n) ≥ 0` trivial.

Checked by `#eval`: these definitions give A121296(n) - A121263(n) for `n = 10..29` equal to all
20 listed terms 0, 0, 0, 0, 0, 3, 14, 35, 87, 293, 4878, ..., 91930654519343922607883279072515432244874866615506797.
-/

namespace OMA.S_oeis_a130287

/-- `sub N b` is `N_b`: the decimal digits of `N` read in base `b`. -/
def sub (N b : ℕ) : ℕ := Nat.ofDigits b (Nat.digits 10 N)

/-- A121263(n) = `10_(11_(..._n))`, subscripts evaluated from the bottom upwards. -/
def alpha (n : ℕ) : ℕ := (List.range (n - 10)).foldl (fun b j => sub (n - 1 - j) b) n

/-- A121296(n) = `((n_(n-1))_(n-2))..._10`, subscripts read from the top downwards. -/
def delta (n : ℕ) : ℕ := (List.range (n - 10)).foldl (fun t j => sub t (n - 1 - j)) n

/-- Conjecture: A130287(n) = A121296(n) - A121263(n) ≥ 0 for all `n ≥ 10`. -/
theorem main : ∀ n : ℕ, 10 ≤ n → alpha n ≤ delta n := by
  sorry

end OMA.S_oeis_a130287
