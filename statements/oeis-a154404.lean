import Mathlib

/-!
# A154404: Number of ways to express n as the sum of an odd prime, a positive Fibonacci number and a Catalan number.

Source: https://oeis.org/A154404
Credit: @Solfanbtc

`a(n) = |{(p, s, t) : p + F_s + C_t = n, p an odd prime, s > 1}|` (`F_s` Fibonacci, `C_t` Catalan;
the count takes `t ≥ 1`, so the Catalan value `1` is counted once). Example: `a(7) = 3` from
`3 + 2 + 2`, `3 + 3 + 1`, `5 + 1 + 1`.

Conjecture (Qing-Hu Hou and Jiang Zeng, Jan 09 2009, prizes offered; verified up to `5 · 10⁸` by
the authors and up to `5 · 10¹³` by D. S. McNeil): `a(n) > 0` for every `n = 5, 6, ...`, i.e.
every integer `n ≥ 5` is the sum of an odd prime, a positive Fibonacci number and a Catalan
number. We state this existence claim (`Nat.fib s` with `s ≥ 1` runs over all positive
Fibonacci numbers; `catalan t` over all Catalan numbers).

Check (python3): the counting definition reproduces the first 33 data terms, and every
`5 ≤ n < 20000` has a representation.
-/

namespace OMA.S_oeis_a154404

/-- Every `n ≥ 5` is an odd prime plus a positive Fibonacci number plus a Catalan number. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ∃ p s t : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ s ∧ n = p + Nat.fib s + catalan t := by
  sorry

end OMA.S_oeis_a154404
