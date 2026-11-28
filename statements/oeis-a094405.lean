import Mathlib

/-!
# A094405: a(1) = 1; a(n) = (sum of previous terms) mod n.

Source: https://oeis.org/A094405
Credit: @Solfanbtc

For a seed `s`, let `a(1) = s` and `a(n) = (a(1) + ⋯ + a(n-1)) mod n` for `n ≥ 2`. Here `S s n`
is the partial sum `a(1) + ⋯ + a(n)` (`S s 1 = s`) and `term s n = a(n)`. For `s = 1` this is
A094405, which is constant (= 97) from `n = 397` on (J. W. Layman's theorem in the entry).
Checked with python3: `s = 1` reproduces the data 1, 1, 2, 0, 4, 2, 3, 5, ...

Conjecture (Z. Seidov, 2006; verified for seeds 1..941): for any seed `a(1)` the sequence ends
with a repeating constant. `main` states this for every seed `s ≥ 0`. (`s = 0` is trivially all
zeros. python3: every seed `s ≤ 1000` becomes constant.)
-/

namespace OMA.S_oeis_a094405

/-- `S s n = a(1) + ⋯ + a(n)` for the seed `s` (`n ≥ 1`; `S s 0 = 0`). -/
def S (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => s
  | n + 2 => S s (n + 1) + S s (n + 1) % (n + 2)

/-- `term s n = a(n)`: `a(1) = s`, `a(n) = S(n-1) mod n` for `n ≥ 2`. -/
def term (s n : ℕ) : ℕ := if n ≤ 1 then s else S s (n - 1) % n

theorem main : ∀ s : ℕ, ∃ N c : ℕ, ∀ n : ℕ, N ≤ n → term s n = c := by
  sorry

end OMA.S_oeis_a094405
