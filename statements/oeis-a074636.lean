import Mathlib

/-!
# A074636: Define b(k) by the recursion b(1)=n, b(k+1)=b(k)-floor(k/b(k)). Sequence gives the value a(n) such that b(a(n))=0; if k>a(n) then b(k) is undefined.

Source: https://oeis.org/A074636
Credit: @Solfanbtc

For a starting value `n ≥ 1`, `b(1) = n` and `b(k+1) = b(k) - ⌊k / b(k)⌋` over the integers.
The trajectory may pass through negative values before reaching 0: for `n = 2` it is
2, 2, 1, -2, 0, so `a(2) = 5`, as in the data and in the Maple and Mathematica programs, which
iterate until `b = 0` with floor division. `a(n)` is the index `k` with `b(k) = 0`; after that
`b(k+1)` would divide by zero ("undefined").

Here `traj n j = b(j + 1)`, with `Int.fdiv` the floor division on `ℤ`. Checked with python3:
the first zero of this recursion is at index `j + 1 = a(n)` for the 56 listed terms.

Conjecture (B. Cloitre): `a(n)` is always defined, i.e. for every `n ≥ 1` the trajectory
reaches 0. `main` states this. (R. Israel's b-file gives `a(n)` for all `n ≤ 2000`; some
`n ≤ 5000` need more than 10^7 steps.)
-/

namespace OMA.S_oeis_a074636

/-- `traj n j = b(j + 1)` for the starting value `b(1) = n`. -/
def traj (n : ℕ) : ℕ → ℤ
  | 0 => n
  | j + 1 => traj n j - Int.fdiv ((j : ℤ) + 1) (traj n j)

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ j : ℕ, traj n j = 0 := by
  sorry

end OMA.S_oeis_a074636
