import Mathlib

/-!
# A091508: least k with b(k) = 1, b(1) = n, b(k+1) = b(k)+k+1 or b(k)/gcd(k+1, b(k)).

Source: https://oeis.org/A091508
Credit: @Solfanbtc

For `n ≥ 1`, `b(1) = n` and `b(k+1) = b(k) + k + 1` if `gcd(k+1, b(k)) = 1`, otherwise
`b(k+1) = b(k) / gcd(k+1, b(k))`. `a(n)` is the least `k` with `b(k) = 1`. Here
`c n j = b(j+1)`, so `c n 0 = n` and `c n (j+1)` is computed from `c n j` with `k = j + 1`.
E.g. `a(6) = 3` (`6, 3, 1`), `a(3) = 111`.

Conjecture (Benoit Cloitre): `a(n)` always exists, i.e. for every `n ≥ 1` some `b(k) = 1`.
(After that the sequence continues `1, k0+1, 1, k0+2, …`.) Sam Chapman reports it verified for
`n ≤ 10^15`. Checked with python3: the definition reproduces the 25 listed terms, and every
`n ≤ 10^5` reaches `1` (within 247 steps).
-/

namespace OMA.S_oeis_a091508

/-- `c n j = b(j+1)` for the sequence started at `b(1) = n`. -/
def c (n : ℕ) : ℕ → ℕ
  | 0 => n
  | j + 1 =>
    let g := Nat.gcd (j + 2) (c n j)
    if g = 1 then c n j + (j + 2) else c n j / g

/-- The conjecture: for every `n ≥ 1` the sequence reaches `1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ j : ℕ, c n j = 1 := by
  sorry

end OMA.S_oeis_a091508
