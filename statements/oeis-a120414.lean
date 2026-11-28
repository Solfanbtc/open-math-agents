import Mathlib

/-!
# A120414: a(0)=0, a(1)=1; thereafter a(n) = ceiling((3/2)^(n-3)*n*(n-1)).

Source: https://oeis.org/A120414
Credit: @Solfanbtc

`a(0) = 0`, `a(1) = 1`, and `a(n) = ⌈(3/2)^{n-3} n(n-1)⌉` for `n ≥ 2`:
`0, 1, 2, 6, 18, 45, 102, 213, 426, ...`.

Conjecture (the original definition of the entry, "Conjectured Ramsey number R(n,n)"): `a(n)` is
the diagonal Ramsey number `R(n, n)`, the least `N` such that every graph on `N` vertices has an
`n`-clique or an independent set of size `n`. Stated as `R(n, n) = a(n)` for all `n`.
(The entry notes that only `0, 1, 2, 6, 18` are proved; `43 ≤ R(5,5) ≤ 46` (Angeltveit and
McKay, 2024), consistent with `a(5) = 45`.)

A python3 check: the formula reproduces the data.

Conventions:
* `R(n, n) = sInf {N | ∀ G : SimpleGraph (Fin N), G has an n-clique or Gᶜ has an n-clique}`
  (an independent set of `G` is a clique of the complement `Gᶜ`); for `n = 0` this is `0`.
* `(3/2)^{n-3}` is computed in `ℚ` with an integer exponent (`n - 3` may be negative).
-/

namespace OMA.S_oeis_a120414

/-- The diagonal Ramsey number `R(n, n)`. -/
noncomputable def R (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ G : SimpleGraph (Fin N), ¬ G.CliqueFree n ∨ ¬ Gᶜ.CliqueFree n}

/-- `a n = A120414(n)`. -/
def a (n : ℕ) : ℕ :=
  if n ≤ 1 then n else (Int.ceil (((3 : ℚ) / 2) ^ ((n : ℤ) - 3) * n * (n - 1))).toNat

/-- The original conjecture: `R(n, n) = A120414(n)` for all `n`. -/
theorem main : ∀ n : ℕ, R n = a n := by
  sorry

end OMA.S_oeis_a120414
