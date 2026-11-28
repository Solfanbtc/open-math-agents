import Mathlib

/-!
# A126198: Triangle read by rows: T(n,k) (1 <= k <= n) = number of compositions of n into parts of size <= k.

Source: https://oeis.org/A126198
Credit: @Solfanbtc

Conjecture (L. Edson Jeffery, Nov 29 2013): `Sum_{k=1..n} T(n,k) = A039671(n)` for `n > 0`.

Formalized:
* `T n k` is the number of compositions of `n` (Mathlib's `Composition n`: ordered lists of
  positive parts summing to `n`) all of whose parts are `≤ k`.
* A039671(n) is the sum `Sum_{m=0..n} F(n,m)` of row `n` of the "postage stamp" array of
  A007059 up to the main diagonal, where (A007059, comment of Richard L. Ollerton)
  `F(n,m) = F(n-1,m) + F(n-2,m) + ... + F(n-m,m)` with `F(0,m) = 1`, `F(n,m) = 0` for `n < 0`
  and `F(n,0) = 0` for `n > 0`. Rows `n < 0` are omitted: `postage (n+1) m` sums
  `F(i, m)` over the indices `0 ≤ i ≤ n` with `n + 1 - i ≤ m`, i.e. the terms `F(n+1-j, m)`,
  `1 ≤ j ≤ m`, whose row is `≥ 0`. A039671 data: 1, 1, 3, 8, 21, 53, 130, ...
* `main`: for every `n > 0`, `∑_{k=1}^{n} T n k = a039671 n`.
-/

namespace OMA.S_oeis_a126198

/-- `T n k`: the number of compositions of `n` into parts of size `≤ k`. -/
def T (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun c : Composition n => ∀ b ∈ c.blocks, b ≤ k).card

/-- The "postage stamp" array `F(n,m)` of A007059 (rows `n ≥ 0`). -/
def postage : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, m => ∑ i : Fin (n + 1), if n + 1 - i.val ≤ m then postage i.val m else 0
termination_by n => n
decreasing_by exact i.isLt

/-- A039671(n): row sums up to the main diagonal of the postage stamp array. -/
def a039671 (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), postage n m

theorem main : ∀ n : ℕ, 0 < n → ∑ k ∈ Finset.Icc 1 n, T n k = a039671 n := by
  sorry

end OMA.S_oeis_a126198
