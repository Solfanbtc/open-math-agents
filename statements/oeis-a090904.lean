import Mathlib

/-!
# A090904: Row products of the irregular triangle defined in A090905.

Source: https://oeis.org/A090904
Credit: @Solfanbtc

The triangle of A090905 splits the positive integers into consecutive blocks (rows, numbered
from 1): row 1 is (1), and row `n + 1` starts right after row `n` and has the least length
`L ≥ 1` such that its product is a multiple of the product of row `n`:
(1), (2), (3,4), (5,...,8), (9,...,14), (15,...,26), ... (such an `L` exists, since `L`
consecutive integers include a multiple of any number `≤ L`). A090904 lists the row products.
We checked by computer that this rule gives the 8 listed products and the row starts of
A090905.

Conjecture (Amarnath Murthy, 2003): for `n > 4` the last term of row `n` is `2p`, where `p` is
the largest prime in row `n - 1`; "and these are the Bertrand primes": the largest primes of
the rows 4, 5, 6, ... are 7, 13, 23, 43, 83, ..., each being the largest prime below twice the
previous one (A006992). We checked both parts for rows up to 15.
-/

namespace OMA.S_oeis_a090904

/-- The product `s (s+1) ⋯ (s+L-1)`. -/
def blockProd (s L : ℕ) : ℕ := ∏ i ∈ Finset.range L, (s + i)

/-- `row k = (start, length)` of row `k + 1`. -/
noncomputable def row : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 =>
      let s := (row k).1 + (row k).2
      (s, sInf {L : ℕ | 0 < L ∧ blockProd (row k).1 (row k).2 ∣ blockProd s L})

/-- The last term of row `n` (`n ≥ 1`). -/
noncomputable def last (n : ℕ) : ℕ := (row (n - 1)).1 + (row (n - 1)).2 - 1

/-- The largest prime in row `n` (`n ≥ 1`). -/
noncomputable def maxPrime (n : ℕ) : ℕ :=
  sSup {p : ℕ | p.Prime ∧ (row (n - 1)).1 ≤ p ∧ p ≤ last n}

/-- Murthy's conjecture. -/
theorem main :
    (∀ n : ℕ, 4 < n → last n = 2 * maxPrime (n - 1)) ∧
    (∀ m : ℕ, 4 ≤ m → maxPrime (m + 1) = sSup {q : ℕ | q.Prime ∧ q < 2 * maxPrime m}) := by
  sorry

end OMA.S_oeis_a090904
