import Mathlib

/-!
# A090905: Left side of irregular triangle of natural numbers in which every row product is a multiple of the previous.

Source: https://oeis.org/A090905
Credit: @Solfanbtc

The natural numbers are cut into rows of consecutive integers: (1), (2), (3, 4), (5, …, 8),
(9, …, 14), (15, …, 26), ... Row 1 is (1); each later row starts right after the previous one
and is the shortest run of consecutive integers whose product is a multiple of the previous row's
product. A090905(n) is the first term of row `n`. Here `row k = (start, length)` describes row
`k + 1`. Checked with python3 (via prime exponents): this reproduces the first 21 listed terms.

Conjecture (A. Murthy): for `n > 4`, the last term of row `n` is `2p`, where `p` is the largest
prime in row `n - 1`, "and these are the Bertrand primes". The second part is read as: the
largest prime of row `n` is the largest prime below `2p` (the Bertrand-prime recurrence, A006992).
`main` states both parts for `n > 4`. (python3: both hold for `5 ≤ n ≤ 21`; the first fails
at `n = 4`, whose last term is 8 while row 3 has largest prime 3.)
-/

namespace OMA.S_oeis_a090905

/-- Product of the `L` consecutive integers starting at `s`. -/
def runProd (s L : ℕ) : ℕ := ∏ i ∈ Finset.range L, (s + i)

/-- `row k = (start, length)` of row `k + 1`. -/
noncomputable def row : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 =>
    let r := row k
    let s := r.1 + r.2
    (s, sInf {M : ℕ | 1 ≤ M ∧ runProd r.1 r.2 ∣ runProd s M})

/-- Start of row `n` (`n ≥ 1`). -/
noncomputable def start (n : ℕ) : ℕ := (row (n - 1)).1

/-- Last term of row `n` (`n ≥ 1`). -/
noncomputable def last (n : ℕ) : ℕ := (row (n - 1)).1 + (row (n - 1)).2 - 1

/-- Primes in row `n`. -/
def rowPrimes (n : ℕ) : Set ℕ := {q | q.Prime ∧ start n ≤ q ∧ q ≤ last n}

theorem main :
    ∀ n p : ℕ, 4 < n → IsGreatest (rowPrimes (n - 1)) p →
      last n = 2 * p ∧
        ∃ q : ℕ, IsGreatest {x | x.Prime ∧ x < 2 * p} q ∧ IsGreatest (rowPrimes n) q := by
  sorry

end OMA.S_oeis_a090905
