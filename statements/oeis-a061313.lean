import Mathlib

/-!
# A061313: a(n) + 2 is the sum of the Hirzebruch continued fraction of the n-th Stern-Brocot fraction

Source: https://oeis.org/A061313
Credit: @Solfanbtc

A061313 (offset 1): `a(n)` is the minimal number of steps to get from 1 to `n` by (a) subtracting
1 or (b) multiplying by 2. Data 0, 1, 3, 2, 5, 4, 4, 3, 7, …

Conjecture (A. Zabolotskii, Apr 17 2020): "a(n)+2 is the sum of the terms of the Hirzebruch
(negative) continued fraction for the Stern-Brocot tree fraction A007305(n)/A007306(n)."

The fractions. A007305/A007306 (offset 0) list the Stern-Brocot subtree in `[0, 1]`:
`0/1, 1/1, 1/2, 1/3, 2/3, 1/4, 2/5, 3/5, 3/4, 1/5, …`: after `0/1, 1/1`, level `k + 1` lists the
`2^k` mediants of consecutive fractions of level `k` (level 0 is `0/1, 1/1`, each level being
the previous one with these mediants inserted), so index `n = 2^k + 1 + i` (`0 ≤ i < 2^k`) is
the `i`-th mediant of consecutive fractions of level `k` (`k = floor(log_2(n - 1))`). The Hirzebruch (negative) continued fraction of `x` is
`x = b_1 - 1/(b_2 - 1/(b_3 - …))` with `b_j = ⌈x_j⌉`, `x_1 = x`, `x_{j+1} = 1/(b_j - x_j)`, stopping
when `x_j` is an integer. For `x = p/q` the denominators strictly decrease, so at most `q`
steps occur; we run the algorithm with `q + 1` steps of fuel.

Minimal fix. At `n = 1` the fraction is `1/1`, whose expansion is `[1]` with sum `1`, while
`a(1) + 2 = 2`; so the identity fails at the first term (under the standard convention) and
`main` states it for `n ≥ 2`. Checked with python3: it holds for `2 ≤ n < 5000`, and fails only
at `n = 1` in that range.
-/

namespace OMA.S_oeis_a061313

/-- The numbers reachable from 1 in exactly `k` steps of `x ↦ x - 1` or `x ↦ 2x`. (In `ℕ`,
`0 - 1 = 0`; from `0` or negative numbers no positive number is reachable, so this is harmless.) -/
def reach : ℕ → Set ℕ
  | 0 => {1}
  | k + 1 => {y | ∃ x ∈ reach k, y = x - 1 ∨ y = 2 * x}

/-- A061313: the minimal number of steps from 1 to `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | n ∈ reach k}

/-- The mediant of two fractions given as (numerator, denominator). -/
def mediant (x y : ℕ × ℕ) : ℕ × ℕ := (x.1 + y.1, x.2 + y.2)

/-- Insert the mediant between consecutive fractions. -/
def refine : List (ℕ × ℕ) → List (ℕ × ℕ)
  | a :: b :: rest => a :: mediant a b :: refine (b :: rest)
  | l => l

/-- Level `k` of the Stern-Brocot subtree in `[0, 1]`. -/
def level : ℕ → List (ℕ × ℕ)
  | 0 => [(0, 1), (1, 1)]
  | k + 1 => refine (level k)

/-- `A007305(n)/A007306(n)` as a (numerator, denominator) pair, for `n ≥ 1`. -/
def sbFrac (n : ℕ) : ℕ × ℕ :=
  if n ≤ 1 then (1, 1)
  else
    let k := Nat.log 2 (n - 1)
    (List.zipWith mediant (level k) (level k).tail).getD (n - 1 - 2 ^ k) (0, 1)

/-- The terms of the Hirzebruch continued fraction of `x`, with `fuel` steps. -/
def hjTerms : ℕ → ℚ → List ℤ
  | 0, _ => []
  | fuel + 1, x =>
    let b := ⌈x⌉
    if (b : ℚ) = x then [b] else b :: hjTerms fuel (1 / (b - x))

/-- The sum of the terms of the Hirzebruch continued fraction of `p/q`. -/
def hjSum (pq : ℕ × ℕ) : ℤ := (hjTerms (pq.2 + 1) ((pq.1 : ℚ) / pq.2)).sum

/-- Zabolotskii's conjecture (for `n ≥ 2`). -/
theorem main : ∀ n : ℕ, 2 ≤ n → (a n : ℤ) + 2 = hjSum (sbFrac n) := by
  sorry

end OMA.S_oeis_a061313
