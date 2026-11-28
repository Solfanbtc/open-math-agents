import Mathlib

/-!
# A144406: Rectangular array A read by upward antidiagonals: entry A(n,k) in row n and column k gives the number of compositions of k in which no part exceeds n, n>=1, k>=0.

Source: https://oeis.org/A144406
Credit: @Solfanbtc

Claim (entry comment, L. Edson Jeffery, 2013): "Since the array row sequences successively tend
to A000079, the absolute values of nonzero differences between two successive row sequences tend
to A045623 = {1, 2, 5, 12, 28, 64, 144, 320, 704, 1536, ...}".

Reading. Rows n and n+1 agree for k ≤ n (both count all compositions of k, A(n,k) = 2^(k-1) for
1 ≤ k ≤ n), and differ from k = n+1 on. So the nonzero differences between rows n and n+1 form
the sequence j ↦ |A(n+1, n+1+j) - A(n, n+1+j)|, j ≥ 0, and the claim is that for each j this
tends to A045623(j) as n → ∞ (the comment writes "as k → infinity", but the differences for fixed
j depend on n only; along the row index they become eventually equal to A045623(j)). The premise
(rows tend to 1, 1, 2, 4, 8, ..., i.e. A(n,k) → 2^(k-1) for k ≥ 1) is included as a first
conjunct. A045623: a(0) = 1, a(j) = (j+3)·2^(j-2) for j ≥ 1 (entry formula), written
(j+3)·2^j/4. A python check: the array reproduces all 91 listed terms, and the differences agree
with A045623(j) for all j ≤ n - 1 (checked n ≤ 13, j < 12).
-/

namespace OMA.S_oeis_a144406

/-- A(n,k): compositions of k with no part exceeding n. -/
def A (n k : ℕ) : ℕ := (Finset.univ.filter fun c : Composition k => ∀ p ∈ c.blocks, p ≤ n).card

/-- A045623. -/
def A045623 (j : ℕ) : ℕ := if j = 0 then 1 else (j + 3) * 2 ^ j / 4

theorem main :
    (∀ k : ℕ, 1 ≤ k → Filter.Tendsto (fun n : ℕ => A n k) Filter.atTop (nhds (2 ^ (k - 1)))) ∧
    ∀ j : ℕ, Filter.Tendsto (fun n : ℕ => ((A (n + 1) (n + 1 + j) : ℤ) - A n (n + 1 + j)).natAbs)
      Filter.atTop (nhds (A045623 j)) := by
  sorry

end OMA.S_oeis_a144406
