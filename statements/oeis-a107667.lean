import Mathlib

/-!
# A107667: Triangular matrix T, read by rows, that satisfies: T = D + SHIFT_LEFT(T^2) where SHIFT_LEFT shifts each row 1 place to the left and D is the diagonal matrix {1, 2, 3, ...}.

Source: https://oeis.org/A107667
Credit: @Solfanbtc

Conjecture (Mikhail Kurkov, Jun 02 2026, %F line of A107667):
`T(n+m, m) = (n+m+1) * P(n+1, n+1, m)`, where
`P(n, k, m) = P(n-1, k, m) + (n+m) * P(n, k-1, m)` for `1 < k < n`, with `P(n, 1, m) = 1` and
`P(n, n, m) = (n+m) * P(n, n-1, m)`.

Formalization.
* `T` is lower triangular (`0 ≤ k ≤ n`, rows and columns from `0`). `T = D + SHIFT_LEFT(T^2)`
  reads entrywise `T(n, n) = n + 1` and, for `k < n`,
  `T(n, k) = (T^2)(n, k+1) = ∑_{i = k+1}^{n} T(n, i) * T(i, k+1)` (as in the Haskell program).
  This determines `T` row by row, each row from right to left: `rowAux rows n s` is the list
  `[T(n, n-s), ..., T(n, n)]`, built from the previous rows `rows` and the entries of row `n`
  already computed; `table n` is the list of rows `0..n`.
* `P m n k` is Kurkov's `P(n, k, m)`, defined for `1 ≤ k ≤ n`. The rule `P(n, 1, m) = 1` is
  applied first, so `P(1, 1, m) = 1` (the diagonal rule is used only for `n ≥ 2`; this is the
  reading that gives `T(m, m) = m + 1`). Values outside `1 ≤ k ≤ n` are set to `0`; they are
  never reached from `P(n+1, n+1, m)`.
* The conjecture is stated for all `n, m ≥ 0`.

Checked with python3: `T` reproduces all listed %S/%T/%U terms, and the conjecture holds for
`n + m ≤ 16`; `#eval` of these Lean definitions agrees on the first rows.
-/

namespace OMA.S_oeis_a107667

/-- Entry `(i, j)` of a list of rows (`0` if absent). -/
def getT (rows : List (List ℕ)) (i j : ℕ) : ℕ := (rows.getD i []).getD j 0

/-- `rowAux rows n s = [T(n, n-s), ..., T(n, n)]`, given `rows = [row 0, ..., row (n-1)]`. -/
def rowAux (rows : List (List ℕ)) (n : ℕ) : ℕ → List ℕ
  | 0 => [n + 1]
  | s + 1 =>
    let acc := rowAux rows n s
    let k := n - (s + 1)
    (∑ i ∈ Finset.Icc (k + 1) n,
      acc.getD (i - (k + 1)) 0 * (if i = n then acc.getD 0 0 else getT rows i (k + 1))) :: acc

/-- `table n = [row 0, ..., row n]` of the triangle `T`. -/
def table : ℕ → List (List ℕ)
  | 0 => [[1]]
  | n + 1 => table n ++ [rowAux (table n) (n + 1) (n + 1)]

/-- A107667: `T(n, k)` for `0 ≤ k ≤ n`. -/
def T (n k : ℕ) : ℕ := getT (table n) n k

/-- Kurkov's auxiliary array: `P m n k = P(n, k, m)`. -/
def P (m : ℕ) : ℕ → ℕ → ℕ
  | n, k =>
    if _hk0 : k = 0 then 0
    else if k = 1 then 1
    else if n < k then 0
    else if _hkn : k = n then (n + m) * P m n (n - 1)
    else P m (n - 1) k + (n + m) * P m n (k - 1)
termination_by n k => n + k
decreasing_by all_goals omega

/-- Kurkov's conjecture: `T(n+m, m) = (n+m+1) * P(n+1, n+1, m)`. -/
theorem main : ∀ n m : ℕ, T (n + m) m = (n + m + 1) * P m (n + 1) (n + 1) := by
  sorry

end OMA.S_oeis_a107667
