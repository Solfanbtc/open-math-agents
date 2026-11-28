import Mathlib

/-!
# A026672: a(n) = T(2n,n-1), T given by A026670.

Source: https://oeis.org/A026672
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Aug 08 2015, in the entry):
-(n+1)(n-6) a(n) + 2(4n^2-23n+3) a(n-1) + 3(-5n^2+33n-42) a(n-2) - 2(2n-3)(n-5) a(n-3) = 0.

Conventions.
* T = A026670, by its formula in that entry: T(n, k) is the number of paths from (0,0) to
  (n-k, k) in the directed graph on (i, j), i, j ≥ 0, with edges (i,j) -> (i+1,j),
  (i,j) -> (i,j+1), and (i,j) -> (i+1,j+1) when i = j. `P i j` counts paths to (i, j), so
  T(n,k) = P(n-k, k) and a(n) = T(2n, n-1) = P(n+1, n-1). This reproduces the rows of A026670
  (1; 1,1; 1,3,1; 1,4,4,1; 1,5,11,5,1; ...).
* Indexing. The entry's offset is 2, but the data 1, 5, 22, 94, ... are T(2n, n-1) for
  n = 1, 2, 3, ... (T(2,0) = 1, T(4,1) = 5, T(6,2) = 22): the offset label is off by one from
  the name. We follow the name, a(n) = T(2n, n-1). With this indexing Mathar's recurrence holds
  for all 4 ≤ n < 60 (python3); with the data shifted to offset 2 it fails already at n = 5,
  so the name's indexing is the one the conjecture is about.
* The recurrence involves a(n-3); it is stated for n ≥ 4 (all indices ≥ 1).
-/

namespace OMA.S_oeis_a026672

/-- Number of paths from (0,0) to (i,j) with steps E, N, and diagonal steps from the diagonal. -/
def P : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | i + 1, 0 => P i 0
  | 0, j + 1 => P 0 j
  | i + 1, j + 1 => P i (j + 1) + P (i + 1) j + if i = j then P i j else 0

/-- A026670: T(n, k) = P(n-k, k). -/
def T (n k : ℕ) : ℕ := P (n - k) k

/-- A026672: a(n) = T(2n, n-1). -/
def a (n : ℕ) : ℕ := T (2 * n) (n - 1)

theorem main : ∀ n : ℕ, 4 ≤ n →
    -((n : ℤ) + 1) * ((n : ℤ) - 6) * a n + 2 * (4 * (n : ℤ) ^ 2 - 23 * n + 3) * a (n - 1)
      + 3 * (-5 * (n : ℤ) ^ 2 + 33 * n - 42) * a (n - 2)
      - 2 * (2 * (n : ℤ) - 3) * ((n : ℤ) - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026672
