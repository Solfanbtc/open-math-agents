import Mathlib

/-!
# A092687: First column and main diagonal of triangle A092686, in which the convolution of each row with {1,2} produces a triangle that, when flattened, equals the flattened form of A092686.

Source: https://oeis.org/A092687
Credit: @Solfanbtc

Conjecture (Vaclav Kotesovec, Jun 29 2015): Limit n->infinity a(n)^(1/n) = 3.

Definition. The triangle A092686 is given in its entry by
  T(n, k) = 2*T(n-1, k) + T(n-1, k+1) for 0 <= k < n, T(n, n) = T(n, 0), T(0, 0) = 1,
with T(n-1, n) = 0 (outside the triangle), as in the PARI program of both entries. `row n` is
the list [T(n,0), ..., T(n,n)], and `a n = T(n, 0)` (offset 0). This reproduces all 27 data terms
1, 2, 6, 16, 46, 132, 384, ... (`#eval`), and agrees with Paul D. Hanna's recurrence
a(n) = Sum_{k=0..floor(n/2)} C(n-k,k) 2^(n-2k) a(k) on those terms.
-/

namespace OMA.S_oeis_a092687

/-- Row `n` of the triangle A092686: `[T(n,0), ..., T(n,n)]`. -/
def row : ℕ → List ℕ
  | 0 => [1]
  | (n + 1) =>
    let r := row n
    let new := (List.range (n + 1)).map fun k => 2 * r.getD k 0 + r.getD (k + 1) 0
    new ++ [new.headD 0]

/-- A092687(n) = T(n, 0). -/
def a (n : ℕ) : ℕ := (row n).headD 0

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n)) Filter.atTop (nhds 3) := by
  sorry

end OMA.S_oeis_a092687
