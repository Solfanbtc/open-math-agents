import Mathlib

/-!
# A113703: the retrograde trajectory of 10 under A111273 is not periodic

Source: https://oeis.org/A113703 (with https://oeis.org/A111273)
A111273 (offset 1): `g(n)` is the smallest divisor of the triangular number `T(n) = n(n+1)/2` not
already in the sequence: 1, 3, 2, 5, 15, 7, 4, 6, 9, 11, 22, ... It is a permutation of the
positive integers (proof in A111273). A113703 (offset 0) is the retrograde trajectory of 10
under `k ↦ g(k)`: `b(0) = 10` and `b(n+1) = g⁻¹(b(n))`, the `m` with `g(m) = b(n)`:
10, 19, 18, 27, 26, 39, 38, 56, 111, ...
Conjecture of the entry: "Sequence is not periodic."

We state: there is no period `p > 0` with `b(n + p) = b(n)` for all `n`.

Conventions. `gList n = [g(1), ..., g(n)]`; the next term is found among `1, ..., T(n)` (every
divisor of `T(n) ≥ 1` is there). `g⁻¹(v)` is taken as the least `m ≥ 1` with `g(m) = v` (`sInf`),
which is the preimage since `g` is a permutation.
Checked with python3: the definition of `g` reproduces the 69 listed terms of A111273, and the
backward orbit reproduces the 56 listed terms of A113703.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a113703

/-- `gList n = [g(1), ..., g(n)]` for A111273. -/
def gList : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let l := gList n
    let T := (n + 1) * (n + 2) / 2
    l ++ [((List.range' 1 T).find? (fun d => d ∣ T ∧ d ∉ l)).getD 0]

/-- A111273: `g(n)`, the smallest divisor of `T(n)` not among `g(1), ..., g(n-1)`. -/
def g (n : ℕ) : ℕ := (gList n).getD (n - 1) 0

/-- The preimage of `v` under the permutation `g`. -/
noncomputable def gInv (v : ℕ) : ℕ := sInf {m : ℕ | 1 ≤ m ∧ g m = v}

/-- A113703: the retrograde trajectory of 10 under `g`. -/
noncomputable def b : ℕ → ℕ
  | 0 => 10
  | n + 1 => gInv (b n)

theorem main : ¬ ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, b (n + p) = b n := by
  sorry

end OMA.S_oeis_a113703
