import Mathlib

/-!
# A078109: Let u(1)=u(2)=1, u(3)=2n, u(k) = abs(u(k-1)-u(k-2)-u(k-3)) and M(k) = Max_{1<=i<=k} u(i), then for any k >= a(n), M(k) = floor(sqrt(k + A078108(n))).

Source: https://oeis.org/A078109
Credit: @Solfanbtc

For a third initial value `t`, let `u(1) = u(2) = 1`, `u(3) = t`,
`u(k) = |u(k-1) - u(k-2) - u(k-3)|` for `k ≥ 4`, and `M(k) = max_{1 ≤ i ≤ k} u(i)`.
With `t = 2n`, A078108(n) is the integer `y` and A078109(n) the least `k₀` such that
`M(k) = ⌊√(k + y)⌋` for all `k ≥ k₀` (`y` is unique when it exists, since `⌊√(k + y)⌋`
jumps exactly when `k + y` is a square). This reproduces every term of the data of A078109 and
of A078108 (checked in Python, `k` up to `4·10^5`).

Conjecture (Benoit Cloitre, in the entry):
1. `a(n)` always exists and `a(n)/n²` is bounded: there is `C` such that for every `n ≥ 1`
   there are `y` and `k₀ ≤ C n²` with `M(k) = ⌊√(k + y)⌋` for all `k ≥ k₀` (since `a(n)` is
   the least such `k₀`, this is exactly "a(n) exists for all n and a(n) ≤ C n²"). We let `y`
   range over `ℤ` (the entry only asks that some integer works; the observed values are
   positive); `⌊√(k + y)⌋` is `Nat.sqrt` of `(k + y).toNat`, which is the floor square root
   whenever `k + y ≥ 0`, as it is for all large `k`.
2. With `t = 2n + 1` instead, `u` eventually reaches a 2-cycle: `u(k + 2) = u(k)` for all
   large `k` (cf. A078098; a constant tail, a degenerate 2-cycle, is allowed by this reading).
   Checked in Python for `1 ≤ n < 200`.
-/

namespace OMA.S_oeis_a078109

/-- `u t k`: the sequence `u(1) = u(2) = 1`, `u(3) = t`, `u(k) = |u(k-1) - u(k-2) - u(k-3)|`.
Position `0` is unused (set to `1`). -/
def u (t : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => t
  | k + 4 => ((u t (k + 3) : ℤ) - u t (k + 2) - u t (k + 1)).natAbs

/-- `M(k) = max_{1 ≤ i ≤ k} u(i)`. -/
def M (t k : ℕ) : ℕ := (Finset.Icc 1 k).sup (u t)

theorem main :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∃ y : ℤ, ∃ k₀ : ℕ, (k₀ : ℝ) ≤ C * (n : ℝ) ^ 2 ∧
      ∀ k : ℕ, k₀ ≤ k → M (2 * n) k = Nat.sqrt ((k : ℤ) + y).toNat) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, ∀ k : ℕ, m ≤ k → u (2 * n + 1) (k + 2) = u (2 * n + 1) k) := by
  sorry

end OMA.S_oeis_a078109
