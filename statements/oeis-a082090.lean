import Mathlib

/-!
# A082090: Length of iteration sequence if function A056239, a pseudo-logarithm is iterated and started at n. Fixed point equals zero for all initial values.

Source: https://oeis.org/A082090
Credit: @Solfanbtc

`f = A056239`: for `n = ∏ p_k^(c_k)` (with `p_k` the `k`-th prime), `f n = ∑ k c_k`, i.e. the sum of
`π(p) · v_p(n)` over the prime factors `p` of `n`. `f 1 = 0`. For `n ≥ 1`, `a(n)` is the length
of the list `n, f n, f (f n), …, 0`, i.e. one more than the number of steps needed to reach 0.
For example `127, 31, 11, 5, 3, 2, 1, 0` gives `a(127) = 8`, and `a(1) = 2` (the Maple program).

Conjectures (G. Wiseman, Dec 01 2023), for `k ≥ 2`:
1. the first appearance of `k` is at `n = A007097(k-2)`, the primeth recurrence
   1, 2, 3, 5, 11, 31, 127, ... (`b(0) = 1`, `b(j+1) = ` the `b(j)`-th prime);
2. the last appearance of `k` is at `n = A014221(k-2) = 2^^(k-2)` (1, 2, 4, 16, 65536, ...);
3. the number of times `k` appears is 1, 1, 2, 8, 435, ... for `k = 2, 3, 4, 5, 6`.
`main` states all three (the counts for the five listed values).
Checked with python3 for `n ≤ 70000`: first appearances 1, 2, 3, 5, 11, 31 (`k = 2..7`), last
appearances 1, 2, 4, 16, 65536 (`k = 2..6`), counts 1, 1, 2, 8, 435.
-/

namespace OMA.S_oeis_a082090

/-- A056239: the sum of the prime indices of `n`, with multiplicity. -/
def f (n : ℕ) : ℕ := n.factorization.sum fun p e => e * Nat.primeCounting p

/-- `a n`: the length of the iteration list `n, f n, …, 0`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {j : ℕ | f^[j] n = 0} + 1

/-- A007097: `b 0 = 1`, `b (j+1)` is the `b j`-th prime. -/
noncomputable def primeth : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.nth Nat.Prime (primeth j - 1)

/-- A014221 (shifted): `tower 0 = 1`, `tower (j+1) = 2 ^ tower j`. -/
def tower : ℕ → ℕ
  | 0 => 1
  | j + 1 => 2 ^ tower j

/-- The positions `n ≥ 1` where `k` appears. -/
def positions (k : ℕ) : Set ℕ := {n | 1 ≤ n ∧ a n = k}

theorem main :
    (∀ k : ℕ, 2 ≤ k → IsLeast (positions k) (primeth (k - 2))) ∧
      (∀ k : ℕ, 2 ≤ k → IsGreatest (positions k) (tower (k - 2))) ∧
      ((positions 2).ncard = 1 ∧ (positions 3).ncard = 1 ∧ (positions 4).ncard = 2 ∧
        (positions 5).ncard = 8 ∧ (positions 6).ncard = 435) := by
  sorry

end OMA.S_oeis_a082090
