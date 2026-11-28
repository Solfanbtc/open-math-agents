import Mathlib

/-!
# A090906: Row lengths of the irregular triangle defined in A090905.

Source: https://oeis.org/A090906
Credit: @Solfanbtc

Conjecture (OEIS A090906, also in A090904, A090905, A090907): for `n > 4` the last term of
the `n`-th group is `2 p`, where `p` is the largest prime in the `(n-1)`-th group; and these
`p` are the Bertrand primes (A006992).

The triangle (A090905): the natural numbers are cut into consecutive groups
`(1), (2), (3,4), (5,...,8), (9,...,14), (15,...,26), ...`, each group being as short as
possible such that its product is a multiple of the product of the previous group.

Formalization.
* `rowData i = (start, length)` of group `i + 1` (OEIS rows are 1-indexed). Group 1 is `(1)`;
  group `i + 2` starts right after group `i + 1` and has the least length `k ≥ 1` such that the
  product of group `i + 1` divides the product of the `k` numbers starting there. Groups are
  nonempty (`k ≥ 1`; otherwise the empty product would make group 2 empty).
  The least `k` is found by a search over `1 ≤ k ≤ s + L - 1` (`s`, `L` the start and length of
  the previous group): `k = s + L - 1` always works, since `k!` divides any product of `k`
  consecutive integers and the previous product `(s + L - 1)! / (s - 1)!` divides `k!`;
  so the bounded search returns the true minimum and the fallback value is never reached
  except when it is itself the minimum.
  (The Mathematica program in A090905 starts its search at the previous length; python3
  confirms the minimum over all `k ≥ 1` is the same on the first 18 groups.)
* `bertrand j` is A006992(j + 1): `2`, then the largest prime `< 2 * previous`.
* For `n > 4`: with group `n` = `rowData (n - 1)` and group `n - 1` = `rowData (n - 2)`, the
  greatest prime `p` of group `n - 1` exists, the last term of group `n` is `2 p`, and
  `p = A006992(n - 1)` (group 4 = `(5,...,8)` has largest prime `7 = A006992(4)`).

Checked with python3: the lengths reproduce the listed terms of A090906 up to 39864
(18 groups), and the conjecture holds for `5 ≤ n ≤ 18`.
-/

namespace OMA.S_oeis_a090906

/-- Product of the `k` consecutive integers `t, t + 1, ..., t + k - 1`. -/
def blockProd (t k : ℕ) : ℕ := ∏ i ∈ Finset.range k, (t + i)

/-- `rowData i = (start, length)` of the `(i + 1)`-th group of the triangle of A090905. -/
def rowData : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | i + 1 =>
    let s := (rowData i).1
    let L := (rowData i).2
    let k := ((List.range' 1 (s + L - 1)).find?
      (fun k => decide (blockProd s L ∣ blockProd (s + L) k))).getD (s + L - 1)
    (s + L, k)

/-- `bertrand j` is A006992(j + 1): `2, 3, 5, 7, 13, 23, ...`. -/
def bertrand : ℕ → ℕ
  | 0 => 2
  | j + 1 => Nat.findGreatest Nat.Prime (2 * bertrand j - 1)

/-- For `n > 4`, the last term of group `n` is twice the largest prime `p` of group `n - 1`,
and `p` is the Bertrand prime A006992(n - 1). -/
theorem main : ∀ n : ℕ, 4 < n →
    ∃ p : ℕ, IsGreatest {q : ℕ | q.Prime ∧ (rowData (n - 2)).1 ≤ q ∧
        q < (rowData (n - 2)).1 + (rowData (n - 2)).2} p ∧
      (rowData (n - 1)).1 + (rowData (n - 1)).2 - 1 = 2 * p ∧
      p = bertrand (n - 2) := by
  sorry

end OMA.S_oeis_a090906
