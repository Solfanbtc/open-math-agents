import Mathlib

/-!
# A006351: Number of series-parallel networks with n labeled edges. Also called yoke-chains by Cayley and MacMahon.

Source: https://oeis.org/A006351
Credit: @Solfanbtc

Conjecture (Mikhail Kurkov): a(n) = A379459(n-2,0) = A379460(n-1,0) for n > 1 with a(1) = 1.

Formalization notes:
* A006351 has offset 1: a(1) = 1, a(2) = 2, a(3) = 8, a(4) = 52, a(5) = 472, ...
  We use the classical identity recorded in the entry, a(n) = 2 * A000311(n) for n ≥ 2
  (a series-parallel network with at least two edges is either of series type or of parallel
  type, and each type is counted by the total partitions of the edge set, Schröder's fourth
  problem). The value `a 0` is a junk value and is never used.
* `schroeder n` is A000311(n), the number of total partitions of an `n`-set (labeled
  series-reduced rooted trees with `n` leaves): A000311(1) = 1, and for `n ≥ 2` a total
  partition is a set partition of `[n]` into at least two blocks, each block carrying a total
  partition. Splitting off the block containing the first element (size `k+1`, its other `k`
  elements chosen among the remaining `n+1` when the set has `n+2` elements), the rest of size
  `m = n+1-k ≥ 1` carries any set partition into blocks each with a total partition; these are
  counted by 1 if `m = 1` and by `2 * A000311(m)` if `m ≥ 2` (one block or at least two).
* A379459 is the array with A(0,k) = 2*(k+1)! and
  A(n,k) = A(n-1,k+1) + 2*(k+1)! * Sum_{j=0..k} A(n-1,j)/j!. Because of the division by `j!`
  it is defined over `ℚ` (the source asserts integer entries; we compare in `ℚ`).
* A379460 is the array with A(0,k) = 1, A(n,0) = A(n-1,0) + A(n-1,1) and
  A(n,k) = A(n,k-1) + (k+1)*(A(n-1,k) + A(n-1,k+1)) for n, k ≥ 1.
* All three identities were checked with exact arithmetic for n ≤ 13 (both arrays agree with
  1, 2, 8, 52, 472, 5504, 78416, 1320064, 25637824, 564275648, ...).
-/

namespace OMA.S_oeis_a006351

/-- A000311: the number of total partitions of an `n`-set (Schröder's fourth problem). -/
def schroeder : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => ∑ k : Fin (n + 1),
      Nat.choose (n + 1) k * schroeder (k + 1) *
        (if n + 1 - k = 1 then 1 else 2 * schroeder (n + 1 - k))
decreasing_by all_goals omega

/-- A006351: the number of series-parallel networks with `n` labeled edges (offset 1). -/
def a (n : ℕ) : ℕ := if n = 1 then 1 else 2 * schroeder n

/-- The array A379459: A(0,k) = 2*(k+1)!,
A(n,k) = A(n-1,k+1) + 2*(k+1)! * Sum_{j=0..k} A(n-1,j)/j!. -/
def A379459 : ℕ → ℕ → ℚ
  | 0, k => 2 * (k + 1).factorial
  | (n + 1), k => A379459 n (k + 1) +
      2 * (k + 1).factorial * ∑ j ∈ Finset.range (k + 1), A379459 n j / j.factorial

/-- The array A379460: A(0,k) = 1, A(n,0) = A(n-1,0) + A(n-1,1),
A(n,k) = A(n,k-1) + (k+1)*(A(n-1,k) + A(n-1,k+1)). -/
def A379460 : ℕ → ℕ → ℕ
  | 0, _ => 1
  | (n + 1), 0 => A379460 n 0 + A379460 n 1
  | (n + 1), (k + 1) => A379460 (n + 1) k + (k + 2) * (A379460 n (k + 1) + A379460 n (k + 2))

theorem main :
    a 1 = 1 ∧
    ∀ n : ℕ, 1 < n →
      ((a n : ℚ) = A379459 (n - 2) 0 ∧ a n = A379460 (n - 1) 0) := by
  sorry

end OMA.S_oeis_a006351
