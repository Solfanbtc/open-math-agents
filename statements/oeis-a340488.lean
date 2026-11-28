import Mathlib

/-!
# A340488: a(n+1) = XOR(a(n),y) for n>=1, where y is the number of m < n such that a(m) = a(n);
a(1)=0.

Source: https://oeis.org/A340488
Credit: @Solfanbtc

The precise conjectures of the entry, stated as one conjunction (`main`):

* (`CountBound`; entry comment.) "It appears that among the first 4^n terms, each integer value
  less than 2^n appears at least (3/4)*2^n times." (For all `n ≥ 0`; written `4·count ≥ 3·2^n`.)
* (`YConjecture`; Rémy Sigrist, Jan 10 2021.) The "y" sequence, `y(n) = #{m < n : a(m) = a(n)}`
  for `n ≥ 1`, is A336033: `A336033(n)` is the number of `k` with `1 ≤ k < n` and
  `A336033(k) XOR ... XOR A336033(n-1) = 0`, `n ≥ 1`.
* (`ZerosConjecture`; Sigrist.) The positions of the 0's are given by A336190 (offset 0), where
  `A336190(i)` is the least `k` such that `A336033(k) = i`: the `i`-th zero of A340488
  (counting from `i = 0`) is at position `A336190(i)`.
* (`PeriodConjecture`; Sigrist.) For a fixed `k > 0`, let `b(n)` be the position of the `k`-th
  occurrence of `n`. Then `b(n) - A340494(n)` has period `2^m` for some `m`, where A340494(n)
  (offset 0) is the index where `n` first appears, i.e. the `k = 1` case of `b`.
* (`PiConjecture`; N. J. A. Sloane, Jan 13 2021.) With `π_i(n)` the number of occurrences of `i`
  among the first `n` terms, `π_0(n) ≥ π_i(n)` for all `i`, and the first time `π_0(n) = m`,
  `π_i(n) < m` for `i > 0`. The second part fails trivially for `m = 0` (at `n = 0` every
  `π_i(0) = 0`); the minimal fix, used here, is `m ≥ 1`.

Not stated: the vague self-similarity remark ("the graph of the first n terms is similar to the
graph of the first n/4 terms"), and the conjectured generating function of A340494 (a statement
about A340494, not about this sequence's terms).

Positions of occurrences use `Nat.nth`; it is meaningful because `CountBound` (part of the
conjunction) implies that every value occurs infinitely often.

A python check over the first `4^9` terms confirms all five parts (periods `1, 4, 8, 8` for
`k = 2, 3, 4, 5`; `y = A336033` and the zero positions for the first 200000 terms).
-/

namespace OMA.S_oeis_a340488

/-- `aList n = [a(1), ..., a(n)]`. -/
def aList : ℕ → List ℕ
  | 0 => []
  | 1 => [0]
  | n + 2 =>
      let l := aList (n + 1)
      let x := l.getLastD 0
      l ++ [x ^^^ l.dropLast.count x]

/-- `a n` is the `n`-th term (`n ≥ 1`). -/
def a (n : ℕ) : ℕ := (aList n).getD (n - 1) 0

/-- `y n = #{m < n : a(m) = a(n)}` (`m ≥ 1`), so that `a(n+1) = a(n) XOR y(n)`. -/
def y (n : ℕ) : ℕ := (aList (n - 1)).count (a n)

/-- `a336033List n = [A336033(1), ..., A336033(n)]`. -/
def a336033List : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
      let l := a336033List n
      l ++ [((List.range n).filter fun j => (l.drop j).foldl (· ^^^ ·) 0 = 0).length]

/-- A336033(n), `n ≥ 1`. -/
def a336033 (n : ℕ) : ℕ := (a336033List n).getD (n - 1) 0

/-- `π_i(n)`: the number of occurrences of `i` among the first `n` terms. -/
def piCount (i n : ℕ) : ℕ := (aList n).count i

/-- Position of the `k`-th occurrence (`k ≥ 1`) of the value `v`. -/
noncomputable def occ (k v : ℕ) : ℕ := Nat.nth (fun p => 1 ≤ p ∧ a p = v) (k - 1)

def CountBound : Prop :=
  ∀ n v : ℕ, v < 2 ^ n → 3 * 2 ^ n ≤ 4 * piCount v (4 ^ n)

def YConjecture : Prop := ∀ n : ℕ, 1 ≤ n → y n = a336033 n

def ZerosConjecture : Prop :=
  ∀ i : ℕ, IsLeast {k : ℕ | 1 ≤ k ∧ a336033 k = i} (occ (i + 1) 0)

def PeriodConjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ m : ℕ, ∀ n : ℕ,
    (occ k (n + 2 ^ m) : ℤ) - occ 1 (n + 2 ^ m) = (occ k n : ℤ) - occ 1 n

def PiConjecture : Prop :=
  (∀ n i : ℕ, piCount i n ≤ piCount 0 n) ∧
  ∀ n m : ℕ, 1 ≤ m → piCount 0 n = m → (∀ n' < n, piCount 0 n' ≠ m) →
    ∀ i : ℕ, 0 < i → piCount i n < m

theorem main :
    CountBound ∧ YConjecture ∧ ZerosConjecture ∧ PeriodConjecture ∧ PiConjecture := by
  sorry

end OMA.S_oeis_a340488
