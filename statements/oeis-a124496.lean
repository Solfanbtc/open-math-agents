import Mathlib

/-!
# A124496: Triangle read by rows: T(n,k) is the number of set partitions of {1,2,...,n} in which the size of the last block is k, 1<=k<=n; the blocks are ordered with increasing least elements.

Source: https://oeis.org/A124496
Credit: @Solfanbtc

Conjectures (R. J. Mathar, Mar 13 2016): T(n,n-3) = A000096(n). T(n,n-4) = A055831(n+1).

Definitions.
* Set partitions of {1..n} with blocks ordered by increasing least elements correspond
  bijectively to restricted growth strings s_1 ... s_n (s_1 = 0, s_i ≤ 1 + max(s_1..s_(i-1))),
  s_i being the index of the block containing i; the last block is the one with index
  max(s), and its size is the number of i with s_i = max(s). T(n, k) (1 ≤ k ≤ n, offset 1)
  counts strings whose last block has size k; this reproduces all 66 data terms (python3,
  `#eval` for n ≤ 6), e.g. T(4,2) = 4.
* A000096(m) = m(m+3)/2 (offset 0) and A055831(m) = (m-3)(m^2+6m-10)/6 (offset 4, the formula
  of that entry, which matches its data).

Index fix for the first conjecture. With the offsets of this entry, T(n, n-3) for n = 4, 5, 6, ...
is 9, 14, 20, 27, ... = A000096(n-1), while A000096(n) = 14, 20, 27, ... (already at n = 4:
T(4,1) = 9 ≠ 14 = A000096(4)). Mathar's first formula is the one for 0-based row and column
indices (T(n+1, k+1) in our indexing), so we state it as T(n, n-3) = A000096(n-1) for n ≥ 4.
The second conjecture holds as written with the entry's indexing: T(n, n-4) = A055831(n+1) for
n ≥ 5 (both checked with python3 for n ≤ 11).
-/

namespace OMA.S_oeis_a124496

/-- Restricted growth string. -/
def IsRGS (s : List ℕ) : Prop :=
  ∀ i ∈ Finset.range s.length, s.getD i 0 ≤ ((s.take i).map (· + 1)).foldl max 0

instance : DecidablePred IsRGS := fun s => by unfold IsRGS; infer_instance

/-- Size of the last block. -/
def lastSize (s : List ℕ) : ℕ := s.count (s.foldl max 0)

/-- A124496: T(n, k). -/
def T (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin n)).filter fun f =>
    IsRGS (List.ofFn fun i => (f i : ℕ)) ∧ lastSize (List.ofFn fun i => (f i : ℕ)) = k).card

/-- A000096(m) = m(m+3)/2. -/
def A000096 (m : ℕ) : ℕ := m * (m + 3) / 2

/-- A055831(m) = (m-3)(m^2+6m-10)/6, m ≥ 4. -/
def A055831 (m : ℕ) : ℕ := (m - 3) * (m ^ 2 + 6 * m - 10) / 6

theorem main :
    (∀ n : ℕ, 4 ≤ n → T n (n - 3) = A000096 (n - 1)) ∧
    (∀ n : ℕ, 5 ≤ n → T n (n - 4) = A055831 (n + 1)) := by
  sorry

end OMA.S_oeis_a124496
