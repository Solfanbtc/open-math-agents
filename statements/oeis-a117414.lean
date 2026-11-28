import Mathlib

/-!
# A117414: An Euler triangle.

Source: https://oeis.org/A117414
Credit: @Solfanbtc

Conjectures in the entry:
1. (Paul Barry) the row sums are the Euler numbers A000364 (1, 1, 5, 61, 1385, ...).
2. (Geoffrey Critzer, Apr 26 2023) T(n,k) is the number of alternating permutations of [2n] with
   exactly k cyclically alternating components, where w_1 < w_2 > w_3 < ... > w_(2n-1) < w_(2n)
   is alternating and its cyclically alternating decomposition is obtained by taking the largest
   i with w_(2i) > w_1, cutting off w_1, ..., w_(2i) as the first component, and repeating on
   w_(2i+1), ..., w_(2n).

Definitions.
* The triangle. The entry gives no definition other than its data and Critzer's e.g.f.
  Sum_{n,k} T(n,k) u^k z^n / B(n) = E((u-1) z) / E(-z), with B(n) = A000680(n) = (2n)!/2^n and
  E(z) = Sum_n z^n / B(n); we define T by this e.g.f.:
  T(n,k) = B(n) Sum_{m=k..n} C(m,k) (-1)^(m-k) / B(m) * d(n-m), where Sum_j d(j) z^j = 1/E(-z).
  This reproduces all 45 data terms (python3, `#eval`).
* A000364 by the recurrence of the Euler (secant) numbers:
  A(0) = 1, A(n) = (-1)^(n+1) Sum_{k<n} (-1)^k C(2n, 2k) A(k).
* Alternating permutations of [2n] are taken on the values 0, ..., 2n-1 (order-isomorphic),
  as permutations of `Fin (2n)` read as the word w_1 ... w_(2n); the number of components is
  computed by the decomposition rule above (`comps`).
* python3: conjecture 1 for n ≤ 8, conjecture 2 for n ≤ 5.
-/

namespace OMA.S_oeis_a117414

/-- B(n) = (2n)!/2^n (A000680). -/
def B (n : ℕ) : ℚ := ((2 * n).factorial : ℚ) / 2 ^ n

/-- `dlist m = [d 0, ..., d (m-1)]`, the coefficients of 1/E(-z). -/
def dlist : ℕ → List ℚ
  | 0 => []
  | m + 1 =>
    let L := dlist m
    L ++ [if m = 0 then 1 else
      -(∑ i ∈ Finset.Icc 1 m, (-1 : ℚ) ^ i / B i * L.getD (m - i) 0)]

/-- The coefficient of z^m in 1/E(-z). -/
def d (m : ℕ) : ℚ := (dlist (m + 1)).getD m 0

/-- A117414: T(n, k). -/
def T (n k : ℕ) : ℚ :=
  B n * ∑ m ∈ Finset.Icc k n, ((m.choose k : ℚ) * (-1) ^ (m - k) / B m) * d (n - m)

/-- `eulerList n = [A000364(0), ..., A000364(n-1)]`. -/
def eulerList : ℕ → List ℤ
  | 0 => []
  | n + 1 =>
    let L := eulerList n
    L ++ [if n = 0 then 1 else
      (-1) ^ (n + 1) * ∑ k ∈ Finset.range n, (-1) ^ k * ((2 * n).choose (2 * k) : ℤ) * L.getD k 0]

/-- A000364(n). -/
def A000364 (n : ℕ) : ℤ := (eulerList (n + 1)).getD n 0

/-- `w` is alternating: w_1 < w_2 > w_3 < ... (0-indexed: rises at even positions). -/
def IsAlt (w : List ℕ) : Prop :=
  ∀ j ∈ Finset.range (w.length - 1), if j % 2 = 0 then w.getD j 0 < w.getD (j + 1) 0
    else w.getD (j + 1) 0 < w.getD j 0

instance : DecidablePred IsAlt := fun w => by unfold IsAlt; infer_instance

/-- Number of cyclically alternating components (with fuel `f ≥ length`). -/
def compsAux : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | f + 1, a :: rest =>
    let l := a :: rest
    match ((List.range l.length).filter fun j => j % 2 = 1 ∧ a < l.getD j 0).getLast? with
    | none => 1
    | some j => 1 + compsAux f (l.drop (j + 1))

/-- Number of cyclically alternating components of `w`. -/
def comps (w : List ℕ) : ℕ := compsAux w.length w

/-- The word of a permutation of `Fin m`. -/
def word {m : ℕ} (σ : Equiv.Perm (Fin m)) : List ℕ := List.ofFn fun i => (σ i).val

/-- Alternating permutations of [2n] with exactly `k` cyclically alternating components. -/
def count (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin (2 * n)))).filter fun σ =>
    IsAlt (word σ) ∧ comps (word σ) = k).card

theorem main :
    (∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), T n k = (A000364 n : ℚ)) ∧
    (∀ n k : ℕ, k ≤ n → (count n k : ℚ) = T n k) := by
  sorry

end OMA.S_oeis_a117414
