import Mathlib

/-!
# A055778: Number of 1's in the base-phi representation of n.

Source: https://oeis.org/A055778
Credit: @Solfanbtc

Conjecture (Dale Gerdemann, OEIS A055778): for all n, A007895(n) <= a(n), where A007895(n) is
the number of terms in the Zeckendorf representation of n; equality holds at 1, 7, 18, 19, 47,
48, 54, 123, 124, 130, 141, 142, 322, 323, 329, 340, 341, 369, 370, 376, 843, 844, 850, 861,
862, 890, 891, 897, 966, 967, 973, 984, 985, 2207, 2208, 2214, 2225, 2226, 2254, 2255, 2261,
2330, 2331, 2337, 2348, 2349, 2529, 2530, 2536, 2547, 2548, 2576, 2577, 2583, ...
Status: the entry records a proof by Jeffrey Shallit (automata: Bellman-Ford on the weighted graph
derived from his automaton "saka"), so this is a known result, stated faithfully.

Definitions.
* The base-phi (Bergman) representation of n: a finite set S of integers, no two consecutive,
  with n = Σ_{i ∈ S} phi^i (phi the golden ratio). It exists and is unique (Bergman 1957);
  a(n) = |S|. `main` includes the existence, so that the statement is not vacuous.
* A007895(n) = the length of Mathlib's `Nat.zeckendorf n`.
* The listed equality cases are read as: for 1 <= n <= 2583 (the last listed value), equality
  holds exactly at the listed n (the list is the beginning of the equality set).
Checked numerically (exact arithmetic in Z[phi]): the listed terms of A055778 are reproduced, the
inequality holds for n < 2600, and the equality cases in 1..2583 are exactly the listed ones.
-/

namespace OMA.S_oeis_a055778

/-- `S` is the base-phi representation of `n`. -/
def IsBasePhiRep (n : ℕ) (S : Finset ℤ) : Prop :=
  (∀ i ∈ S, i + 1 ∉ S) ∧ ∑ i ∈ S, Real.goldenRatio ^ i = (n : ℝ)

/-- The listed equality cases. -/
def equalityCases : Finset ℕ :=
  {1, 7, 18, 19, 47, 48, 54, 123, 124, 130, 141, 142, 322, 323, 329, 340, 341, 369, 370, 376,
   843, 844, 850, 861, 862, 890, 891, 897, 966, 967, 973, 984, 985, 2207, 2208, 2214, 2225,
   2226, 2254, 2255, 2261, 2330, 2331, 2337, 2348, 2349, 2529, 2530, 2536, 2547, 2548, 2576,
   2577, 2583}

theorem main :
    (∀ n : ℕ, ∃ S : Finset ℤ, IsBasePhiRep n S) ∧
    (∀ n : ℕ, ∀ S : Finset ℤ, IsBasePhiRep n S →
      (Nat.zeckendorf n).length ≤ S.card ∧
      (1 ≤ n → n ≤ 2583 → ((Nat.zeckendorf n).length = S.card ↔ n ∈ equalityCases))) := by
  sorry

end OMA.S_oeis_a055778
