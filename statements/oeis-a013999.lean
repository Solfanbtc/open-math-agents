import Mathlib

/-!
# A013999: acyclic orientations of the complement of a path graph

Source: https://oeis.org/A013999
Credit: @Solfanbtc

A013999 (offset 0): "From applying the 'rational mean' to the number e"; data 1, 1, 2, 8, 42, 258,
1824, 14664, … We define it by the entry's explicit formula (E. Munarini)
`a(n) = Sum_{k=0..floor((n+1)/2)} binomial(n-k+1, k) (-1)^k (n-k+1)!`, which reproduces the data.
(The entry's g.f. `Sum_{m>=0} m! (x(1-x))^m` has coefficients 1, 1, 1, 2, 8, 42, …, i.e. it is the
g.f. of `1, a(0), a(1), …`, one index off from the data; we do not use it.)

Conjecture (M. Rubey, Oct 15 2023): "this is also the number of acyclic orientations of the
complement of the path graph."

Index. Matching the data, the graph is the complement of the path on `n + 1` vertices: for
`n + 1 = 1, 2, 3, 4` the complements have 0, 0, 1, 3 edges (the last one a path) and 1, 1, 2, 8
acyclic orientations, which are `a(0), …, a(3)`; with `n` vertices instead the counts would be
1, 1, 1, 2, …, off by one. `main` states: for every `n`, the complement of `pathGraph (n + 1)` has
exactly `a(n)` acyclic orientations. Checked with python3 by brute force for `n + 1 ≤ 8`
(1, 1, 2, 8, 42, 258, 1824, 14664).

Orientations. An orientation of a simple graph `G` is a Boolean relation `r` such that `r u v`
only for adjacent `u, v` and, for each edge, exactly one of `r u v`, `r v u` holds; it is acyclic
if no vertex reaches itself along `r` (`Relation.TransGen`).
-/

namespace OMA.S_oeis_a013999

/-- A013999 by Munarini's formula. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range ((n + 1) / 2 + 1),
    ((n - k + 1).choose k : ℤ) * (-1) ^ k * ((n - k + 1).factorial : ℤ)

/-- `r` is an orientation of `G`. -/
def IsOrientation {m : ℕ} (G : SimpleGraph (Fin m)) (r : Fin m → Fin m → Bool) : Prop :=
  (∀ u v, r u v = true → G.Adj u v) ∧ (∀ u v, G.Adj u v → (r u v = true ↔ r v u = false))

/-- `r` has no directed cycle. -/
def IsAcyclic {m : ℕ} (r : Fin m → Fin m → Bool) : Prop :=
  ∀ v, ¬ Relation.TransGen (fun x y => r x y = true) v v

/-- The number of acyclic orientations of `G`. -/
noncomputable def numAcyclicOrientations {m : ℕ} (G : SimpleGraph (Fin m)) : ℕ :=
  {r : Fin m → Fin m → Bool | IsOrientation G r ∧ IsAcyclic r}.ncard

/-- Rubey's conjecture: the complement of the path graph on `n + 1` vertices has `a(n)` acyclic
orientations. -/
theorem main : ∀ n : ℕ, (numAcyclicOrientations (SimpleGraph.pathGraph (n + 1))ᶜ : ℤ) = a n := by
  sorry

end OMA.S_oeis_a013999
