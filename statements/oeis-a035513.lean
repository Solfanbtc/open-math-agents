import Mathlib

/-!
# A035513: Wythoff array read by falling antidiagonals

Source: https://oeis.org/A035513
Credit: @Solfanbtc

The Wythoff array T(n,k) (rows n ≥ 1, columns k ≥ 1) is given in the entry by the formula
T(n,k) = Fib(k+1)*floor(n*tau) + Fib(k)*(n-1), where tau = (1+sqrt(5))/2 (Bottomley, 2001;
Kimberling, 1994, p. 314). Its first rows are 1, 2, 3, 5, 8, ...; 4, 7, 11, 18, ...;
6, 10, 16, 26, ...

Conjecture (Clark Kimberling, Jun 04 2025): if m ≥ 2, then the set
{(T(n,1), T(n,2)) mod m} (over all rows n ≥ 1) has cardinality m^2, i.e. every pair of
residues mod m occurs as (T(n,1) mod m, T(n,2) mod m) for some row n.

Formalization: residues mod m are taken in `ZMod m`; the set is the image of the rows n ≥ 1
under n ↦ (T(n,1), T(n,2)) cast to `ZMod m × ZMod m`, and its cardinality is `Set.ncard`.
-/

namespace OMA.S_oeis_a035513

open Real

/-- The Wythoff array: T(n,k) = Fib(k+1)*floor(n*tau) + Fib(k)*(n-1), for n, k ≥ 1. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Nat.fib (k + 1) * ⌊(n : ℝ) * goldenRatio⌋₊ + Nat.fib k * (n - 1)

theorem main :
    ∀ m : ℕ, 2 ≤ m →
      ((fun n : ℕ => ((T n 1 : ZMod m), (T n 2 : ZMod m))) '' Set.Ici 1).ncard = m ^ 2 := by
  sorry

end OMA.S_oeis_a035513
