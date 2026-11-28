import Mathlib

/-!
# A055496: a(1) = 2; a(n) is smallest prime > 2*a(n-1).

Source: https://oeis.org/A055496
Credit: @Solfanbtc

Two conjectures in the entry; `main` is their conjunction:
1. (Franklin T. Adams-Watters, Nov 11 2011) "It appears that lim_{n->infinity} a(n)/2^n exists
   and is approximately 1.569985585....";
2. (Thomas Ordowski, Apr 05 2015) lim_{n->infinity} a(n)/A006992(n) = 5.1648264...,
   where A006992 (Bertrand primes) is b(1) = 2, b(n) = largest prime < 2 b(n-1).

Conventions.
* Offset 1; the recursions are defined as a(n+1) = least prime
  > 2 a(n) and b(n+1) = greatest prime < 2 b(n) (both exist: Bertrand's postulate), via
  `sInf` / `sSup` of the corresponding sets (the set of primes < 2 b(n) is finite and
  nonempty, so `sSup` is its maximum). Data: a = 2, 5, 11, 23, 47, 97, ...;
  b = 2, 3, 5, 7, 13, 23, 43, ...
* A constant given only by its leading digits ("5.1648264...", "1.569985585...") is stated as:
  the limit exists and its decimal expansion begins with those digits, i.e. it lies in
  [5.1648264, 5.1648265) resp. [1.569985585, 1.569985586).
* python3: a(n)/2^n = 1.569985585331... and a(n)/b(n) = 5.164826406957... for n = 80..160.
-/

namespace OMA.S_oeis_a055496

/-- A055496 (index shifted: `a 0` is the first term). -/
noncomputable def a : ℕ → ℕ
  | 0 => 2
  | n + 1 => sInf {p : ℕ | p.Prime ∧ 2 * a n < p}

/-- A006992, Bertrand primes (index shifted: `b 0` is the first term). -/
noncomputable def b : ℕ → ℕ
  | 0 => 2
  | n + 1 => sSup {p : ℕ | p.Prime ∧ p < 2 * b n}

theorem main :
    (∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (a (n - 1) : ℝ) / 2 ^ n) Filter.atTop (nhds L) ∧
      1.569985585 ≤ L ∧ L < 1.569985586) ∧
    (∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (a n : ℝ) / b n) Filter.atTop (nhds L) ∧
      5.1648264 ≤ L ∧ L < 5.1648265) := by
  sorry

end OMA.S_oeis_a055496
