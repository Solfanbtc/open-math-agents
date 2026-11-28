import Mathlib

/-!
# A060649: Smallest squarefree k ≡ 3 (mod 4) such that Q(sqrt(-k)) has class number n (or 0).

Source: https://oeis.org/A060649
Credit: @Solfanbtc

Four conjectures in the entry; `main` is their conjunction:
1. (Jianing Song, May 08 2021) a(n) > 0 for all n;
2. (Jianing Song, May 08 2021) a(n) = o(n^2);
3. (Jianing Song, Oct 03 2022) a(n) is also the smallest absolute value of a negative
   fundamental discriminant with class number n; "this is to say, for even n, if a(n) > 0 and
   A344072(n/2) > 0, then A344072(n/2) > a(n)" (stated in this explicit form);
4. (Ralf Stephan, May 23 2026) except a(1) = 3, a(n) is congruent to 7 (mod 8).

Conventions.
* Q(sqrt(-m)) for squarefree m ≥ 1 is `AdjoinRoot (X^2 + m)` over ℚ (X^2 + m is irreducible
  over ℚ for m ≥ 1, as -m < 0 is not a rational square); its class number is Mathlib's
  `NumberField.classNumber`. `hK m` is that class number (set to 0 if X^2 + m were reducible,
  which does not happen for m ≥ 1).
* a(n) = least squarefree k ≡ 3 (mod 4) with hK k = n, and 0 if there is none: `sInf` of the
  set, which is 0 for the empty set, matching the entry's convention. Data: 3, 15, 23, 39, ...
* A344072(n) = smallest even fundamental discriminant k with h(-k) = 2n (0 if none). The even
  negative fundamental discriminants are -4m with m squarefree, m ≡ 1 or 2 (mod 4), and the
  field of discriminant -4m is Q(sqrt(-m)); so A344072(n) = least 4m with such m and hK m = 2n.
* o(n^2) is `Asymptotics.IsLittleO` along n → ∞.
-/

namespace OMA.S_oeis_a060649

open Polynomial

open scoped Classical in
/-- Class number of Q(sqrt(-m)). -/
noncomputable def hK (m : ℕ) : ℕ :=
  if h : Irreducible (X ^ 2 + C (m : ℚ)) then
    haveI : Fact (Irreducible (X ^ 2 + C (m : ℚ))) := ⟨h⟩
    NumberField.classNumber (AdjoinRoot (X ^ 2 + C (m : ℚ)))
  else 0

/-- A060649. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | Squarefree k ∧ k % 4 = 3 ∧ hK k = n}

/-- A344072. -/
noncomputable def A344072 (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ m : ℕ, k = 4 * m ∧ Squarefree m ∧ (m % 4 = 1 ∨ m % 4 = 2) ∧ hK m = 2 * n}

theorem main :
    (∀ n : ℕ, 1 ≤ n → 0 < a n) ∧
    (fun n : ℕ => (a n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → 0 < a n → 0 < A344072 (n / 2) → a n < A344072 (n / 2)) ∧
    (∀ n : ℕ, 2 ≤ n → a n % 8 = 7) := by
  sorry

end OMA.S_oeis_a060649
