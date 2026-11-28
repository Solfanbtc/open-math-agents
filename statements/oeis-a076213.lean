import Mathlib

/-!
# A076213: 2*a(n)-1 = sign(A005132(n+1)-A005132(n)).

Source: https://oeis.org/A076213
Credit: @Solfanbtc

Conjecture (OEIS A076213, %F line): let s(n) = Σ_{k=1..n} a(k); then
1. lim_{n→∞} s(n)/n = 1/2;
2. for any n, 2 s(n) > n (for n >= 1: at n = 0 the empty sum gives 0 > 0, false, so the claim
   is read for n >= 1, the range where s(n) is a nonempty sum);
3. with v(n) = 2 s(n) - n, v(n)/log(n) is bounded (stated for n >= 2, where log n > 0);
4. Σ_{k=1..n} v(k) is asymptotic to c n log(n) for some constant c with 1 < c < 3/2.

Definitions. A005132 is Recamán's sequence: R(0) = 0, R(n) = R(n-1) - n if that is positive and
not already in the sequence, else R(n-1) + n (as in upstream `OeisA5132`, reproduced here). Since
R(n+1) - R(n) = ±(n+1) is never 0, a(n) = 1 if R(n+1) > R(n) and a(n) = 0 otherwise (offset 0).
Checked numerically up to n = 2 * 10^6: the listed terms are reproduced, 2 s(n) > n always,
s(n)/n = 0.5000065, max v(n)/log(n) = 2.885, and Σ v(k)/(n log n) = 1.531 at n = 2 * 10^6
(above 3/2 at that point; the conjecture concerns the limit).
-/

namespace OMA.S_oeis_a076213

open Filter

/-- The next Recamán term after the list `previous` (whose last entry is the current term). -/
def nextTerm (previous : List ℕ) (step : ℕ) : ℕ :=
  let current := previous.getLastD 0
  if step < current ∧ current - step ∉ previous then current - step else current + step

/-- The list R(0), ..., R(n). -/
def recamanPrefix : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => recamanPrefix n ++ [nextTerm (recamanPrefix n) (n + 1)]

/-- Recamán's sequence A005132. -/
def R (n : ℕ) : ℕ := (recamanPrefix n).getLastD 0

/-- a(n) = 1 if R increases from n to n+1, else 0. -/
def a (n : ℕ) : ℕ := if R n < R (n + 1) then 1 else 0

/-- s(n) = Σ_{k=1..n} a(k). -/
def s (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, a k

/-- v(n) = 2 s(n) - n. -/
def v (n : ℕ) : ℤ := 2 * (s n : ℤ) - n

theorem main :
    Tendsto (fun n : ℕ => (s n : ℝ) / n) atTop (nhds (1 / 2)) ∧
    (∀ n : ℕ, 1 ≤ n → n < 2 * s n) ∧
    (∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(v n : ℝ)| / Real.log n ≤ C) ∧
    (∃ c : ℝ, 1 < c ∧ c < 3 / 2 ∧
      Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (v k : ℝ)) / (c * n * Real.log n)) atTop
        (nhds 1)) := by
  sorry

end OMA.S_oeis_a076213
