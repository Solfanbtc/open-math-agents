import Mathlib

/-!
# A011946: Number of Barlow packings with group P63/mmc(S) that repeat after 4n layers.

Source: https://oeis.org/A011946
Credit: @Solfanbtc

The OEIS entry records two conjectures:
* (R. J. Mathar, 2011) A011946 is the Möbius transform of A127804;
* (R. J. Mathar, 2024) a(n) = A045683(2n).

`main` states both, as a conjunction, for every n ≥ 1 (the offset of A011946).

Conventions.
* Barlow packings with a given space group have no Mathlib counterpart, so `a` is defined by
  the formula given in the entry (P. D. Hanna, B. Naskręcki):
  a(n) = Σ_{d ∣ n, d odd} μ(d) · 2^(n/d - 1).
  It reproduces all listed terms 1, 2, 3, 8, 15, 30, 63, 128, ... (checked numerically).
* A127804 has offset 0 and is defined by its name: a(2n) = 2^(2n), a(2n+1) = 2^(2n+1) + a(n).
  The Möbius transform pairs the k-th term of the list (k ≥ 1), i.e. A127804(k - 1), with
  index k: a(n) = Σ_{d ∣ n} μ(n/d) · A127804(d - 1). This is the reading that matches the
  data (a(4) = 11 - 3 = 8, a(6) = 36 - 4 - 3 + 1 = 30).
* A045683(m) is defined by its name: the number of 2m-bead binary necklaces (words up to
  rotation) that are balanced (m beads of each color), have fundamental period 2m, and are
  equivalent (as necklaces, i.e. up to rotation) to their reverse, their complement and their
  reversed complement. Necklaces are counted as rotation orbits of such words. This
  reproduces 1, 1, 1, 2, 3, 3, 7, 8, 14, 15 for m = 1..10 (checked by brute force).
  So A045683(2n) counts necklaces with 4n beads.
-/

namespace OMA.S_oeis_a011946

open ArithmeticFunction

/-- A011946 via its formula: a(n) = Σ_{d ∣ n, d odd} μ(d) 2^(n/d - 1). -/
def a (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter Odd, (moebius d : ℤ) * 2 ^ (n / d - 1)

/-- A127804: a(2n) = 2^(2n), a(2n+1) = 2^(2n+1) + a(n). -/
def A127804 (n : ℕ) : ℕ :=
  if h : n % 2 = 0 then 2 ^ n else 2 ^ n + A127804 (n / 2)
termination_by n
decreasing_by omega

/-- Rotation of a cyclic binary word by `k` positions. -/
def rot {L : ℕ} (k : Fin L) (w : Fin L → Bool) : Fin L → Bool := fun i => w (i + k)

/-- Words of length `2m` that are balanced, primitive (fundamental period `2m`), and
rotation-equivalent to their reverse, complement and reversed complement. -/
def goodWords (m : ℕ) : Finset (Fin (2 * m) → Bool) :=
  Finset.univ.filter fun w =>
    (Finset.univ.filter fun i => w i = true).card = m ∧
    (∀ k : Fin (2 * m), rot k w = w → k.val = 0) ∧
    (∃ k : Fin (2 * m), rot k (w ∘ Fin.rev) = w) ∧
    (∃ k : Fin (2 * m), rot k (fun i => !w i) = w) ∧
    (∃ k : Fin (2 * m), rot k (fun i => !w (Fin.rev i)) = w)

/-- A045683(m): number of necklaces (rotation orbits) of words in `goodWords m`. -/
def A045683 (m : ℕ) : ℕ :=
  ((goodWords m).image fun w => Finset.univ.image fun k : Fin (2 * m) => rot k w).card

theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = ∑ d ∈ n.divisors, (moebius (n / d) : ℤ) * (A127804 (d - 1) : ℤ)) ∧
    (∀ n : ℕ, 1 ≤ n → a n = (A045683 (2 * n) : ℤ)) := by
  sorry

end OMA.S_oeis_a011946
