import Mathlib

/-!
# A137295: P-positions in sparse Atomic Wari, octal game .37.

Source: https://oeis.org/A137295 (Joshua Zucker, 2008; OEIS Foundation, CC BY-SA 4.0).
Reference: J. Erickson, "Sowing Games", in R. J. Nowakowski (ed.), Games of No Chance, 1996,
p. 295.
Credit: @Solfanbtc

The game (OEIS example): a player can remove one seed from any pile, or remove two seeds from
any pile and optionally split the remainder into two piles. This is the octal game .37: digit
3 = 1 + 2 for removing one seed (the pile may vanish or remain as one pile), digit 7 = 1 + 2 + 4
for removing two seeds (the pile may vanish, remain as one pile, or be split into two nonempty
piles). The player who cannot move loses (normal play).

The terms 0, 3, 11, 19, 29, 45, 71, 97, 123, 149, 175, 313, 407 are the pile sizes n such that a
single pile of n seeds is a P-position, i.e. has nim-value 0.

Conjecture (OEIS comment): the sequence is finite ("only conjectured to be finite as of the
publication in 1996, but there are definitely no more terms under 200000").

Formalization notes.
* `G n` is the nim-value (Sprague–Grundy value) of a single pile of n seeds, computed by the
  standard recursion: the mex of the values of the options, where the empty position has value
  0, one pile of a seeds has value G a, and two piles of a and b seeds have value G a xor G b.
  A single pile is a P-position iff its nim-value is 0 (Sprague–Grundy theorem).
* The options of a pile of n: remove one seed, leaving one pile of n - 1 (n ≥ 1; for n = 1 that
  is the empty position, value G 0 = 0); remove two seeds, leaving one pile of n - 2 (n ≥ 2);
  or remove two and split the remainder into piles of a ≥ 1 and n - 2 - a ≥ 1 seeds.
* A python computation of G reproduces exactly the 13 listed terms among n ≤ 5000.
-/

namespace OMA.S_oeis_a137295

/-- The minimum excluded value of a finite set of natural numbers. -/
def mex (s : Finset ℕ) : ℕ :=
  Nat.find (p := fun m => m ∉ s)
    ⟨s.sup id + 1, fun h => Nat.not_succ_le_self _ (Finset.le_sup (f := id) h)⟩

/-- Nim-value of a single pile of `n` seeds in the octal game .37. -/
def G (n : ℕ) : ℕ :=
  let g : ℕ → ℕ := fun a => if a < n then G a else 0
  -- remove one seed (n ≥ 1): one pile of n - 1 seeds (empty when n = 1)
  let removeOne : Finset ℕ := if 1 ≤ n then {g (n - 1)} else ∅
  -- remove two seeds (n ≥ 2): one pile of n - 2 seeds (empty when n = 2)
  let removeTwo : Finset ℕ := if 2 ≤ n then {g (n - 2)} else ∅
  -- remove two seeds and split the rest into piles of a ≥ 1 and n - 2 - a ≥ 1 seeds,
  -- i.e. 1 ≤ a < n - 2
  let split : Finset ℕ :=
    (Finset.Ico 1 (n - 2)).image (fun a => g a ^^^ g (n - 2 - a))
  mex (removeOne ∪ removeTwo ∪ split)

/-- The pile sizes that are P-positions (A137295) form a finite set. -/
theorem main : {n : ℕ | G n = 0}.Finite := by
  sorry

end OMA.S_oeis_a137295
