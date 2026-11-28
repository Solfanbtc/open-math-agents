import Mathlib

/-!
# Frame–Stewart conjecture for five or more pegs

Source: https://en.wikipedia.org/wiki/Tower_of_Hanoi#Frame%E2%80%93Stewart_algorithm
Credit: @Solfanbtc

The Tower of Hanoi with `r` pegs starts with `n` disks stacked on one peg in order of decreasing
size, the smallest at the top; the objective is to move the entire stack to another peg, obeying
the rules of the source: only one disk may be moved at a time; each move takes the upper disk of
one of the stacks and places it on top of another stack or on an empty peg; no disk may be placed
on top of a disk that is smaller than it.

The source writes `T(n, r)` for the minimum number of moves required to transfer `n` disks using
`r` pegs, and describes the Frame–Stewart algorithm recursively: for some `k` with `1 ≤ k < n`,
transfer the top `k` disks to a peg other than the start and destination pegs (`T(k, r)` moves),
then the remaining `n - k` disks to the destination peg using only the remaining `r - 1` pegs
(`T(n - k, r - 1)` moves), then the top `k` disks to the destination peg (`T(k, r)` moves), with
`k` chosen to minimise `2 T(k, r) + T(n - k, r - 1)`. With three pegs this is the classical
solution in `2 ^ n - 1` moves, which is the minimum. The source says that the Frame–Stewart
algorithm is known without proof of optimality since 1941 for four or more pegs, that its
optimality for four pegs was verified in 2014 by Bousch, and that it is presumed to be optimal for
any number of pegs. The catalogue's open problem is the case of five or more pegs: `main` below.

Encoding: the disks are `Fin n`, numbered from the smallest (`0`) to the largest, and the pegs
are `Fin r`. Since the disks on a peg are always stacked in order of size, a configuration is
determined by the peg of each disk, so a configuration is a function `Fin n → Fin r`.
-/

namespace OMA.S_wpc_frame_stewart_conjecture

/-- A configuration of `n` disks on `r` pegs: disk `i` sits on peg `c i` (on each peg the disks
are stacked in order of size, the smallest on top). -/
abbrev Config (n r : ℕ) := Fin n → Fin r

/-- A legal move from `c` to `c'`: exactly one disk `d` changes peg; it is the upper disk of its
peg (no smaller disk is on the peg it leaves) and it is not placed on a smaller disk (no smaller
disk is on the peg it goes to). -/
def IsMove {n r : ℕ} (c c' : Config n r) : Prop :=
  ∃ d : Fin n, c' d ≠ c d ∧ (∀ e, e ≠ d → c' e = c e) ∧
    ∀ e, e < d → c e ≠ c d ∧ c e ≠ c' d

/-- `SolvableIn m start goal`: some sequence of `m` legal moves leads from `start` to `goal`. -/
def SolvableIn {n r : ℕ} (m : ℕ) (start goal : Config n r) : Prop :=
  ∃ s : Fin (m + 1) → Config n r, s 0 = start ∧ s (Fin.last m) = goal ∧
    ∀ i : Fin m, IsMove (s i.castSucc) (s i.succ)

/-- The number of moves of the Frame–Stewart algorithm for `n` disks and `r` pegs: `2 ^ n - 1`
for three pegs, and for `r ≥ 4` pegs `0` for no disk, `1` for one disk, and otherwise the
minimum over `1 ≤ k < n` of `2 * frameStewart r k + frameStewart (r - 1) (n - k)`. (The values
for fewer than three pegs are never used.) -/
def frameStewart (r n : ℕ) : ℕ :=
  if hr : r ≤ 3 then 2 ^ n - 1
  else if hn : n ≤ 1 then n
  else (Finset.range (n - 1)).attach.inf' (by simp; omega)
    fun j => 2 * frameStewart r (j.1 + 1) + frameStewart (r - 1) (n - (j.1 + 1))
termination_by r + n
decreasing_by
  all_goals have := j.2
  all_goals simp only [Finset.mem_range] at this
  all_goals omega

/-- **Frame–Stewart conjecture** for five or more pegs: for every number `r ≥ 5` of pegs, every
number `n` of disks and any two distinct pegs `a` and `b`, the least number of moves that
transfers the stack of all `n` disks from peg `a` to peg `b` is the number of moves of the
Frame–Stewart algorithm, `frameStewart r n`. -/
theorem main : ∀ r : ℕ, 5 ≤ r → ∀ n : ℕ, ∀ a b : Fin r, a ≠ b →
    IsLeast {m : ℕ | SolvableIn m (fun _ : Fin n => a) (fun _ => b)} (frameStewart r n) := by
  sorry

end OMA.S_wpc_frame_stewart_conjecture
