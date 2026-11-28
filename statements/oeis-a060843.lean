import Mathlib

/-!
# A060843: Busy Beaver problem: a(n) is the maximal number of steps that an n-state Turing machine can make on an initially blank tape before eventually halting.

Source: https://oeis.org/A060843
Credit: @Solfanbtc

Conjecture: "It is conjectured that a(5) = 47176870 (Conjecture 10 of the Scott Aaronson link
'The busy beaver frontier')."

(This value was later established by the bbchallenge collaboration in 2024, with a proof
checked in Coq; the statement below is the claim as the source records it.)

Formalization notes (Radó's model, the one used by the sequence: a(1) = 1, a(2) = 6, a(3) = 21,
a(4) = 107):
* An `n`-state machine has states `Fin n`, tape symbols `Bool` (`false` = blank), and a
  two-way infinite tape `ℤ → Bool`, initially blank, with the head at 0 in state 0.
* Each transition reads the symbol under the head, writes a symbol, moves the head one cell
  left or right, and goes to a state in `Fin n` or to the halting state (`none`).
* The number of steps counts every transition executed, including the final one into the
  halting state. (Checked in python: the 5-state champion 1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA
  makes exactly 47176870 steps in this count, and 1RB1LB_1LA1RZ makes 6 for n = 2.)
* `a(n)` is a maximum, so `a(5) = 47176870` is stated as: 47176870 is the greatest number of
  steps after which some 5-state machine halts.
-/

namespace OMA.S_oeis_a060843

/-- A transition table of an `n`-state, 2-symbol Turing machine: for the current state and the
symbol read, the symbol to write, whether to move right (`true`) or left (`false`), and the next
state (`none` = halt). -/
abbrev Machine (n : ℕ) := Fin n → Bool → Bool × Bool × Option (Fin n)

/-- A configuration of a running machine: current state, tape contents and head position. -/
structure Config (n : ℕ) where
  state : Fin n
  tape : ℤ → Bool
  head : ℤ

/-- One step: execute the transition for the current state and symbol. Returns `none` if the
transition goes to the halting state. -/
def step {n : ℕ} (M : Machine n) (c : Config n) : Option (Config n) :=
  let t := M c.state (c.tape c.head)
  let tape' := Function.update c.tape c.head t.1
  let head' := if t.2.1 then c.head + 1 else c.head - 1
  t.2.2.map fun q => ⟨q, tape', head'⟩

/-- The configuration after `k` steps from the blank tape (`none` once the machine halted). -/
def conf {n : ℕ} (M : Machine n) (q₀ : Fin n) : ℕ → Option (Config n)
  | 0 => some ⟨q₀, fun _ => false, 0⟩
  | k + 1 => (conf M q₀ k).bind (step M)

/-- `M`, started in state 0 on a blank tape, halts after exactly `t` steps: it is still running
after `t - 1` steps and the `t`-th transition goes to the halting state. -/
def HaltsAfter {n : ℕ} (M : Machine (n + 1)) (t : ℕ) : Prop :=
  1 ≤ t ∧ (conf M 0 (t - 1)).isSome ∧ conf M 0 t = none

/-- Conjecture 10 of Aaronson's "The Busy Beaver Frontier": a(5) = 47176870. -/
theorem main :
    IsGreatest {t : ℕ | ∃ M : Machine 5, HaltsAfter (n := 4) M t} 47176870 := by
  sorry

end OMA.S_oeis_a060843
