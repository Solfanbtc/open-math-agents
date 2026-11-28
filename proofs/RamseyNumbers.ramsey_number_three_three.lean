import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open RamseyNumbers SimpleGraph

-- R(3,3) is the least n with IsGraphRamsey n 3 3: the five-cycle fails, and on six vertices
-- a triangle-free graph whose complement is triangle-free has every degree below 3 on both sides.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_three_three := by
  classical
  rw [classicalRamsey_eq_sInf]
  refine (Nat.sInf_upward_closed_eq_succ_iff (fun _ _ h => monotone_nat_of_le_succ
    (f := (IsGraphRamsey · 3 3)) (IsGraphRamsey.succ · 3 3) h) 5).2 ⟨?_, fun h => h (cycleGraph 5) (by unfold CliqueFree; decide)⟩
  rintro G ⟨hG, hGc⟩
  have low (H : SimpleGraph (Fin 6)) (h : H.CliqueFree 3) (hc : Hᶜ.CliqueFree 3) :
      H.degree 0 < 3 := by
    by_contra! hd
    refine hc.mono hd _ ⟨?_, rfl⟩
    rw [H.coe_neighborFinset, H.isClique_compl]
    exact H.isIndepSet_neighborSet_of_triangleFree h 0
  have := low Gᶜ hGc (by simpa using hG)
  rw [G.degree_compl, Fintype.card_fin] at this
  have := low G hG hGc
  omega
