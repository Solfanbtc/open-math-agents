import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist

open RamseyNumbers SimpleGraph

namespace RamseyThreeFour

-- On the eight-cycle, add the four edges between opposite vertices.
-- The absolute differences 1 and 7 give the cycle and 4 gives its diagonals.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
lemma eight_fails : ¬ IsGraphRamsey 8 3 4 := by
  let G : SimpleGraph (Fin 8) :=
    { Adj := fun u v => Nat.dist u.val v.val = 1 ∨ Nat.dist u.val v.val = 4 ∨
          Nat.dist u.val v.val = 7
      symm := ⟨by decide⟩
      loopless := ⟨by decide⟩ }
  let : DecidableRel G.Adj := fun u v => by
    dsimp [G]
    infer_instance
  exact fun h => h G (by unfold CliqueFree; decide)

lemma six_works : IsGraphRamsey 6 3 3 := by
  classical
  rintro G ⟨hG, hGc⟩
  -- In a triangle-free graph the neighbours of any vertex form a clique in the complement.
  have low_degree (H : SimpleGraph (Fin 6)) (h : H.CliqueFree 3) (hc : Hᶜ.CliqueFree 3) :
      H.degree 0 < 3 := by
    by_contra! hdeg
    refine hc.mono hdeg _ ⟨?_, rfl⟩
    rw [H.coe_neighborFinset, H.isClique_compl]
    exact H.isIndepSet_neighborSet_of_triangleFree h 0
  have hd := low_degree G hG hGc
  have hdc := low_degree Gᶜ hGc (by simpa using hG)
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

lemma nine_works : IsGraphRamsey 9 3 4 := by
  classical
  rintro G ⟨hG, hGc⟩
  have hdegree (v : Fin 9) : G.degree v = 3 := by
    have upper : G.degree v < 4 := by
      by_contra! h
      refine hGc.mono h _ ⟨?_, rfl⟩
      rw [G.coe_neighborFinset, G.isClique_compl]
      exact G.isIndepSet_neighborSet_of_triangleFree hG v
    have comp_upper : Gᶜ.degree v < 6 := by
      by_contra! h
      obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
        (α := Fin 6) (s := Gᶜ.neighborFinset v) (by simpa using h)
      have hv (i : Fin 6) : Gᶜ.Adj v (f i) :=
        (Gᶜ.mem_neighborFinset v (f i)).mp (hf ⟨i, rfl⟩)
      -- Apply R(3,3) to these six non-neighbours. An independent triple extends by v.
      let H := G.comap f
      let e : H ↪g G := Embedding.comap f G
      let ec : Hᶜ ↪g Gᶜ := Embedding.complEquiv e
      apply six_works H
      refine ⟨CliqueFree.comap e.isContained hG, ?_⟩
      intro t ht
      obtain ⟨a, b, c, hab, hac, hbc, _⟩ := is3Clique_iff.mp ht
      have htri : Gᶜ.IsNClique 3 {f a, f b, f c} := is3Clique_triple_iff.mpr
        ⟨ec.map_adj_iff.mpr hab, ec.map_adj_iff.mpr hac, ec.map_adj_iff.mpr hbc⟩
      apply hGc _ (htri.insert (a := v) ?_)
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> apply hv
    rw [G.degree_compl, Fintype.card_fin] at comp_upper
    omega
  -- Nine vertices of degree three would give an odd degree sum.
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hdegree] at hsum
  omega

end RamseyThreeFour

theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_three_four := by
  rw [classicalRamsey_eq_sInf]
  exact (Nat.sInf_upward_closed_eq_succ_iff (fun _ _ h => monotone_nat_of_le_succ
    (f := (IsGraphRamsey · 3 4)) (IsGraphRamsey.succ · 3 4) h) 8).2
    ⟨RamseyThreeFour.nine_works, RamseyThreeFour.eight_fails⟩
