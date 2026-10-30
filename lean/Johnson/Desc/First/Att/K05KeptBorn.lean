-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05KeptBorn.lean: AT EVERY REQUEST's SHAPE AND EVERY LINK there are as many
kept oracle messages as entries in the group's list "born": the premise hk of whereIs_cell
(Johnson/Desc/First/Att/K05SeatsOne.lean) and of what stands on it is a law of the programs' plain
function reqGroupAt (OnBytes/Iop/Req.lean), which makes both lists out of one.

Main names:
  `groupAt_kept`: the group that reqGroupAt makes has as many kept targets as entries of "born".
  `groupsFrom_kept`, `groups_kept`: so has every group of reqGroups s.
  `kept_born`: **(keptAt D i).length = (bornAt D i).size**, for every D and i (both are 0 where the
    shape has no group number i).
General in the sort of link, though the file stands among the files of kind K5.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First.Look (Sent keptAt bornAt)

theorem groupAt_kept (s : ReqShape) (l : ℕ) (alive : List ReqAlive) :
    (reqGroupAt s l alive).1.target.kept.size = (reqGroupAt s l alive).1.born.size := by
  simp [reqGroupAt]

theorem groupsFrom_kept (s : ReqShape) : ∀ (count l : ℕ) (alive : List ReqAlive),
    ∀ g ∈ reqGroupsFrom s count l alive, g.target.kept.size = g.born.size
  | 0, _, _, g, hg => by cases hg
  | count + 1, l, alive, g, hg => by
    simp only [reqGroupsFrom, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact groupAt_kept s l alive
    · exact groupsFrom_kept s count (l + 1) _ g hg

theorem groups_kept (s : ReqShape) (i : ℕ) (g : ReqGroup) (h : (reqGroups s)[i]? = some g) :
    g.target.kept.size = g.born.size := by
  unfold reqGroups at h
  rw [reqGroupsLoop_eq] at h
  have hm : g ∈ (#[] ++ (reqGroupsFrom s (s.link.length + 1) 0 []).toArray : Array ReqGroup) :=
    Array.mem_of_getElem? h
  simp only [Array.empty_append, List.mem_toArray] at hm
  exact groupsFrom_kept s _ _ _ g hm

/-- **As many kept messages as entries of "born", at every shape and link.** -/
theorem kept_born (D : Sent) (i : ℕ) : (keptAt D i).length = (bornAt D i).size := by
  unfold keptAt bornAt
  cases h : (reqGroups D.shape)[i]? with
  | none => rfl
  | some g =>
    show (Params.keptOf g).length = g.born.size
    unfold Params.keptOf
    rw [Array.length_toList]
    exact groups_kept D.shape i g h

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.kept_born
