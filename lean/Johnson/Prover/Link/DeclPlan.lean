-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DeclPlan.lean: THE PROXIMITY TEST (the kind K12): WHICH TREE THE PLAN's ROUND
"CS" OF A STAGE DECLARES. General in the numbers of a place. Statements and proofs, over the
library's Dealt and listsOf (Johnson/Desc/K12/OpenLaws.lean).

  cs_opens       at a stage that is not the last: "SEND seed" opens nothing, "CS" the first of the
                 lists that are left
  base_opens     at the last stage: the first round opens nothing, the second the first list
  listsOf_first  where no fold sends its own mask: the first list: the trees of the test's group
  listsOf_later  there: the list of stage number j + 1: ONE tree: the own tree number free + j, of
                 the stage's depth, of the format's width (wMid; at the last stage wLast)
  dealt_drop     WHAT RIDES OF THE PLAN along the stages: Dealt at the lists from number j on

By: Dealt.cons, open_step (OpenLaws.lean).

Limits. Nothing on a record, a book or a view. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.OpenLaws
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.K12.AtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- At a stage that is not the last. -/
theorem cs_opens (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (x : List Told)
    (Ls : List (List Told)) (l : Laid) (h : Dealt cur (next :: rest) (x :: Ls) l)
    (dS dC : Fmt.DeclaredRound) (hc : ((l.drop (1 + cur.k)).take 2).map (·.1) = [dS, dC]) :
    dS.opens = [] ∧ dC.opens = x := by
  have h1 : (((l.map (·.1.opens)).drop (1 + cur.k)).take 2) = [dS.opens, dC.opens] := by
    have := congrArg (List.map (·.opens)) hc
    rw [List.map_map, List.map_take, List.map_drop] at this
    exact this
  rw [h.cons, List.drop_left' (by simp)] at h1
  simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

/-- At the last stage. -/
theorem base_opens (cur : Fmt.M1.Stage) (x : List Told) (Ls : List (List Told)) (l : Laid)
    (h : Dealt cur [] (x :: Ls) l) (d₁ d₂ : Fmt.DeclaredRound) (hc : l.map (·.1) = [d₁, d₂]) :
    d₁.opens = [] ∧ d₂.opens = x := by
  have h1 : l.map (·.1.opens) = [d₁.opens, d₂.opens] := by
    have := congrArg (List.map (·.opens)) hc
    rw [List.map_map] at this
    exact this
  rw [h.opens] at h1
  simp only [quiet, fill, List.cons.injEq, and_true] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

/-- The first list. -/
theorem listsOf_first (N : H2U.TestNums) (hm : N.ownMask = false) :
    (listsOf N)[0]? = some N.first := by
  simp [listsOf, hm]

/-- **The list of stage number j + 1.** -/
theorem listsOf_later (N : H2U.TestNums) (j : Nat) (s : Fmt.M1.Stage) (hm : N.ownMask = false)
    (hs : N.stages[j + 1]? = some s) :
    (listsOf N)[j + 1]? = some [N.own s.C.a
      (if j + 2 == N.stages.length then Fmt.M1.wLast s else Fmt.M1.wMid s) (N.free + j)] := by
  have h1 : N.stages.tail[j]? = some s := by
    rw [List.getElem?_tail]
    exact hs
  simp [listsOf, H2U.TestNums.sent, hm, List.getElem?_zipIdx, h1]

/-- **What rides of the plan.** -/
theorem dealt_drop (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Ls : List (List Told))
    (j : Nat) (l : Laid) (hj : j < Ls.length) (h : Dealt cur (next :: rest) (Ls.drop j) l) :
    Dealt next rest (Ls.drop (j + 1)) (l.drop (cur.k + 3)) := by
  rw [List.drop_eq_getElem_cons hj] at h
  exact (open_step (Cl := Unit) guardedProximityTestParts (H2U.noP12 ⟨1, none, 0, .K12⟩) 0 cur next rest _ _ l
    h).2.2

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.cs_opens
#print axioms Johnson.Prover.Link.base_opens
#print axioms Johnson.Prover.Link.listsOf_first
#print axioms Johnson.Prover.Link.listsOf_later
#print axioms Johnson.Prover.Link.dealt_drop
