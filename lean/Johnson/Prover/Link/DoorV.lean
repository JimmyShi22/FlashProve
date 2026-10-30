--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/Link/DoorV.lean: **door_V: THE VALUES' HALF OF THE DOOR INTO A PROXIMITY TEST**,
generic: at a statement in order whose claims hold of the words m, the one row that the batching
returns holds of the message that the words make on the group's tables.

Main names.
  taken_say    what a statement still claims holds of the words: then every row that a test on a
    group of pending messages takes in says its claim.
  combineAt_of_order   the landed test of the batching's law, from a statement in order.
  door_V       THE STATEMENT. s: the stage; its four numbers are the layout's.
  door_V_first the same at TestFront (Johnson/Prover/Link/FormFirst.lean), at the place's first
  stage.

How. Calls alone: allSay_begun (Johnson/Desc/Means/ItemsBegun.lean) · combine_holds
(Johnson/Desc/K12/Law/BatMeans.lean) · combine_noKept0 (BatNoKept.lean) · mem_samples
(Johnson/Desc/Means/Order.lean).

Limits. FOR EVERY DRAWN x: no stop is needed. The words m are a letter: that they are what was
committed, and 0 where nobody sent anything, is the caller's. The honest direction alone: nothing on
soundness. No kept member.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormBatLaws
import Johnson.Desc.K12.Law.BatMeans
import Johnson.Desc.K12.Law.ChainOf
import Johnson.Desc.Means.Claims
import Johnson.Desc.Means.ItemsBegun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means
open Iop Prob Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.ClaimSays (msgOf)

/-- **Every row that a test on a group of pending messages takes in says its claim.** -/
theorem taken_say {K : Type} [CommRing K] (ρ : Model.Reading K) (S : Statement) (g : Nat)
    (G : Group) (m : Words K) (hG : S.groups[g]? = some G) (hC : Claims ρ S m)
    (hP : ∀ o ∈ G.members.toList, Pending S o) : AllSay ρ S (runRows S G).toList m := by
  intro r hr
  unfold Slice.runRows at hr
  simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter] at hr
  rcases hr with (c | c) | c
  · exact hC.rows g G hG r c.1
  · rw [← Array.foldl_toList] at c
    rcases mem_samples S r _ _ c with c' | ⟨o, ho, x, hx, hr'⟩
    · simp at c'
    · exact hC.samples o x hx (hP o ho) r hr'
  · exact hC.rows g G hG r c.1

/-- The landed test of the batching's law, from a statement in order. -/
theorem combineAt_of_order (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G)
    (hI : InOrder S) : combineAt (begun S g G) g ⟨layoutOf S G, runRows S G⟩ = true := by
  have h := combOk_of_order
    { st := S, book := ⟨#[], #[]⟩, roots := 0, g := g, pass := .nothing, mask := none } G hG hI
  unfold combOk at h
  simp only [hG, layout_eq S g G hG] at h
  exact h

/-- **door_V: THE DOOR's VALUES' HALF.** -/
theorem door_V (s : Sg) (S : Statement) (g : Nat) (G : Group) (x : E) (row : GroupRow)
    (m : Words GE) (hG : S.groups[g]? = some G) (hI : InOrder S) (hC : Claims rdE S m)
    (hP : ∀ o ∈ G.members.toList, Pending S o) (hK : ∀ j, G.kept.getD j false = false)
    (hk : (layoutOf S G).k = s.h + s.g) (hh : (layoutOf S G).h = s.h)
    (hl : 2 ^ (layoutOf S G).logEll = s.C.l) (hz : 2 ^ (layoutOf S G).logEllZk = s.Z.l)
    (hc : Bat.combine (begun S g G) g ⟨layoutOf S G, runRows S G⟩ x = some row) :
    (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmG s row)
      (msgOf s (tablesOf (begun S g G) (layoutOf S G) m)) :=
  H2K.ClaimSays.combine_holds s (begun S g G) g ⟨layoutOf S G, runRows S G⟩ x row
    (combineAt_of_order S g G hG hI) hc hk hh hl hz
    (H2K.Pin.combine_noKept0 _ _ _ _ _ hc fun j => hK j) m
    ((allSay_begun rdE hI g hG m).2 (taken_say rdE S g G m hG hC hP))

/-- The main code's message length is a power of two, at a stage in order. -/
theorem stageOk_main {s : Fmt.M1.Stage} (h : K12.stageOk false s = true) :
    2 ^ Nat.log2 s.C.l = s.C.l := by
  unfold K12.stageOk K12.pow2 at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.false_eq_true, if_false] at h
  exact h.1.1.1.1.1.2

/-- **The same at TestFront**, at the place's first stage. -/
theorem door_V_first {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {G : Group} {i n : Nat × Nat}
    {id : Nat} (H : TestFront p cur nxt t G i n id) (x : E) (row : GroupRow) (m : Words GE)
    (hC : Claims rdE t.st m) (hP : ∀ o ∈ G.members.toList, Pending t.st o)
    (hc : Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩ x = some row) :
    (Slf.idf (E := GE) (J := (H2K.Pub.sgOf cur).cIn.J)).Holds (stmG (H2K.Pub.sgOf cur) row)
      (msgOf (H2K.Pub.sgOf cur) (tablesOf (begun t.st t.g G) (layoutOf t.st G) m)) := by
  obtain ⟨s1, _, s3, _, _⟩ := stageOk_of H.stage
  have s0 := stageOk_main H.stage
  refine door_V (H2K.Pub.sgOf cur) t.st t.g G x row m H.group H.order hC hP H.noKept ?_ H.layH ?_ ?_
    hc
  · rw [H.layK]
    show cur.k = cur.h + (cur.k - cur.h)
    omega
  · show 2 ^ (t.st.codes.base.getD G.code default).logEll = cur.C.l
    rw [H.code, Array.getD_eq_getD_getElem?, H.base]
    show 2 ^ ceilLog2 cur.C.l = cur.C.l
    rw [← s0, ceilLog2_two_pow]
  · show 2 ^ (t.st.codes.mask.getD G.maskCode default).logEll = cur.Z.l
    rw [H.maskCode, Array.getD_eq_getD_getElem?, H.maskC]
    show 2 ^ ceilLog2 cur.Z.l = cur.Z.l
    rw [← s1, ceilLog2_two_pow]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.taken_say
#print axioms Johnson.Prover.Link.combineAt_of_order
#print axioms Johnson.Prover.Link.door_V
#print axioms Johnson.Prover.Link.stageOk_main
#print axioms Johnson.Prover.Link.door_V_first
