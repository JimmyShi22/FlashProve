-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/MadeOwedCallsHead.lean: the kind "lookup" (K3).
Conditional, under the library's hypothesis `P5J.AtMgA`: the library's `IM.MadeOwed`
(Johnson/IMR/MadeOwed.lean) at the lookup on the calls of the head's link (24): the twenty-fifth
beside the twenty-four of Honest/K3/Law/Total/MadeOwedCalls.lean; and the same at all 25 links in
one statement. At any fence inside "reached by the wrapped sub-protocols' steps". Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a state s bears no mark if `s.failed = none`. The
lookups' 50 members stand at the numbers `k3K l d` of the flat list
(Johnson/Desc/First/Look/K3Base.lean): l < 25 is the link; d is false for the lookup on the calls
and true for the lookup on the digits. The step's acceptance alone from s to s' is `IM.Yes 0 b s s'`
(Johnson/IMR/HandsDef.lean). The table is the table of borders (Johnson/Desc/First/Borders.lean).
What the debt `IM.MadeOwed` is, and how it is shown, stands in the head of MadeOwedCalls.lean. A
fence is its letter Fk: a condition on the state in front. In the statements four local notations
stand: PS for the places of all the first chain's sub-protocols, in the flat list's order, at the
full size's row of links (`flatPlacesOf linksFull true`, Johnson/Desc/First/Driver/Chain.lean); 𝔐
for `AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)`, through which the hypothesis `h` enters them; theP for
the place's parameters at the calls (`P.ofPlace`); baseP for the public test of the meaning beneath
(`mgBase`).

What is shown.
  `merge_behind_head`: behind the acceptance of the decision no heard row names the slot of the
    merge's end value: in front of the head's calls the merge has not set it yet.
  `objInT_head`: so the new test formsInT 24 3 "objects" holds behind that acceptance.
  `madeOwed_calls_head`: the debt at the head's link.
  `madeOwed_calls`: the debt at all 25 links in one statement, without the hypothesis on the place
    that the two theorems of MadeOwedCalls.lean keep: in the goals' scope the library's own place is
    there at every link in front of the head's (`layAt_scope`,
    Johnson/Desc/First/Look/K3PlanLay.lean; `attAt_scope`, Johnson/Desc/First/Look/K3PlanAtt.lean).

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hb`: b is the member at the number.
  `hFk`: the fence lies inside "reached" (`Reach`, Johnson/Top/H0/Walk/Reach.lean, over the wrapped
    sub-protocols).
  `hl`: (in `madeOwed_calls`) the link is below 25. The last two theorems make no hypothesis on a
    state.
  `hd`, `hr`, `hf`, `hfront`, `hbook`, `hpcX`: (in the first two) the decision of the kind's
    sub-protocol accepts from s to s'; s is reached; s bears no mark; the public tests in front
    hold; the book's test in front holds; the two texts of the piece agree.

Imported. MadeOwedCalls.lean and files of the library. No module under Johnson/Goal/ is imported
directly.
Follows. The way from `IM.MadeOwed` to `IM.HandsR` by the library's `IM.rows_at_rch`
(Johnson/IMR/RowsAtRch.lean) and `IM.rows_at_plan` (Johnson/IMR/RowsAtPaid.lean) was pointed out in
the work on K11's files.

How the proof goes. What is other than at the twenty-four: the place is the head's own
(`k03_look_head`, Johnson/P5J/K03HeadPartsAt.lean; its shape: `k03_shape_head`,
Johnson/P5J/K03ObjInAt.lean; its slots: `k03_slots_head`, Johnson/P5J/K03SlotsHeadAt.lean), so no
hypothesis on a place is left. The piece is 3. "The merge has no slot" is a fact of other files on
every state reached at number 340 (`k6Reached_340`, Johnson/P5J/K03MergeIdleHeadAt.lean). No fact on
the calling kind's own rounds is needed: the table asks no callerIn there. The mask row's seat is by
`mask_behind_calls` of MadeOwedCalls.lean, which stands at all 25.

Users. `handsR_calls` (Honest/K3/Law/Total/HandsCalls.lean) calls `madeOwed_calls`.

Options. `maxRecDepth` is raised to 100000 for the file; `maxHeartbeats` to 4000000 in front of two
theorems; `quotPrecheck` is off at two local notations. These raise limits on Lean's own work or
switch off a check on a notation's names: none loosens a check on a proof.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
`P5J.AtMgA` is a hypothesis; no state is shown to be reached. This file does not bring the debt to
the library's `IM.HandsR` (Johnson/IMR/HandsFence.lean): `IM.rows_at` (Johnson/IMR/RowsAt.lean) has
further hypotheses of its own and is not called here. The Boolean tests alone: what the item left l
says beside its test is not here. At the full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.MadeOwedCalls
import Johnson.P5J.K03HeadPartsAt
import Johnson.P5J.K03MergeIdleHeadAt
import Johnson.P5J.K03SlotsHeadAt
import Johnson.Desc.First.Look.K3PlanLay
import Johnson.Desc.First.Look.K3PlanAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift bookAt)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.K9 (mergeOf)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "𝔐" => AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)
set_option quotPrecheck false in
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) false
local notation "baseP" => Desc.First.Meaning.pub (mgBase : Desc.First.Meaning ProofFile.InstPub
  (Desc.Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))

include h in
/-- **Behind the acceptance at the head's calls no heard row names the slot of the merge's end
value.** Conditional on `P5J.AtMgA`; the acceptance of the decision; s being reached. No instance of
these hypotheses is exhibited in this file. -/
theorem merge_behind_head (p : Desc.First.Look.P) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ))
    (guests : List (Guest TS ProofFile.Cl)) (s s' : TS) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls K3Lot.ofForm) piece laid before p guests).decide s rs
      cols = .ok s')
    (z : ProofFile.InstPub) (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K 24 false) (z, s)) :
    ∀ g, s'.lookHeard? = some g → ∀ f ∈ g.rows.toList, ∀ t ∈ f.slots.toList,
      mergeOf s' ≠ some t.1 := by
  intro g _ f _ t _
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 340 (z, s) := reach_raw hr
  rw [k3_calls_merge_kept _ _ _ _ _ _ _ _ _ _ hd, (k6Reached_340 h.scope h.reads O hr').wo]
  exact fun e => nomatch e

set_option maxHeartbeats 4000000 in
/-- **The new test formsInT 24 3 "objects" holds behind the acceptance.** Conditional on
`P5J.AtMgA`; the acceptance of the decision at the head's own place; s being reached and without a
mark; the public tests and the book's test in front. No instance of these hypotheses is exhibited in
this file. -/
theorem objInT_head
    (hpcX : (IM.k3Place 24 false).piece = Desc.K3.pieceAt (At.X Zp) 24 false) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Guest TS ProofFile.Cl)) (s s' : TS) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls K3Lot.ofForm) piece laid before (theP x₀) guests).decide
      s rs cols = .ok s')
    (z : ProofFile.InstPub) (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K 24 false) (z, s))
    (hf : s.failed = none)
    (hfront : ∀ q ∈ frontAtK mgMore (kOfCalls 24), (mgAll (𝔐) mgBase).pub q (z, s) = true)
    (hbook : bookAt (𝔐).N PS[k3K 24 false]? s = true) :
    (mgAll (𝔐) mgBase).pub (.formsInT 24 3 "objects") (z, s') = true := by
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full 24 (by omega)
  have hsh : 2 + shift sub = 3 := hpc.symm.trans k03_piece_head
  have hruns := k03_runs_calls h 24 (by omega) sub hs'
  rw [hsh] at hruns
  obtain ⟨lk, hRd, hfind, hfindG⟩ := k03_hfind2 h 24 (by omega)
  have hlook := k03_look_head h
  have hIn := (front_three (𝔐) mgBase (a := IM.k3Place 24 false) s rfl hpcX hpc (by omega) hs'
    (calls_tests (by omega)).1 hlook rfl (hfit_mgAll (𝔐) mgBase rfl) z hfront).1
  exact objInT_state (𝔐) mgBase K3Lot.ofForm piece laid before guests s s' rs cols hd hIn
    (k03_shape_head h) hruns k03_atS2_calls hRd k03_hpass k03_hsame hfind hfindG z
    (mask_behind_calls h (by omega) hlook piece laid before guests s s' rs cols hd z hr hf hfront
      hbook)
    (merge_behind_head h _ piece laid before guests s s' rs cols hd z hr)

set_option maxHeartbeats 4000000 in
/-- **The debt `IM.MadeOwed` at the calls of the head's link.** Conditional on `P5J.AtMgA`; b being
the member at the number; a fence inside "reached". No instance of these hypotheses is exhibited in
this file. -/
theorem madeOwed_calls_head {b : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[k3K 24 false]? = some b)
    (z : ProofFile.InstPub) (Fk : ℕ → TS → Prop)
    (hFk : ∀ s, Fk (k3K 24 false) s →
      Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K 24 false) (z, s)) :
    IM.MadeOwed Fk (𝔐).N IM.linksW IM.placesW (𝔐).pubD baseP z 0 (k3K 24 false) b b.place := by
  intro s s' hF hy' h0 _ hx q hq
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hpcW, P', sent, laid, rs, gs, hP, hd⟩ :=
    calls_hd_of_yes h.scope h.reads O h.laid.planOk (by omega) hb hy'
  rw [O.W] at hpcW hP
  have hlook := k03_look_head h
  have eP : P' = theP x₀ := by
    have e0 : placeAt (At.X Zp) 24 false = some P' := hP
    unfold placeAt at e0
    rw [hlook] at e0
    exact (Option.some.inj e0).symm
  subst eP
  have hr := hFk s hF
  have hfront0 := front_of_xk _ _ _ z (k3K 24 false) s hx
  have hbook : bookAt (𝔐).N PS[k3K 24 false]? s = true := by
    have h4 := (IM.xk_parts hx).2.2.2.1
    rw [IM.placesW_full] at h4
    exact h4
  have hpl : b.place = IM.k3Place 24 false := by
    have e1 := IM.place_at h.scope h.reads O hb
    rw [IM.placesW_full, K3Lot.k03_at_full 24 (by omega) false] at e1
    exact (Option.some.inj e1).symm
  have hq' := behind_of_made _ _ _ _ q hq
  rw [hpl] at hq'
  have hObj := objInT_head h hpcW _ laid sent [] s s' rs gs hd z hr h0 hfront0 hbook
  exact behind_head_state (𝔐) mgBase K3Lot.ofForm _ laid sent [] s s' rs gs hd rfl
    (fun _ _ _ _ => rfl) (headLink_in_scope h.scope h.reads h.pubOne) hlook (k03_shape_head h) hpcW
    (k03_slots_head h) z hfront0 hObj q hq'

/-- **The debt `IM.MadeOwed` at the calls of every link.** Conditional on `P5J.AtMgA`; a link below
25; b being the member at the number; a fence inside "reached". No instance of these hypotheses is
exhibited in this file. -/
theorem madeOwed_calls {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) (Fk : ℕ → TS → Prop)
    (hFk : ∀ s, Fk (k3K l false) s →
      Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l false) (z, s)) :
    IM.MadeOwed Fk (𝔐).N IM.linksW IM.placesW (𝔐).pubD baseP z 0 (k3K l false) b b.place := by
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · rcases Nat.mod_two_eq_zero_or_one l with he | ho
    · obtain ⟨y, _, hy, -⟩ := layAt_scope h.scope h.reads h.pubOne h24 he
      exact madeOwed_calls_lay h hl hy hb z Fk hFk
    · obtain ⟨y, a, -, -, hy, -⟩ :=
        attAt_scope h.scope h.reads h.pubOne h24 ho (𝔐).sent (fun _ => 0)
      exact madeOwed_calls_att h hl hy hb z Fk hFk
  · obtain rfl : l = 24 := by omega
    exact madeOwed_calls_head h hb z Fk hFk

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.merge_behind_head
#print axioms ProofFile.Honest.K3.Law.Total.objInT_head
#print axioms ProofFile.Honest.K3.Law.Total.madeOwed_calls_head
#print axioms ProofFile.Honest.K3.Law.Total.madeOwed_calls
