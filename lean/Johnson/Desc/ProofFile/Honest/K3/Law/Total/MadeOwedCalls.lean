-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/MadeOwedCalls.lean: the kind "lookup" (K3). Conditional,
under the library's hypothesis `P5J.AtMgA`: the library's `IM.MadeOwed` (Johnson/IMR/MadeOwed.lean:
"the debt of a kind's authors at one of its places") at the lookup on the calls of the 24 links in
front of the head's, at the composed meaning's own data, at any fence that lies inside "reached by
the wrapped sub-protocols' steps". Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a state s bears no mark if `s.failed = none`. The
lookups' 50 members stand at the numbers `k3K l d` of the flat list
(Johnson/Desc/First/Look/K3Base.lean): l < 25 is the link; d is false for the lookup on the calls
and true for the lookup on the digits. The step's acceptance alone from s to s' is `IM.Yes 0 b s s'`
(Johnson/IMR/HandsDef.lean). The table is the table of borders (Johnson/Desc/First/Borders.lean). A
fence is the letter Fk of `IM.MadeOwed`: a condition on the state in front.
What the debt is. From a fenced state s, the acceptance alone of the step of the chain's member from
s to s', no mark at either, and the table's Boolean tests in front (`IM.XK`, HandsDef.lean, at the
public items' test `IM.EAt`, MadeOwed.lean): every public test that is asked behind the place and
does not ride by its footprint (the library's word: Johnson/Goal/Meaning/QuietRide.lean) holds at
s'. In the debt's own form the acceptance is the member's as it stands at its number of the flat
list, while "reached" is by the steps of the wrapped sub-protocols, each under the library's `below`
(Johnson/Desc/Sound/ChainRule.lean). With the debt the library's `IM.rows_at`
(Johnson/IMR/RowsAt.lean) gives `IM.HandsR` (Johnson/IMR/HandsFence.lean), all six fields, at the
member's number, under further hypotheses of its own: the book's test at every state reached over
the list as it stands; the public test of the meaning beneath has one value at all states; the
place's kind is one of the six; the fence lies inside "reached" over the list as it stands.
`IM.rows_at` is not called in this file.

What is shown.
  `mask_behind_calls`: behind the acceptance of the decision the mask row's message has a seat among
    the link's own.
  `merge_behind_calls`: behind that acceptance no heard row names the slot of the merge's end value:
    the merge has no slot there.
  `objInT_calls`: so the new test formsInT l 2 "objects" holds behind that acceptance.
  `madeOwed_calls_lay`, `madeOwed_calls_att`: the debt, at a layers' link and at an attention link.
The statements speak of the verifier's states alone: no thread, prover, coin, string, piece or
transcript occurs in them.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hy`: (in the last two) y is the library's own place of the lookup at the link (`layAt`,
    Johnson/Desc/First/Look/K3CallerLayTests.lean; `attAt`, Johnson/Desc/First/Look/K3AttInst.lean):
    public data.
  `hl`: (in `mask_behind_calls` and the last two) the link is below 25.
  `hb`: b is the member at the number `k3K l false`.
  `hFk`: the fence lies inside "reached" (`Reach`, Johnson/Top/H0/Walk/Reach.lean, over the wrapped
    sub-protocols). The last two make no hypothesis on a state.
  `hlook`, `hd`, `hr`, `hf`, `hfront`, `hbook`, `hsP`, `hpcX`, `h24`: (in the first three) y is the
    lookup's place; the decision of the kind's sub-protocol accepts from s to s'; s is reached; s
    bears no mark; the public tests in front hold; the book's test in front holds; the place's
    parameters make its shape; the two texts of the piece agree; the link stands in front of the
    head's.

Imported. Honest/K3/Law/Total/CallsBehindAll.lean, Honest/K3/Law/Total/CallsYesAt.lean and files of
the library. Of these Johnson/P5J/StartAtHead.lean and others import modules under Johnson/Goal/;
none is imported here directly. One name that is declared under that folder is written in a proof
here: `Meaning.scope_plans` (Johnson/Goal/Meaning/PlanShapes.lean), a lemma's call.
Follows. The proofs of `mask_behind_calls` and `merge_behind_calls` follow `k03_maskAt_lean`
(Johnson/P5J/K03MaskLeanAt.lean) and `k03_merge_none_calls`, `k03_mergeAt_calls`
(Johnson/P5J/K03MergeIdleAt.lean) line for line from the decision's acceptance on. The way from
`IM.MadeOwed` to `IM.HandsR` by the library's `IM.rows_at_rch` (Johnson/IMR/RowsAtRch.lean) and
`IM.rows_at_plan` (Johnson/IMR/RowsAtPaid.lean) was pointed out in the work on K11's files.

How the proof goes. The last two combine other files' theorems. The three bridges of CallsYesAt.lean
lead from what the debt gives to the decision's acceptance, to the tests in front and to the list
behind; "every public test behind the acceptance" is from CallsBehindAll.lean. What these leave is
shown as the library itself shows it at a piece's acceptance, by the same named lemmas, in the same
order: Johnson/P5J/K03OthersPubAt.lean (the place's facts; the built link's slots; nothing of the
calling kind's own rounds is heard in front, and which sort of link stands open:
Johnson/IMR/UnheardField.lean, Johnson/IMR/SortField.lean, from "reached"),
Johnson/P5J/K03ObjInAt.lean (the terms of the readers), K03MaskLeanAt.lean (`maskSeat_at`, on one
state), K03MergeIdleAt.lean. It parts from them in one thing. The library's "reached" under its
hypothesis (`AtMg.rch`, Johnson/P5J/FourAtMg.lean) asks besides that the statement's public part is
a typed instance's, and speaks of statements with strings. Here the facts along the fold are taken
at "reached" itself, with nothing beside a statement: the library's `atMgR_of_head`
(StartAtHead.lean) is general in that letter.

Users. `madeOwed_calls` (Honest/K3/Law/Total/MadeOwedCallsHead.lean) calls the last two.

Options. `maxRecDepth` is raised to 100000 for the file; `maxHeartbeats` to 4000000 in front of four
theorems; `quotPrecheck` is off at two local notations. These raise limits on Lean's own work or
switch off a check on a notation's names: none loosens a check on a proof.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
`P5J.AtMgA` is a hypothesis; no state is shown to be reached. The library's
`P5J.head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean) gives a value of `P5J.AtMgA` under
four hypotheses of its own: the public files are in the goals' scope; their reading returns; the
verifier's own three values are laid; `At.CondsOwed`. By that file's own limits, at the release's
full-size public files the first three are evaluated true by name (runs, no theorem), and the fourth
is for other files to speak of (Johnson/Goal/Skeleton/CondsOfLaid.lean). Since that file was written
the library has a value of `P5J.AtMgA` with no premise at each of the goals' two named sets of
public files: `headMember_zFull` (AtFullSide/Top/HeadMemberAtFull.lean) and `headMember_zGap`
(AtFullSide/Top/HeadMemberAtGap.lean), in its side library. The Boolean tests alone: what the item
left l says beside its test is not here. The head's own link (24) is not here. At the full size
alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.CallsBehindAll
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.CallsYesAt
import Johnson.P5J.K03Due5
import Johnson.P5J.StartAtHead
import Johnson.IMR.PlacesScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift moreItem pubSets bookAt)
open VerifiableInference.Desc.First.FillSent (sentName five_of_sentIs)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.K9 (segAt? maskSeat mergeOf)
open Johnson.Desc.First.Walk.Tied (Reach)
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

set_option maxHeartbeats 4000000 in
/-- **Behind the acceptance the mask row's message has a seat among the link's own.** Conditional on
`P5J.AtMgA`; the place; the acceptance of the decision; s being reached and without a mark; the
public tests and the book's test in front. No instance of these hypotheses is exhibited in this
file. -/
theorem mask_behind_calls {l : ℕ} (hl : l < 25) {y : Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l false = some y) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ))
    (guests : List (Guest TS ProofFile.Cl)) (s s' : TS) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls K3Lot.ofForm) piece laid before (theP y) guests).decide
      s rs cols = .ok s')
    (z : ProofFile.InstPub) (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l false) (z, s))
    (hf : s.failed = none)
    (hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll (𝔐) mgBase).pub q (z, s) = true)
    (hbook : bookAt (𝔐).N PS[k3K l false]? s = true) :
    ∀ c, segAt? s' = some c → (maskSeat ((𝔐).N.sent l 0) c).isSome = true := by
  intro c hc
  obtain ⟨L, R⟩ := atMgR_of_head h (Str := Unit)
    (fun k a => Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a.1) (fun _ _ ha => ha)
  have F := R.fold
  have hT := k03_maskC_at h L R.listed l hl y hlook
  have hsb := k3_calls_sameBut K3Lot.ofForm piece laid before _ guests s s' rs cols hd
  have ey : y.link = l := lookAt_link hlook
  obtain ⟨hLv, -, -, -⟩ := VerifiableInference.OnPublicFiles.segAt_parts hc
  have hLu : s.link? = some c.L := hsb.link.symm.trans hLv
  have eLive : s'.live = s.live := by
    rw [live_of_link hLv, live_of_link hLu]
  have hmem : moreItem (sentName l) ∈ (pubSets mgMore linksFull PS)[k3K l false]?.getD [] := by
    have h0 := List.all_eq_true.1 callsSentFront l (List.mem_range.2 hl)
    unfold callsSentFrontB at h0
    simpa using h0
  have hsent := pubSent_mgAll (𝔐) mgBase l z s (hfront _ (by
    rw [kOfCalls_k3K l]
    exact List.mem_append_left _ hmem))
  obtain ⟨fnext, flink, -, fown, -⟩ := five_of_sentIs hLu hsent
  have hk : k3K l false < (PS).length :=
    (List.getElem?_eq_some_iff.1 (K3Lot.k03_at_full l hl false)).1
  have hbook' := Desc.First.bookAt_step (𝔐).N PS (At.told cF) (k03_book_at Zp cF) (k3K l false) hk
    (k03_tells_at h.toAtMg l hl false) s s' hsb.book (by rw [hsb.st]) hbook
  refine maskSeat_at y (D := (𝔐).sent) ((𝔐).seat3 y.link false) ?_ ?_ ?_ ?_ ?_ hbook' ?_ hT c hc
  · rw [eLive]
    exact F.liveShape (k3K l false) ((z, s), ()) hr hf
  · rw [eLive]
    exact F.liveGroups (k3K l false) ((z, s), ()) hr hf
  · rw [live_of_link hLv, ey]
    exact flink
  · rw [live_of_link hLv]
    exact fnext
  · rw [live_of_link hLv, ey]
    exact fown
  · have h0 := F.seatsCarried (k3K l false) ((z, s), ()) hr hf
    unfold Desc.K12.Door.atFirstSeats at h0 ⊢
    rw [hsb.book]
    exact h0

include h in
/-- **Behind the acceptance no heard row names the slot of the merge's end value.** Conditional on
`P5J.AtMgA`; a link in front of the head's; the acceptance of the decision; s being reached and
without a mark. No instance of these hypotheses is exhibited in this file. -/
theorem merge_behind_calls {l : ℕ} (h24 : l < 24) (p : Desc.First.Look.P) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Guest TS ProofFile.Cl)) (s s' : TS) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls K3Lot.ofForm) piece laid before p guests).decide s rs
      cols = .ok s')
    (z : ProofFile.InstPub) (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l false) (z, s))
    (hf : s.failed = none) :
    ∀ g, s'.lookHeard? = some g → ∀ f ∈ g.rows.toList, ∀ t ∈ f.slots.toList,
      mergeOf s' ≠ some t.1 := by
  intro g _ f _ t _
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have ek : k3K l false = 14 * l + 3 :=
    ((kOfCalls_border l).symm : k3K l false = kOfCalls l).trans (calls_number l h24)
  rw [ek] at hr
  have hp2 : (IM.k3Place l false).piece = 2 :=
    of_decide_eq_true (List.all_eq_true.1 calls_piece_two l (List.mem_range.2 h24))
  have hnone : mergeOf s = none := by
    rcases Meaning.K2.unheard_field_at h.scope h.reads O (X := ProofFile.InstPub × TS)
        (fun k a => Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a) (fun a => a)
        (fun _ _ ha => ha) (14 * l + 3) (z, s) (IM.k3Place l false) l hr hf
        (k03_calls_place l h24) rfl rfl hp2 with ⟨b, hb, q⟩ | ⟨b, hb, -⟩
    · have hb' : s.here = .lay b := hb
      unfold mergeOf
      rw [hb']
      show b.own.map (·.wo.sFv) = none
      rw [q.2.1]
      rfl
    · have hb' : s.here = .att b := hb
      unfold mergeOf
      rw [hb']
  rw [k3_calls_merge_kept _ _ _ _ _ _ _ _ _ _ hd, hnone]
  exact fun e => nomatch e

set_option maxHeartbeats 4000000 in
/-- **The new test formsInT l 2 "objects" holds behind the acceptance.** Conditional on `P5J.AtMgA`;
a link in front of the head's; the place and its shape; the acceptance of the decision; s being
reached and without a mark; the public tests and the book's test in front. No instance of these
hypotheses is exhibited in this file. -/
theorem objInT_calls {l : ℕ} (h24 : l < 24) {y : Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l false = some y) (hsP : (theP y).shape = some y.fs)
    (hpcX : (IM.k3Place l false).piece = Desc.K3.pieceAt (At.X Zp) l false) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Guest TS ProofFile.Cl)) (s s' : TS) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls K3Lot.ofForm) piece laid before (theP y) guests).decide
      s rs cols = .ok s')
    (z : ProofFile.InstPub) (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l false) (z, s))
    (hf : s.failed = none)
    (hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll (𝔐) mgBase).pub q (z, s) = true)
    (hbook : bookAt (𝔐).N PS[k3K l false]? s = true) :
    (mgAll (𝔐) mgBase).pub (.formsInT l 2 "objects") (z, s') = true := by
  have hl5 : l < 25 := by omega
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full l hl5
  have hsh : 2 + shift sub = 2 := hpc.symm.trans (k03_piece_calls l h24)
  have hruns := k03_runs_calls h l hl5 sub hs'
  rw [hsh] at hruns
  obtain ⟨lk, hRd, hfind, hfindG⟩ := k03_hfind2 h l hl5
  have hIn := (front_three (𝔐) mgBase (a := IM.k3Place l false) s rfl hpcX hpc hl5 hs'
    (calls_tests hl5).1 hlook rfl (hfit_mgAll (𝔐) mgBase rfl) z hfront).1
  exact objInT_state (𝔐) mgBase K3Lot.ofForm piece laid before guests s s' rs cols hd hIn hsP hruns
    k03_atS2_calls hRd k03_hpass k03_hsame hfind hfindG z
    (mask_behind_calls h hl5 hlook piece laid before guests s s' rs cols hd z hr hf hfront hbook)
    (merge_behind_calls h h24 _ piece laid before guests s s' rs cols hd z hr hf)

set_option maxHeartbeats 4000000 in
/-- **The debt `IM.MadeOwed` at the calls of a layers' link.** Conditional on `P5J.AtMgA`; the
library's own place of the lookup at the link; b being the member at the number; a fence inside
"reached". No instance of these hypotheses is exhibited in this file. -/
theorem madeOwed_calls_lay {l : ℕ} (hl : l < 25) {y : Desc.First.Look.Place}
    (hy : layAt (At.X Zp) l = some y) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) (Fk : ℕ → TS → Prop)
    (hFk : ∀ s, Fk (k3K l false) s →
      Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l false) (z, s)) :
    IM.MadeOwed Fk (𝔐).N IM.linksW IM.placesW (𝔐).pubD baseP z 0 (k3K l false) b b.place := by
  intro s s' hF hy' h0 _ hx q hq
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨he, hne⟩ := layAt_even hp4 hN hy
  have h24 : l < 24 := by omega
  have hsub := links_lay l h24 he
  obtain ⟨hpcW, P', sent, laid, rs, gs, hP, hd⟩ :=
    calls_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy'
  rw [O.W] at hpcW hP
  have hlook := k03_look_lay h hl hy
  have eP : P' = theP y := by
    have e0 : placeAt (At.X Zp) l false = some P' := hP
    unfold placeAt at e0
    rw [hlook] at e0
    exact (Option.some.inj e0).symm
  subst eP
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub = ModelPart.layers := Option.some.inj (hs'.symm.trans hsub)
  have ek : k3K l false = kOfCalls l := (kOfCalls_border l).symm
  have hr := hFk s hF
  have hr3 : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * l + 3) (z, s) := by
    rw [← calls_number l h24, ← ek]
    exact hr
  have hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll (𝔐) mgBase).pub q (z, s) = true := by
    rw [← ek]
    exact front_of_xk _ _ _ z (k3K l false) s hx
  have hbook : bookAt (𝔐).N PS[k3K l false]? s = true := by
    have h4 := (IM.xk_parts hx).2.2.2.1
    rw [IM.placesW_full] at h4
    exact h4
  have hpl : b.place = IM.k3Place l false := by
    have e1 := IM.place_at h.scope h.reads O hb
    rw [IM.placesW_full, K3Lot.k03_at_full l hl false] at e1
    exact (Option.some.inj e1).symm
  have hq' := behind_of_made _ _ _ _ q hq
  rw [hpl, ek] at hq'
  have hObj := objInT_calls h h24 hlook (k03_shape_lay hy) hpcW _ laid sent [] s s' rs gs hd z hr h0
    hfront hbook
  exact behind_lay_state (𝔐) mgBase K3Lot.ofForm _ laid sent [] s s' rs gs hd rfl hpcW hpc hl hsub
    (calls_tests hl).1 hlook (k03_shape_lay hy) rfl rfl
    (by rw [headLink_in_scope h.scope h.reads h.pubOne]; omega) (hfit_mgAll (𝔐) mgBase rfl)
    (k03_slots_lay h h24 hy) z hfront
    (fun o ho' => Meaning.K2.own_none_field_at h.scope h.reads O (X := ProofFile.InstPub × TS)
      (fun k a => Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a) (fun a => a)
      (fun _ _ ha => ha) (14 * l + 3) (z, s) (IM.k3Place l false) l hr3 h0
      (k03_calls_place l h24) rfl rfl hpc o ho')
    (Meaning.K2.lay_number_at h.scope h.reads O (X := ProofFile.InstPub × TS)
      (fun k a => Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a) (fun a => a)
      (fun _ _ ha => ha) l (z, s) h24 hr3 h0 (by rw [LPFK9.linksW_full]; exact hsub))
    hObj q hq'

set_option maxHeartbeats 4000000 in
/-- **The debt `IM.MadeOwed` at the calls of an attention link.** Conditional on `P5J.AtMgA`; the
library's own place of the lookup at the link; b being the member at the number; a fence inside
"reached". No instance of these hypotheses is exhibited in this file. -/
theorem madeOwed_calls_att {l : ℕ} (hl : l < 25) {y : Desc.First.Look.Place}
    {A : Attention.Shape} {tl : HTailF2} (hy : attAt (At.X Zp) l = some (y, A, tl))
    {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) (Fk : ℕ → TS → Prop)
    (hFk : ∀ s, Fk (k3K l false) s →
      Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l false) (z, s)) :
    IM.MadeOwed Fk (𝔐).N IM.linksW IM.placesW (𝔐).pubD baseP z 0 (k3K l false) b b.place := by
  intro s s' hF hy' h0 _ hx q hq
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have ho := attAt_odd hy
  have h24 : l < 24 := by omega
  have hsub := links_att l h24 ho
  obtain ⟨hpcW, P', sent, laid, rs, gs, hP, hd⟩ :=
    calls_hd_of_yes h.scope h.reads O h.laid.planOk hl hb hy'
  rw [O.W] at hpcW hP
  have hlook := k03_look_att h hl hy
  have eP : P' = theP y := by
    have e0 : placeAt (At.X Zp) l false = some P' := hP
    unfold placeAt at e0
    rw [hlook] at e0
    exact (Option.some.inj e0).symm
  subst eP
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub = ModelPart.attention := Option.some.inj (hs'.symm.trans hsub)
  have ek : k3K l false = kOfCalls l := (kOfCalls_border l).symm
  have hr := hFk s hF
  have hr3 : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * l + 3) (z, s) := by
    rw [← calls_number l h24, ← ek]
    exact hr
  have hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll (𝔐) mgBase).pub q (z, s) = true := by
    rw [← ek]
    exact front_of_xk _ _ _ z (k3K l false) s hx
  have hbook : bookAt (𝔐).N PS[k3K l false]? s = true := by
    have h4 := (IM.xk_parts hx).2.2.2.1
    rw [IM.placesW_full] at h4
    exact h4
  have hpl : b.place = IM.k3Place l false := by
    have e1 := IM.place_at h.scope h.reads O hb
    rw [IM.placesW_full, K3Lot.k03_at_full l hl false] at e1
    exact (Option.some.inj e1).symm
  have hq' := behind_of_made _ _ _ _ q hq
  rw [hpl, ek] at hq'
  have hObj := objInT_calls h h24 hlook (attAt_shape hy) hpcW _ laid sent [] s s' rs gs hd z hr h0
    hfront hbook
  exact behind_att_state (𝔐) mgBase K3Lot.ofForm _ laid sent [] s s' rs gs hd rfl hpcW hpc hl hsub
    (calls_tests hl).1 hlook (attAt_shape hy) rfl rfl
    (by rw [headLink_in_scope h.scope h.reads h.pubOne]; omega) (hfit_mgAll (𝔐) mgBase rfl)
    (k03_slots_att h h24 hy) z hfront
    (fun o ho' => Meaning.K2.heard5_none_field_at h.scope h.reads O (X := ProofFile.InstPub × TS)
      (fun k a => Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a) (fun a => a)
      (fun _ _ ha => ha) (14 * l + 3) (z, s) (IM.k3Place l false) l hr3 h0
      (k03_calls_place l h24) rfl rfl hpc o ho')
    hObj q hq'

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.mask_behind_calls
#print axioms ProofFile.Honest.K3.Law.Total.merge_behind_calls
#print axioms ProofFile.Honest.K3.Law.Total.objInT_calls
#print axioms ProofFile.Honest.K3.Law.Total.madeOwed_calls_lay
#print axioms ProofFile.Honest.K3.Law.Total.madeOwed_calls_att
