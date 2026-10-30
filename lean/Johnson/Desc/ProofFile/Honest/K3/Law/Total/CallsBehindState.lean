-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/CallsBehindState.lean: the kind "lookup" (K3).
Conditional: behind an acceptance of the decision of the lookup on a link's calls the public tests
that the table of borders asks there hold, all but the five that the library's own rule shows
(`paidCallsR`, Johnson/Desc/First/Look/K3CallsBehindR.lean); said of two states of the verifier. At
the library's composed meaning, for every value of its data. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the table of borders is Johnson/Desc/First/Borders.lean,
whose head calls it the table of joints. A public test is the Boolean test of a public item: the
meaning's field pub. The tests in front and behind are the lists `frontAtK mgMore k` and
`behindAtK mgMore k a` (Johnson/Desc/Sound/MgAt/K3CallsTable.lean), at the head's link `headFront`
and `headBehind` (Johnson/Desc/Sound/MgAt/K3HeadBehindAt.lean).

What is shown.
  `othersPub_att_state`: at an attention link.
  `othersPub_lay_state`: at a layers' link.
  `othersPub_head_state`: at the head's link.
  `objInT_state`: the one new test that is neither the kind's own nor a caller's: formsInT l pc
    "objects", the piece being a letter.
The statements speak of two states alone: no piece, transcript or string occurs in them, nor the
table's promise as a whole, nor "reached".

Hypotheses that remain. None of them is shown in this file.
  `hd`: the decision of the kind's sub-protocol accepts from s to s'.
  `hsb`: the library's `SameBut` (Johnson/Desc/First/Look/K3CallsTurns.lean) between the two states.
  `hfront`: the public tests that are open or tied in front hold at s.
  public facts on the place and the table: `hla`, `hpcX`, `hpc`, `hl`, `hsub`, `here`, `hlook`,
    `hsP`, `hhd`, `hfit`, `hns`, `hmH`.
  terms of the composed meaning: `hmore` (named `hM` in the third theorem), `hlinks`, `hBase`; in
    the fourth theorem `hruns`, `hA`, `hlink`, `hpass`, `hsame`, `hfind`, `hfindG`.
  `hIn`: (in the fourth theorem) the lookup's promise in front holds at s (`k3OnIn`).
  facts on the state in front: `hh5`, `hown`, `hlay`: the calling kind's own rounds are not yet
    heard; a layers' link stands open.
  facts on the state behind: `hObj` (which is the conclusion of the fourth theorem), `hmask`,
    `hmerge`.

Follows. The four proofs are the library's own,
taken over by a program from their texts: `othersPub_att_mgAll` and `othersPub_lay_mgAll`
(Johnson/Desc/Sound/MgAt/K3CallsOthers.lean), `head_bPub_mgAll` (K3HeadBehindAt.lean), `objIn_pc`
(Johnson/Desc/Sound/MgAt/K3CallsObjInPc.lean). These stand at a piece's acceptance with a
transcript, under the table's whole promise in front, "reached" and "no mark in front". Their first
step arrives at the decision of `K3.block` (Johnson/Desc/First/Look/K3Lookup.lean); from there on each
line speaks of the two states alone. This file parts from them in the following, and nowhere else.
  (1): that first step is removed (`seat_yes`, Johnson/Desc/First/Look/K3CallsMeanOf.lean; at the
    head's link `k3_calls_stated_yes`, Johnson/Desc/First/Look/K3CallsStatedYes.lean), and what it
    yields is a hypothesis: `hd`. With it go the stated sub-protocol, its test on the plan, the
    piece and its seat.
  (2): the promise in front gives way to what the proofs draw out of it by `onQ_front`
    (K3CallsOthers.lean): `hfront`.
  (3): the hypotheses that were asked at every reached state without a mark are asked at the one
    state at which the proofs use them; "reached" and "no mark in front" go.
  (4): u.1 and v.1 are s and s'.
  (5): the lists of items in front and behind are stated at the library's closed list of extra
    public tests (`mgMore`), theirs at the composed meaning's own list. So their rewritings of these
    two hypotheses by "the two lists are one" are removed; that equation is still made and used.
  (6): at the head's link the piece's number is a hypothesis (`hpc`): they draw it from the stated
    sub-protocol, which has gone.
  (7): at the head's link their letter T is `hsb`.
Every other line is theirs token for token: of the 228 lines of the four proofs 215, counted by a
program.

Users. `behind_att_state`, `behind_lay_state` and `behind_head_state`
(Honest/K3/Law/Total/CallsBehindAll.lean) call the first three; `objInT_calls`
(Honest/K3/Law/Total/MadeOwedCalls.lean) and `objInT_head`
(Honest/K3/Law/Total/MadeOwedCallsHead.lean) call the fourth.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
At no two states have the hypotheses been shown to hold together. At the written full list of links
and the library's closed list of extra public tests alone. The five items of `paidCallsR` are not
here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.Sound.MgAt.K3CallsOthers
import Johnson.Desc.Sound.MgAt.K3HeadBehindAt
import Johnson.Desc.Sound.MgAt.K3CallsObjInPc

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  pubFit shift pubStep pubRowM stepOpen pubOfItems)
open VerifiableInference.Desc.First (pubAll pubAll_look_att pubAll_look_lay pubAll_callerIn_att
  pubAll_callerIn_lay pubAll_more_sentIs pubAll_more_treesAre pubAll_more_rowsBare
  pubAll_more_lookLeft pubAll_more_readsThere pubAll_tokenSmall pubAll_look_head)
open VerifiableInference.Desc (Link)
open VerifiableInference.Desc.K9 (segAt? readersOfLink statesOfLink LinkHoles maskSeat mergeOf)

section
variable {Xi P Tok Cl : Type} {rows cols₀ nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols₀ nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols₀) Tok MsgT)) (claim : Aff → Cl)
  {l : ℕ} {x : Desc.First.Look.Place} {a : Desc.Place}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **The other kinds' public tests behind the acceptance, at an attention link.** Here s is the
verifier's state in front of the lookup on the calls and s' the state behind the acceptance of its
decision. Conditional on that acceptance; `SameBut`; the tests that are open or tied in front;
nothing of attention's own rounds heard in front; the test formsInT l 2 "objects" behind; public
facts and terms. No instance of these hypotheses is exhibited in this file. -/
theorem othersPub_att_state (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide s rs cols =
      .ok s')
    (hsb : SameBut s s') (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hl : l < 25) (hsub : linksFull[l]? = some .attention) (here : PS[kOfCalls l]? = some a)
    (hlook : lookAt X l false = some x) (hsP : (theP).shape = some x.fs)
    (hmore : Mg.more = {}) (hlinks : Dm.links = linksFull) (hhd : l ≠ headLink X)
    (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (z : P)
    (hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll Dm Mg).pub q (z, s) = true)
    (hh5 : ∀ o, s.here = .att o → o.heard5 = none)
    (hObj : (mgAll Dm Mg).pub (.formsInT l 2 "objects") (z, s') = true) :
    ∀ p ∈ behindAtK mgMore (kOfCalls l) a, p ∉ paidCallsR l 2 →
      (mgAll Dm Mg).pub p (z, s') = true := by
  intro p hp hnp
  have hM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hmore
  obtain ⟨hsort, hkept⟩ := calls_sorted hl hsub here
  have hpc2 : a.piece = 2 + shift .attention := hpc
  have hIn : Desc.K3.k3OnIn theP s = true :=
    k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l false hlook z s (by
      rw [← hpcX, hpc]
      exact hfront _ (List.mem_append_left _ (by
        rw [← hM]
        exact calls_asks_open (mgAll Dm Mg).more linksFull PS (kOfCalls l) a l .attention hfit here
          hla hsub hpc2 _ (by simp [shift])))))
  have hT : ∀ r ∈ keptCalls l .attention, (mgAll Dm Mg).pub r (z, s) = true := fun r hr' =>
    hfront r (hkept r hr')
  have hmH : (l == Dm.pubD.mH) = false := by
    rw [beq_eq_false_iff_ne]
    exact hhd
  have hLay : Desc.First.FillK4.isLay Dm.pubD.links l = false := by
    show (Dm.links[l]? == some ModelPart.layers) = false
    rw [hlinks, hsub]
    rfl
  have hAtt : Dm.pubD.d5.isAtt l = true := by
    show (Dm.links[l]? == some ModelPart.attention) = true
    rw [hlinks, hsub]
    rfl
  obtain ⟨o, o', ho, -⟩ : ∃ o o', s.here = .att o ∧ s'.here = .att o' := by
    have hl0 := hT (.more (some l) "K5.readsThere") (by simp [keptCalls])
    rw [mgAll_pub, pubAll_more_readsThere Dm.pubD Mg.pub l hAtt] at hl0
    rcases hsb.sort with ⟨o, o', h1, -⟩ | h2 | ⟨o, o', h1, -⟩
    · unfold H2K5.Door.readsThereB at hl0
      rw [h1] at hl0
      cases hl0
    · exact h2
    · unfold H2K5.Door.readsThereB at hl0
      rw [h1] at hl0
      cases hl0
  rcases hsort p hp with h1 | h1 | h1
  · exact absurd (hpc ▸ h1) hnp
  · have ht := hT p h1
    simp only [keptCalls, List.mem_cons, List.not_mem_nil, or_false] at h1
    rw [mgAll_pub] at ht ⊢
    rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact three_stay Dm.pubD Mg.pub z hsb _ (by simp) ht
    · rw [pubAll_more_sentIs] at ht ⊢
      exact sentIs_kept claim piece laid before theP guests s s' rs cols hd _ _ ht
    · rw [pubAll_more_treesAre] at ht ⊢
      exact treesAre_kept claim piece laid before theP guests s s' rs cols hsP hd hIn _ _ ht
    · rw [pubAll_more_readsThere Dm.pubD Mg.pub l hAtt] at ht ⊢
      exact readsThere_kept claim piece laid before theP guests s s' rs cols hsP hd hIn _ _ ht
    · rw [Desc.First.pubAll_more_liveReq Dm.pubD Mg.pub l hAtt] at ht ⊢
      exact liveReq_kept claim piece laid before theP guests s s' rs cols hd _ ht
    · exact three_stay Dm.pubD Mg.pub z hsb _ (by simp) ht
    · exact three_stay Dm.pubD Mg.pub z hsb _ (by simp) ht
  · simp only [newCalls, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl | rfl
    · rw [mgAll_pub, pubAll_look_att Dm.pubD Mg.pub l hmH hLay hAtt]
      exact look_att_made claim piece laid before theP guests s s' rs cols hsP hd hIn ho
    · rw [mgAll_pub, pubAll_callerIn_att Dm.pubD Mg.pub l hLay hAtt]
      have e5 : Dm.pubD.d5.first? l = some ((theP).first + Forest.elems x.fs) :=
        nextOf_is hlook hsP
      rw [e5, Option.any_some]
      exact callerIn_att_made claim piece laid before theP guests s s' rs cols hsP hd hIn ho
        (hh5 o ho) rfl
    · exact hObj

/-- **The same at a layers' link.** Conditional on the like, with: a layers' link stands open in
front, nothing of its own rounds is heard, and the built link has the place's number of slots.
No instance of these hypotheses is exhibited in this file. -/
theorem othersPub_lay_state (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide s rs cols =
      .ok s')
    (hsb : SameBut s s') (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hl : l < 25) (hsub : linksFull[l]? = some .layers) (here : PS[kOfCalls l]? = some a)
    (hlook : lookAt X l false = some x) (hsP : (theP).shape = some x.fs)
    (hmore : Mg.more = {}) (hlinks : Dm.links = linksFull) (hhd : l ≠ headLink X)
    (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hns : (Dm.built[l]?).map (·.ns) = some (theP).ns)
    (z : P)
    (hfront : ∀ q ∈ frontAtK mgMore (kOfCalls l), (mgAll Dm Mg).pub q (z, s) = true)
    (hown : ∀ o, s.here = .lay o → o.own = none) (hlay : ∃ o, s.here = .lay o)
    (hObj : (mgAll Dm Mg).pub (.formsInT l 2 "objects") (z, s') = true) :
    ∀ p ∈ behindAtK mgMore (kOfCalls l) a, p ∉ paidCallsR l 2 →
      (mgAll Dm Mg).pub p (z, s') = true := by
  intro p hp hnp
  have hM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hmore
  obtain ⟨hsort, hkept⟩ := calls_sorted hl hsub here
  have hpc2 : a.piece = 2 + shift .layers := hpc
  have hIn : Desc.K3.k3OnIn theP s = true :=
    k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l false hlook z s (by
      rw [← hpcX, hpc]
      exact hfront _ (List.mem_append_left _ (by
        rw [← hM]
        exact calls_asks_open (mgAll Dm Mg).more linksFull PS (kOfCalls l) a l .layers hfit here hla
          hsub hpc2 _ (by simp [shift])))))
  have hT : ∀ r ∈ keptCalls l .layers, (mgAll Dm Mg).pub r (z, s) = true := fun r hr' =>
    hfront r (hkept r hr')
  have hmH : (l == Dm.pubD.mH) = false := by
    rw [beq_eq_false_iff_ne]
    exact hhd
  have hLay : Desc.First.FillK4.isLay Dm.pubD.links l = true := by
    show (Dm.links[l]? == some ModelPart.layers) = true
    rw [hlinks, hsub]
    rfl
  have hLay' : (Dm.pubD.links[l]? == some ModelPart.layers) = true := hLay
  obtain ⟨o, ho⟩ := hlay
  obtain ⟨o', ho'⟩ : ∃ o', s'.here = .lay o' := by
    rcases hsb.sort with ⟨_, o', -, h2⟩ | ⟨o1, _, h1, -⟩ | ⟨o1, _, h1, -⟩
    · exact ⟨o', h2⟩
    · rw [ho] at h1
      cases h1
    · rw [ho] at h1
      cases h1
  -- the ledger in front: sized, the place's number of slots, free from its next slot on
  obtain ⟨F, hF, hz, -, -⟩ := k3OnIn_free hsP hIn
  have hQ : LeftQ (theP).ns F := by
    have f0 : (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true :=
      hfront _ (List.mem_append_left _ (by
        rw [← hM]
        exact calls_asks_open (mgAll Dm Mg).more linksFull PS (kOfCalls l) a l .layers hfit here hla
          hsub hpc2 _ (by simp)))
    have f1 : ((Dm.pubD.nsOf l).any fun n => Desc.First.freeAboveB n s) = true := f0
    have hns' : Dm.pubD.nsOf l = some (theP).ns := hns
    rw [hns', Option.any_some, freeAboveB_is] at f1
    unfold freeAboveAtB at f1
    simp only [Bool.and_eq_true] at f1
    have f2 := f1.2
    rw [hF] at f2
    simp only [Option.any_some, beq_iff_eq] at f2
    have f3 := f1.1
    unfold freeAboveB at f3
    rw [hF] at f3
    simp only [Option.any_some, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at f3
    refine ⟨hz, f2, fun j hj hlt => ?_⟩
    have q0 := f3 (j - F.next) (by omega)
    rw [show F.next + (j - F.next) = j by omega] at q0
    exact q0
  rcases hsort p hp with h1 | h1 | h1
  · exact absurd (hpc ▸ h1) hnp
  · have ht := hT p h1
    simp only [keptCalls, List.mem_cons, List.not_mem_nil, or_false] at h1
    rw [mgAll_pub] at ht ⊢
    rcases h1 with rfl | rfl | rfl | rfl | rfl
    · exact three_stay Dm.pubD Mg.pub z hsb _ (by simp) ht
    · rw [pubAll_more_sentIs] at ht ⊢
      exact sentIs_kept claim piece laid before theP guests s s' rs cols hd _ _ ht
    · rw [pubAll_more_treesAre] at ht ⊢
      exact treesAre_kept claim piece laid before theP guests s s' rs cols hsP hd hIn _ _ ht
    · exact three_stay Dm.pubD Mg.pub z hsb _ (by simp) ht
    · exact three_stay Dm.pubD Mg.pub z hsb _ (by simp) ht
  · simp only [newCalls, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl | rfl | rfl | rfl
    · rw [mgAll_pub, pubAll_look_lay Dm.pubD Mg.pub l hmH hLay]
      exact look_lay_made claim piece laid before theP guests s s' rs cols hsP hd hIn ho
    · rw [mgAll_pub, pubAll_callerIn_lay Dm.pubD Mg.pub l hLay]
      have e5 : Dm.pubD.nextOf l = some ((theP).first + Forest.elems x.fs) :=
        nextOf_is hlook hsP
      rw [e5, Option.any_some]
      exact callerIn_lay_made claim piece laid before theP guests s s' rs cols hsP hd hIn ho
        (hown o ho) rfl
    · rw [mgAll_pub, pubAll_more_rowsBare Dm.pubD Mg.pub l hLay']
      exact rowsBare_lay_made claim piece laid before theP guests s s' rs cols hsP hd hF hQ ho'
    · rw [mgAll_pub, pubAll_more_lookLeft Dm.pubD Mg.pub l hLay']
      exact lookLeft_lay_made claim piece laid before theP guests s s' rs cols hsP hd hF hQ ho'
    · exact hObj

/-- **The same at the head's link.** Conditional on the acceptance; `SameBut`; the tests in front;
the test formsInT 24 3 "objects" behind; the meaning beneath has no extra public test and reads no
state; the head's link is 24. No instance of these hypotheses is exhibited in this file. -/
theorem othersPub_head_state (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide s rs cols =
      .ok s')
    (hsb : SameBut s s') (hM : Mg.more = {})
    (hBase : ∀ r (z : P) (s s' : Desc.First.S), Mg.pub r (z, s') = Mg.pub r (z, s))
    (hmH : headLink X = 24) (hlook : lookAt X 24 false = some x)
    (hpc : 2 + shift ModelPart.head = Desc.K3.pieceAt X 24 false) (z : P)
    (hfront : ∀ r ∈ headFront mgMore, (mgAll Dm Mg).pub r (z, s) = true)
    (hObj : (mgAll Dm Mg).pub (.formsInT 24 3 "objects") (z, s') = true) :
    ∀ p ∈ headBehind mgMore, p ∉ paidCallsR 24 (2 + shift ModelPart.head) →
      (mgAll Dm Mg).pub p (z, s') = true := by
  intro p hp hpaid
  have eM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hM
  have hIn : Desc.K3.k3OnIn
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) s = true := by
    have hOpen := calls_asks_open (mgAll Dm Mg).more linksFull PS (k3K 24 false)
      (IM.k3Place 24 false) 24 ModelPart.head (hfit_mgAll Dm Mg hM)
      (K3Lot.k03_at_full 24 (by decide) false) rfl (by decide) rfl
      (.lookIn 24 (2 + shift ModelPart.head)) (by simp)
    rw [eM] at hOpen
    have h0 := hfront _ (List.mem_append_left _ hOpen)
    have h3 : 2 + shift ModelPart.head = Desc.K3.pieceAt X 24 false := hpc
    rw [h3] at h0
    exact k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) 24 false hlook z s h0)
  obtain ⟨hs, hsh⟩ : ∃ hs,
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).shape = some hs := by
    cases e : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).shape with
    | none =>
      unfold Desc.K3.k3OnIn at hIn
      rw [e] at hIn
      cases hIn
    | some hs => exact ⟨hs, rfl⟩
  have hK : ∀ r ∈ headKept, (mgAll Dm Mg).pub r (z, s) = true := fun r hr =>
    hfront r (of_decide_eq_true (List.all_eq_true.1 head_kept_front r hr))
  have hseven : p ∈ headKept ++ headNew :=
    (of_decide_eq_true (List.all_eq_true.1 head_sorted p hp)).resolve_left hpaid
  simp only [headKept, headNew, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hseven
  rcases hseven with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h0 := hK .tokenSmall (by simp [headKept])
    rw [mgAll_pub, pubAll_tokenSmall] at h0 ⊢
    exact tokenSmall_kept (hd := hd) (h0 := h0)
  · have h0 := hK .indexIs (by simp [headKept])
    rw [mgAll_pub] at h0 ⊢
    exact sameBut_rides Dm.pubD Mg.pub _ (k3_three_ride _) z hsb (fun r _ => hBase r z s s') _
      (by simp) h0
  · have h0 := hK .indexThere (by simp [headKept])
    rw [mgAll_pub] at h0 ⊢
    exact sameBut_rides Dm.pubD Mg.pub _ (k3_three_ride _) z hsb (fun r _ => hBase r z s s') _
      (by simp) h0
  · have h0 := hK (.more (some 24) "frame.sentIs") (by simp [headKept])
    rw [mgAll_pub, pubAll_more_sentIs] at h0 ⊢
    exact sentIs_kept (hd := hd) (h0 := h0)
  · have h0 := hK (.more (some 24) "ledger.treesAre") (by simp [headKept])
    rw [mgAll_pub, pubAll_more_treesAre] at h0 ⊢
    exact treesAre_kept (hs := hsh) (hd := hd) (hIn := hIn) (h0 := h0)
  · have e24 : ((24 : ℕ) == Dm.pubD.mH) = true := by
      show ((24 : ℕ) == headLink X) = true
      rw [hmH]
      rfl
    rw [mgAll_pub, pubAll_look_head _ _ 24 e24]
    exact look_head_made (hs := hsh) (hd := hd) (hIn := hIn) (hS := Dm.pubD.hShape)
      (iU3 := Dm.pubD.iU3)
  · exact hObj

end

section
variable {Xi P Tok : Type} {rows cols₀ nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols₀ nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols₀) Tok MsgT)) (claim : Aff → Desc.Claim)
  {l pc : ℕ} {x : Desc.First.Look.Place}
  {pr : ℕ} {H : LinkHoles} {lk : Link Desc.First.S Desc.Claim}
  {pass : Desc.First.S → Desc.First.S → Prop}

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **formsInT l pc "objects" holds behind the acceptance.** Conditional on the acceptance; the
lookup's promise in front; terms of the composed meaning's readers at the link; behind: the mask
row's message has a seat among the link's own, and no heard row names the slot of the merge's end
value. No instance of these hypotheses is exhibited in this file. -/
theorem objInT_state (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Desc.Claim)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before theP guests).decide s rs cols =
      .ok s')
    (hIn : Desc.K3.k3OnIn theP s = true) (hsP : (theP).shape = some x.fs)
    (hruns : Dm.runs l pc "objects" = [(pr, "objects"), (pr, "guests")])
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hlink : Dm.Rd l = readersOfLink H lk)
    (hpass : ∀ t G, pass t (t.putFork G)) (hsame : ∀ t, pass t t)
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hfindG : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "guests") = some (nm, run) ∧
      RunOver pass run (guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim))))
    (z : P)
    (hmask : ∀ c, segAt? s' = some c → (maskSeat (Dm.N.sent l 0) c).isSome = true)
    (hmerge : ∀ g, s'.lookHeard? = some g → ∀ f ∈ g.rows.toList, ∀ y ∈ f.slots.toList,
      mergeOf s' ≠ some y.1) :
    (mgAll Dm Mg).pub (.formsInT l pc "objects") (z, s') = true := by
  obtain ⟨F, F', g, rs', hF, hz, -, -, -, -, hF', hg, L, -⟩ :=
    k3_calls_made claim piece laid before theP guests s s' rs cols hsP hd hIn
  obtain ⟨F1, y, hF1, hn1, e1, hN⟩ :=
    decide_named (Desc.K3.seatCalls claim) piece laid before theP guests s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((Desc.K3.seatCalls claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : (Desc.K3.seatCalls claim).heard s' = some y.1 := by
    rw [e1]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn1
  have hF1' : (Desc.K3.seatCalls claim).fork s' = some y.2 := by
    rw [e1]
    exact seatCalls_keeps claim _ _ _ hsome hn1
  have ey1 : y.1 = g := Option.some.inj (hg1.symm.trans hg)
  have ey2 : y.2 = F' := Option.some.inj (hF1'.symm.trans hF')
  have hNm := (hN hz).rows
  rw [ey1, ey2] at hNm
  obtain ⟨Lc, hLc⟩ := link_some_of_fork hF'
  obtain ⟨c, hc, -, hcF, -, -⟩ := segAt_make hLc hF' (tl_some_of_fork hF')
  show pubAll Dm.pubD Mg.pub (.formsInT l pc "objects") (z, s') = true
  show ((Dm.runs l pc "objects").all fun p =>
    Desc.K9.formsInT (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 s') = true
  rw [hruns, hlink]
  show (Desc.K9.formsInT (readersOfLink H lk) (Dm.N.sent l 0) pr "objects" s' &&
    (Desc.K9.formsInT (readersOfLink H lk) (Dm.N.sent l 0) pr "guests" s' && true)) = true
  rw [Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, guests_formsInT H lk pr (Dm.N.sent l 0) pass hsame hfindG hc⟩
  exact objects_formsInT H lk pr (Dm.N.sent l 0) (Desc.K3.seatCalls claim) hA pass hpass hfind hc
    hg (by rw [hcF]; exact hNm) (by rw [hcF]; exact L.padLeft.fit)
    (hmask c hc) (hmerge g hg)

end

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.othersPub_att_state
#print axioms ProofFile.Honest.K3.Law.Total.othersPub_lay_state
#print axioms ProofFile.Honest.K3.Law.Total.othersPub_head_state
#print axioms ProofFile.Honest.K3.Law.Total.objInT_state
