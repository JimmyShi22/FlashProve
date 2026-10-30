-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsOthers.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING
mgAll: THE FIELD othersPub OF AttRestR, LayRestR AND CallsLeftR
(Johnson/Desc/Sound/MgAt/K3CallsRestR.lean, K3CallsLeftR.lean): "the other kinds' public tests that
are open or tied behind hold behind", ITEM BY ITEM. Which items these are: a test on the table by
the kernel (calls_sorted, MgAt/K3CallsTable.lean). What is open on both sides stays: unheard,
indexIs, indexThere by their own texts (three_stay: they read the statement and what goes out,
which SameBut keeps); "frame.sentIs", "ledger.treesAre", "K5.readsThere",
"K5.liveReq" by K3CallsKept.lean. What is new is made by the accept: look, callerIn, "K4.rowsBare",
"K4.lookLeft" by K3CallsMade.lean and K3CallsMadeAtt.lean. By calls alone. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the composed public tests pubAll at the state behind an accept.
Used by K03OthersPubAt.lean (Johnson/P5J/) · K3CallsAsks.lean, K3CallsPaid.lean
  (Johnson/Desc/Sound/MgAt/) and 11 more.
LETTERS: those of MgAt/K3CallsRestR.lean; the border is kOfCalls l.

WHAT IS LEFT, EACH A NAMED PREMISE, BOOKED: accept: hObj (the new test formsInT l 2
  "objects" at the state behind) · fold fact: hown (layers: in front of the lookup on the calls the
  caller's own rounds are not yet heard) | hh5 (attention: the like) · term: hmore (the meaning
  beneath has no extra public test), hlinks (mgAll's list of sorts is the written one) ·
  test: hfit, hns (the layers alone), hhd, hsP and the place's facts.

Main names: `onQ_front` · `three_stay` · `othersPub_att_mgAll`, `othersPub_lay_mgAll`.

Limits. Attention and the layers; the head's calls are not in this file. The closed list mgMore.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsMean
import Johnson.Desc.Sound.MgAt.K3CallsTable
import Johnson.Desc.First.Look.K3CallsMadeAtt
import Johnson.Desc.First.Look.K3CallsKept
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc smpWc strWc)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open VerifiableInference.Desc.First (pubAll pubAll_look_att pubAll_look_lay pubAll_callerIn_att
  pubAll_callerIn_lay pubAll_more_sentIs pubAll_more_treesAre pubAll_more_rowsBare
  pubAll_more_lookLeft pubAll_more_readsThere)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

/-- **What the unmarked arm of the table's promise holds of the public tests**: the open ones and
the tied ones. -/
theorem onQ_front {P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart}
    {ps : List Desc.Place} {pi : P} {k : ℕ} {a : Desc.First.S × Fr.E.Str}
    (h : onQ N Mg links ps (fun s => (pi, s)) k a) (hu : a.1.failed = none) :
    ∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [] ++
        pubOfItems ((openSets links ps (start links))[k]?.getD []),
      Mg.pub q (pi, a.1) = true := by
  obtain ⟨-, hm | ⟨h1, -, -, -⟩⟩ := h
  · exact absurd hu hm
  · simp only [Bool.and_eq_true] at h1
    have hp := h1.1.2
    unfold Desc.First.pubHeld at hp
    rw [List.all_eq_true] at hp
    exact hp

/-- **Three tests that read the statement and what goes out alone stay.** -/
theorem three_stay {P : Type} (D : Desc.First.PubData) (base : Pub → P × Desc.First.S → Bool)
    (z : P) {s s' : Desc.First.S} (T : SameBut s s') (q : Pub)
    (hq : q = .unheard ∨ q = .indexIs ∨ q = .indexThere) (ht : pubAll D base q (z, s) = true) :
    pubAll D base q (z, s') = true := by
  rcases hq with rfl | rfl | rfl
  · have h0 : s.out.reply.isNone = true := ht
    show s'.out.reply.isNone = true
    rw [T.out]
    exact h0
  · have h0 : (s.out.indexMasks == D.N.indexNo) = true := ht
    show (s'.out.indexMasks == D.N.indexNo) = true
    rw [T.out]
    exact h0
  · have h0 : (s.st.oracles[s.out.indexMasks]?).isSome = true := ht
    show (s'.st.oracles[s'.out.indexMasks]?).isSome = true
    rw [T.out, T.st]
    exact h0

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Cl)
  (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes) (shape : Params.ReqShape)
  {l : ℕ} {x : Desc.First.Look.Place} {a : Desc.Place} {b' : Desc.Block Desc.First.S Cl}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT)}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- The number that both callers' tests name is the place's first slot and the lookup's count. -/
theorem nextOf_is (hlook : lookAt X l false = some x) (hsP : (theP).shape = some x.fs) :
    (placeAt X l false).bind (fun pC => pC.shape.map fun hC => pC.first + Forest.elems hC) =
      some ((theP).first + Forest.elems x.fs) := by
  unfold placeAt
  rw [hlook]
  show ((theP).shape.map fun hC => (theP).first + Forest.elems hC) = _
  rw [hsP]
  rfl

/-- **othersPub, at an attention link.** -/
theorem othersPub_att_mgAll
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = []) (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hl : l < 25) (hsub : linksFull[l]? = some .attention) (here : PS[kOfCalls l]? = some a)
    (hlook : lookAt X l false = some x) (hsP : (theP).shape = some x.fs)
    (hmore : Mg.more = {}) (hlinks : Dm.links = linksFull) (hhd : l ≠ headLink X)
    (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hh5 : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → ∀ o, u.1.here = .att o → o.heard5 = none)
    (hObj : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (kOfCalls l) u →
      Rch (kOfCalls l) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      (mgAll Dm Mg).pub (.formsInT l 2 "objects") (z, v.1) = true) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (kOfCalls l) u →
      Rch (kOfCalls l) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[kOfCalls l]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[kOfCalls l]?.getD [])
            (Desc.First.rowOf linksFull a)),
        p ∉ paidCallsR l 2 → (mgAll Dm Mg).pub p (z, v.1) = true := by
  intro B' hB z u v hu hr hf hy hsb p hp hnp
  have e : placeAt X l false = some theP := by
    unfold placeAt
    rw [hlook]
    rfl
  obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ :=
    seat_yes claim readers codes shape h hOk hla hpcX e hback B' hB u v hy
  have hM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hmore
  have hfront := onQ_front hu hf
  rw [hM] at hp hfront
  obtain ⟨hsort, hkept⟩ := calls_sorted hl hsub here
  have hpc2 : a.piece = 2 + shift .attention := hpc
  have hIn : Desc.K3.k3OnIn theP u.1 = true :=
    k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l false hlook z u.1 (by
      rw [← hpcX, hpc]
      exact hfront _ (List.mem_append_left _ (by
        rw [← hM]
        exact calls_asks_open (mgAll Dm Mg).more linksFull PS (kOfCalls l) a l .attention hfit here
          hla hsub hpc2 _ (by simp [shift])))))
  have hT : ∀ r ∈ keptCalls l .attention, (mgAll Dm Mg).pub r (z, u.1) = true := fun r hr' =>
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
  obtain ⟨o, o', ho, -⟩ : ∃ o o', u.1.here = .att o ∧ v.1.here = .att o' := by
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
      exact sentIs_kept claim piece laid before theP guests u.1 v.1 rs cols hd _ _ ht
    · rw [pubAll_more_treesAre] at ht ⊢
      exact treesAre_kept claim piece laid before theP guests u.1 v.1 rs cols hsP hd hIn _ _ ht
    · rw [pubAll_more_readsThere Dm.pubD Mg.pub l hAtt] at ht ⊢
      exact readsThere_kept claim piece laid before theP guests u.1 v.1 rs cols hsP hd hIn _ _ ht
    · rw [Desc.First.pubAll_more_liveReq Dm.pubD Mg.pub l hAtt] at ht ⊢
      exact liveReq_kept claim piece laid before theP guests u.1 v.1 rs cols hd _ ht
    · exact three_stay Dm.pubD Mg.pub z hsb _ (by simp) ht
    · exact three_stay Dm.pubD Mg.pub z hsb _ (by simp) ht
  · simp only [newCalls, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl | rfl
    · rw [mgAll_pub, pubAll_look_att Dm.pubD Mg.pub l hmH hLay hAtt]
      exact look_att_made claim piece laid before theP guests u.1 v.1 rs cols hsP hd hIn ho
    · rw [mgAll_pub, pubAll_callerIn_att Dm.pubD Mg.pub l hLay hAtt]
      have e5 : Dm.pubD.d5.first? l = some ((theP).first + Forest.elems x.fs) :=
        nextOf_is hlook hsP
      rw [e5, Option.any_some]
      exact callerIn_att_made claim piece laid before theP guests u.1 v.1 rs cols hsP hd hIn ho
        (hh5 z u hr hf o ho) rfl
    · exact hObj B' hB z u v hu hr hf hy hsb

/-- **othersPub, at a layers' link.** -/
theorem othersPub_lay_mgAll
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = []) (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hpc : a.piece = 2)
    (hl : l < 25) (hsub : linksFull[l]? = some .layers) (here : PS[kOfCalls l]? = some a)
    (hlook : lookAt X l false = some x) (hsP : (theP).shape = some x.fs)
    (hmore : Mg.more = {}) (hlinks : Dm.links = linksFull) (hhd : l ≠ headLink X)
    (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (hns : (Dm.built[l]?).map (·.ns) = some (theP).ns)
    (hown : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → ∀ o, u.1.here = .lay o → o.own = none)
    (hlay : ∀ (z : P) (u : Desc.First.S × Fr.E.Str), Rch (kOfCalls l) ((z, u.1), u.2) →
      u.1.failed = none → ∃ o, u.1.here = .lay o)
    (hObj : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (kOfCalls l) u →
      Rch (kOfCalls l) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      (mgAll Dm Mg).pub (.formsInT l 2 "objects") (z, v.1) = true) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (kOfCalls l) u →
      Rch (kOfCalls l) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[kOfCalls l]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[kOfCalls l]?.getD [])
            (Desc.First.rowOf linksFull a)),
        p ∉ paidCallsR l 2 → (mgAll Dm Mg).pub p (z, v.1) = true := by
  intro B' hB z u v hu hr hf hy hsb p hp hnp
  have e : placeAt X l false = some theP := by
    unfold placeAt
    rw [hlook]
    rfl
  obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ :=
    seat_yes claim readers codes shape h hOk hla hpcX e hback B' hB u v hy
  have hM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hmore
  have hfront := onQ_front hu hf
  rw [hM] at hp hfront
  obtain ⟨hsort, hkept⟩ := calls_sorted hl hsub here
  have hpc2 : a.piece = 2 + shift .layers := hpc
  have hIn : Desc.K3.k3OnIn theP u.1 = true :=
    k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l false hlook z u.1 (by
      rw [← hpcX, hpc]
      exact hfront _ (List.mem_append_left _ (by
        rw [← hM]
        exact calls_asks_open (mgAll Dm Mg).more linksFull PS (kOfCalls l) a l .layers hfit here hla
          hsub hpc2 _ (by simp [shift])))))
  have hT : ∀ r ∈ keptCalls l .layers, (mgAll Dm Mg).pub r (z, u.1) = true := fun r hr' =>
    hfront r (hkept r hr')
  have hmH : (l == Dm.pubD.mH) = false := by
    rw [beq_eq_false_iff_ne]
    exact hhd
  have hLay : Desc.First.FillK4.isLay Dm.pubD.links l = true := by
    show (Dm.links[l]? == some ModelPart.layers) = true
    rw [hlinks, hsub]
    rfl
  have hLay' : (Dm.pubD.links[l]? == some ModelPart.layers) = true := hLay
  obtain ⟨o, ho⟩ := hlay z u hr hf
  obtain ⟨o', ho'⟩ : ∃ o', v.1.here = .lay o' := by
    rcases hsb.sort with ⟨_, o', -, h2⟩ | ⟨o1, _, h1, -⟩ | ⟨o1, _, h1, -⟩
    · exact ⟨o', h2⟩
    · rw [ho] at h1
      cases h1
    · rw [ho] at h1
      cases h1
  -- the ledger in front: sized, the place's number of slots, free from its next slot on
  obtain ⟨F, hF, hz, -, -⟩ := k3OnIn_free hsP hIn
  have hQ : LeftQ (theP).ns F := by
    have f0 : (mgAll Dm Mg).pub (.freeAbove l) (z, u.1) = true :=
      hfront _ (List.mem_append_left _ (by
        rw [← hM]
        exact calls_asks_open (mgAll Dm Mg).more linksFull PS (kOfCalls l) a l .layers hfit here hla
          hsub hpc2 _ (by simp)))
    have f1 : ((Dm.pubD.nsOf l).any fun n => Desc.First.freeAboveB n u.1) = true := f0
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
      exact sentIs_kept claim piece laid before theP guests u.1 v.1 rs cols hd _ _ ht
    · rw [pubAll_more_treesAre] at ht ⊢
      exact treesAre_kept claim piece laid before theP guests u.1 v.1 rs cols hsP hd hIn _ _ ht
    · exact three_stay Dm.pubD Mg.pub z hsb _ (by simp) ht
    · exact three_stay Dm.pubD Mg.pub z hsb _ (by simp) ht
  · simp only [newCalls, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl | rfl | rfl | rfl
    · rw [mgAll_pub, pubAll_look_lay Dm.pubD Mg.pub l hmH hLay]
      exact look_lay_made claim piece laid before theP guests u.1 v.1 rs cols hsP hd hIn ho
    · rw [mgAll_pub, pubAll_callerIn_lay Dm.pubD Mg.pub l hLay]
      have e5 : Dm.pubD.nextOf l = some ((theP).first + Forest.elems x.fs) :=
        nextOf_is hlook hsP
      rw [e5, Option.any_some]
      exact callerIn_lay_made claim piece laid before theP guests u.1 v.1 rs cols hsP hd hIn ho
        (hown z u hr hf o ho) rfl
    · rw [mgAll_pub, pubAll_more_rowsBare Dm.pubD Mg.pub l hLay']
      exact rowsBare_lay_made claim piece laid before theP guests u.1 v.1 rs cols hsP hd hF hQ ho'
    · rw [mgAll_pub, pubAll_more_lookLeft Dm.pubD Mg.pub l hLay']
      exact lookLeft_lay_made claim piece laid before theP guests u.1 v.1 rs cols hsP hd hF hQ ho'
    · exact hObj B' hB z u v hu hr hf hy hsb

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.onQ_front
#print axioms VerifiableInference.OnPublicFiles.othersPub_att_mgAll
#print axioms VerifiableInference.OnPublicFiles.othersPub_lay_mgAll
