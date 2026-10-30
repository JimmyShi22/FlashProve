-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K7/Law/FormBehind.lean: CONDITIONAL: THE THREAD's FORM BEHIND THE STEP
OF THE MEMBER NUMBER 338, THE NEXT TOKEN's (kind K7), at the first chain's thread at the library's
head (lettersHead, Honest/Thread/FirstHead.lean). One statement with its proof. It joins theorems of
the library: it shows nothing new on the next token.

  k7_form_behind   CONDITIONAL: **from the thread in front and the member's step: the form one
                   border on, at where the prover's run then stands**

The one premise beside its own two (the thread in front; the member's step): h: the library's head
(P5J.AtMgA, Johnson/P5J/MgAtAll.lean). General in all letters of lettersHead.

THE ROAD. The form at a border is "no mark" and the table's promise at the honest letters and no
strings. THE PROMISE BEHIND IS THE LIBRARY's k7_rides (Johnson/Desc/Kinds/Law/K7Rides.lean), CALLED:
it is general in the meaning and speaks of the two states by facts. It is typed at a frame's
strings: it is called at a made-up frame and made-up strings: the honest letters read no string, so
the promise at these and at no strings is one by unfolding. What it asks, and who has it: the member
is the seated constant (the entry of the head's link, then the next token's block): P4.k7_left_seat
(Johnson/P4R/ReplyTiedN.lean) · from the step's yes to the decision's: step_decide
(Johnson/Desc/First/Close/Law/HandsOfK10.lean) · what the state behind is: place_facts
(K7Rides.lean) and place_whole (Johnson/Desc/Kinds/Law/ReplyRest.lean: the mark stays) · the two
places: place338, place339 · no class of rows is open there, so the premise on the fresh group's
number is idle: noRows338 (all three: Johnson/Desc/Kinds/Law/K7AtMgAll.lean) · the table's test on
the book, at the thread's own letters, with no premise: P5J.k03_book_at (Johnson/P5J/K03BookAt.lean)
· the member tells no tree: P4.told_338 (Johnson/P4R/Told338N.lean) · of the six sentences on the
meaning four are the composed meaning's own, which the honest letters do not turn: "in order" reads
the public part alone (mgAll_inOrder_at, Johnson/Desc/Sound/MgAll.lean) · the public items' test:
H2K7.k7_pub_at (Johnson/Desc/Kinds/Honest/Law/K7PubAt.lean) · what they say beside it: pubP_mgAll ·
"held" reads no group: smpHeld_withFresh (both: K7AtMgAll.lean); the other two ("decodes"; "shown"
and "no collision") are true by the honest letters' text · the input behind the step is the input in
front: play_mid (Honest/Law/Along.lean).

Limits. Conditional. h is a hypothesis. It can be met: at the library's written copy of the
full-size public files the head has a member with no premise (AtFullSide.Top.headMember_zFull): this
file does not call it; that copy is tied to the package's files by no theorem. NOTHING SHOWS THAT
THE THREAD HOLDS AT ANY RUN OR THAT THE MEMBER's STEP SAYS YES ANYWHERE: where either is not met the
statement says nothing. It speaks of the form alone: not of what rides, of what the step keeps, or
of the items that the row owes. RIGHT BENEATH WHAT IS CALLED LIE CLOSED FACTS THAT LEAN's KERNEL HAS
DECIDED BY EVALUATION at the library's written lists: place338 · place339 · open338 (under
noRows338) · pubFront338 · pubStep338 · pubTied339 (under k7_pub_at and pubP_mgAll); "the link
number 24 is a head's" is decided in this file. What lies deeper was not walked. Through its imports
the file stands above the library's folder ThirdParty/. At the library's full size and the format's
second hash function alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.Kinds.Honest.Law.K7PubAt
import Johnson.Desc.Kinds.Law.K7Rides
import Johnson.Desc.Kinds.Law.K7CondOfLaid
import Johnson.Desc.First.Close.Law.HandsOfK10
import Johnson.P5J.K03BookAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K7
open VerifiableInference.Desc (Chain Strs Place KindName)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase mgAll_more_base mgAll_inOrder_at linksFull)
open VerifiableInference.Desc.First (onAt openSets pubSets start flatPlacesOf rowSegs)
open VerifiableInference.Desc.Kinds.Head.Law
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread (Script WtF lettersHead honest noStrs)
open P5J (AtMgA CellsM TS mgAtAll fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE FORM BEHIND THE STEP OF THE MEMBER NUMBER 338, THE NEXT TOKEN's.** CONDITIONAL: under the
hypothesis h; blk is the member number 338 of the first chain's flat list; the thread in front; the
member's step. -/
theorem k7_form_behind :
    ∀ blk, cF.blocksInOrder[338]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 338 k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (338 + 1) k s' y.2 := by
  intro blk hblk k s m E ds y cols s' hT hS
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, e1, e2, -, -, hyes, hfront⟩ := P4.k7_left_seat h.scope h.reads O
  have f1 : cF.blocksInOrder[338]? = some b := by
    have q' := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope h.scope h.reads O (by decide) 0] at q'
  obtain rfl : b = blk := Option.some.inj (f1.symm.trans hblk)
  obtain ⟨rs0, gs0, hd0⟩ :=
    VerifiableInference.Desc.First.Close.step_decide b _ s s' _ _ _ hS.2
  obtain ⟨rs, gs, hy⟩ := hyes _ _ _ _ hd0
  obtain ⟨h0, hst, hbk, hsh⟩ := place_facts Bs.G₀.W 24 "H:1" (P4.k7Front Bs.G₀.W) Bs.G₀.W.H.tl
    hfront _ _ _ _ hy
  have hw := place_whole Bs.G₀.W 24 "H:1" (P4.k7Front Bs.G₀.W) Bs.G₀.W.H.tl hfront _ _ _ _ hy
  obtain ⟨-, hon0⟩ := hT.2.2.1
  obtain ⟨⟨st, -, hyp⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hyp
  refine ⟨?_, ?_⟩
  · show s'.failed.isNone = true
    rw [hw.2.2.2.2.1, h0]
    rfl
  · show onAt (P5J.At.N Zp cF)
      (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test) fullLinks P5J.At.ps[338 + 1]?
      (((openSets fullLinks P5J.At.ps (start fullLinks))[338 + 1]?).getD [])
      (((pubSets (mgAtAll h).more fullLinks P5J.At.ps)[338 + 1]?).getD [])
      (y.2.st.input.x.pub, s') noStrs
    rw [ei]
    refine k7_rides (Fr := ⟨0, [], fun _ => 0, 0⟩) (P5J.At.N Zp cF)
      (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test) fullLinks P5J.At.ps
      (fun a => a) 338 24 .K7 .K2 (by decide) place338 place339
      ((m.st.input.x.pub, s), (fun _ => (0, []), fun _ => []))
      ((m.st.input.x.pub, s'), (fun _ => (0, []), fun _ => [])) hon0 _ _ h0 hst
      hbk hsh ?_ (P5J.At.told cF) (P5J.k03_book_at Zp cF) ?_ (fun _ => trivial) ?_ ?_ ?_ ?_
      (fun _ _ _ _ _ => ⟨trivial, trivial⟩)
    · intro v hv
      have hv' : v ∈ rowSegs (VerifiableInference.Desc.Sound.openQ linksFull
        (flatPlacesOf linksFull true) 338) := hv
      rw [noRows338] at hv'
      cases hv'
    · exact P4.told_338 h.scope h.reads O
    · intro _ _ e
      have e' : (mgAll h.𝔇 mgBase).inOrder (m.st.input.x.pub, s) = true := e
      show (mgAll h.𝔇 mgBase).inOrder (m.st.input.x.pub, s') = true
      rw [mgAll_inOrder_at] at e' ⊢
      simp only [Bool.and_eq_true] at e' ⊢
      exact ⟨rfl, e'.2⟩
    · intro _ _ e
      exact H2K7.k7_pub_at h.𝔇 mgBase (mgAll_more_base h.𝔇) Bs.G₀.W (by rw [O.W]; rfl) 24 "H:1"
        (P4.k7Front Bs.G₀.W) Bs.G₀.W.H.tl hfront m.st.input.x.pub hy e
    · intro _ _ _
      exact pubP_mgAll h.𝔇 mgBase (mgAll_more_base h.𝔇) (fun _ => rfl) (m.st.input.x.pub, s')
    · intro _ _ v _ e
      show VerifiableInference.Desc.smpHeld s'.st s'.book v.1 v.2 = true
      rw [hst, hbk, smpHeld_withFresh]
      exact e

end ProofFile.Honest.K7

#print axioms ProofFile.Honest.K7.k7_form_behind
