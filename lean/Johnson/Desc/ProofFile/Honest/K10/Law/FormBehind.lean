-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Law/FormBehind.lean: CONDITIONAL: THE THREAD's FORM BEHIND THE
STEP OF THE MEMBER THAT CLOSES A SEGMENT's FRAME (kind K10), at the first chain's thread at the
library's head (lettersHead, Honest/Thread/FirstHead.lean), AT EACH OF THE 25 SEGMENTS. Statements
with their proofs. It joins theorems of the library: it shows nothing new on the closing.

  k10_place_head    the place number 14 l + IM.nAt l + 5 of the written list of places is of the
                    kind K10, at each l below 25
  k10_out_of_groups CONDITIONAL: at a state that the thread holds in front of such a member the
                    index masks' message is a member of no group
  k10_form_behind   CONDITIONAL: **from the thread in front and the member's step: the form one
                    border on, at where the prover's run then stands**

The one premise of k10_form_behind beside its own two (the thread in front; the member's step): h:
the library's head (P5J.AtMgA, Johnson/P5J/MgAtAll.lean). General in all letters of lettersHead.

THE ROAD. The form at a border is "no mark" and the table's promise at the honest letters and no
strings. The promise behind K10's writing follows from the promise in front by k10_promise_at
(Johnson/Desc/First/Close/Law/PromiseAt.lean), which is general in the meaning. What it asks, and
who has it: the member is a segment's closing, seated alone: P5J.k10_block_at
(Johnson/P5J/K10Seat.lean) · its yes is the frame's closing's, and leaves no mark:
LPFK10.seated_yes (Johnson/LPFK10R/Sits.lean) · the two tests on the table: P5J.fit_full, next_full
(Johnson/P5J/K10Kind.lean) · what is kept lies in its group: P5J.k10_kept_at
(Johnson/LPFE1R/K10KeptAt.lean) · the plan's two counts stay: P5J.k10_counts_at
(Johnson/P5J/K10Seat.lean) · of the six
sentences on the meaning four ("in order", the public items' test, what they say beside it, "held")
are the composed meaning's own, which the honest letters do not turn: P5J.k10_asks_at
(Johnson/P5J/K10Asks.lean), under a fence on the state in front; the other two ("decodes"; "shown"
and "no collision") are true by the honest letters' text · the fence: P1L20.room_out_of_groups
(Johnson/P1L20R/RoomFold.lean) with P5J.k10_room_at (Johnson/P5J/K10Two.lean), at a reached state:
the thread's clause on how the state was made gives "reached" (reach_of_made,
Honest/Thread/MadeLaw.lean). SMALLER CALLS: which place stands at the number: LPFK10.k10_place_w
(Johnson/LPFK10R/CloseShare.lean), pw_is (Johnson/LPFK10R/HandsK10W.lean), P5J.placesW_at
(Johnson/P5J/FoldJ3.lean) · the number lies from 3 to 355: P5J.k10_in_room
(Johnson/P5J/K10Fence.lean) · from the step's yes to K10's writing, and that it turns no mark:
k10_step_of_yes, k10_step_mark (Johnson/Desc/First/Close/Law/HandsOfK10.lean) · the fence's two
forms: P1L20.outOfGroupsB_iff · every member's test on the plan: planOk_parts
(Johnson/Desc/Sound/PieceLaid.lean) · the input behind the step is the input in front: play_mid
(Honest/Law/Along.lean).

Limits. Conditional. h is a hypothesis of every statement that names it. It can be met: at the
goals' two named sets of full-size public files, as Lean's written copies spell them, the head has a
member with no premise (at the first set the library's AtFullSide.Top.headMember_zFull; at the
second headMember_zGap; at either, under "Z is one of the two", headMember_named).
This file does not call these. At other public files in scope
the library's P5J.head_exists_at_name gives a member under premises on the files, of which the
fourth follows from the third (P5J.owed_of_live).
NOTHING SHOWS THAT THE THREAD HOLDS AT ANY RUN OR THAT THE MEMBER's STEP SAYS YES ANYWHERE: where
either is not met the statement says nothing. It speaks of the form alone: not of what rides, of
what the step keeps, or of the items that the row owes. RIGHT BENEATH WHAT IS CALLED LIE TEN CLOSED
FACTS THAT ARE DECIDED BY EVALUATION at the library's written lists: sorts_are_full
(Johnson/P5J/K10Kind.lean), closersFit_real (Johnson/Desc/First/Close/Law/PromiseBehind.lean) and
closersNext_real (ShapeBehind.lean, beside it), under the two tests on the table · pubFitK_full and
saidFitK_full (Johnson/P5J/K10Asks.lean) · k10_in_room_all (Johnson/P5J/K10Fence.lean) ·
k10_places_w (Johnson/LPFK10R/CloseShare.lean) · lw_is (Johnson/LPFK10R/HandsK10W.lean) · kept_full
(Johnson/Desc/First/Link/Law/KeptInGroup.lean) · linksW_at (Johnson/P5J/FoldJ3.lean). Lean's kernel
has checked all ten; at the first nine it alone did the evaluating. What lies deeper was not walked.
At the library's full size and the format's second hash function alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.LPFK10R.HandsK10W
import Johnson.P5J.K10Asks
import Johnson.P5J.K10Seat
import Johnson.P5J.K10Two
import Johnson.P5J.FoldJ3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Strs Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (onAt openSets pubSets start k10_promise_at)
open VerifiableInference.Desc.First.Close (OutF K10Step)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread (Script WtF lettersHead honest noStrs)
open P5J (AtMgA CellsM TS mgAtAll fullLinks)

/-- **The place number 14 l + IM.nAt l + 5 of the written list is of the kind K10.** CONDITIONAL: l
is below 25. -/
theorem k10_place_head {l : Nat} (hl : l < 25) :
    ∃ p, P5J.At.ps[14 * l + IM.nAt l + 5]? = some p ∧ p.kind = KindName.K10 := by
  obtain ⟨p, hp, hK⟩ := LPFK10.k10_place_w hl
  rw [LPFK10.pw_is, P5J.placesW_at] at hp
  exact ⟨p, hp, hK⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **At a state that the thread holds in front of a member of the kind K10 the index masks' message
is a member of no group.** CONDITIONAL: under the hypothesis h; the place number b is of the kind
K10; the thread at the border number b. -/
theorem k10_out_of_groups {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hK : p.kind = KindName.K10) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    OutF s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨free0, R⟩ := P5J.k10_room_at h
  obtain ⟨h3, h355⟩ := P5J.k10_in_room b p hp hK
  obtain ⟨B, -, -, hB, -⟩ := P5J.k10_block_at h b p hp hK
  have hpl : ∀ c ∈ cF.blocksInOrder, c.planOk = true := fun c hc =>
    (Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1
      (VerifiableInference.Desc.Sound.planOk_parts (P5J.F0T OnBytes.secondHashFunction Zp Np cF)
        h.laid.planOk).1 c hc)).1
  have hr := reach_of_made (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (ProofFile.startS Zp) m.st.input.x.pub
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hB).1) (fun _ e => e) hT.2.2.2.2.1
  exact P1L20.outOfGroupsB_iff.1 (P1L20.room_out_of_groups h.scope h.reads O hpl R hr h3 h355)

/-- **THE FORM BEHIND THE STEP OF THE MEMBER OF KIND K10, AT EACH OF THE 25 SEGMENTS.** CONDITIONAL:
under the hypothesis h; l is below 25; blk is the member number 14 l + IM.nAt l + 5 of the first
chain's flat list; the thread in front; the member's step. -/
theorem k10_form_behind {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (14 * l + IM.nAt l + 5) k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * l + IM.nAt l + 5 + 1) k s' y.2 := by
  intro blk hblk k s m E ds y cols s' hT hS
  obtain ⟨p, hp, hK⟩ := k10_place_head hl
  -- the member is a segment's closing, seated alone
  obtain ⟨B, Q9, a, hB, -, hak, -, hla⟩ := P5J.k10_block_at h _ p hp hK
  obtain rfl : B = blk := Option.some.inj (hB.symm.trans hblk)
  -- its step's yes is the frame's closing's
  have hs : K10Step s s' :=
    VerifiableInference.Desc.First.Close.k10_step_of_yes Q9 B
      (fun t rs gs t' hy => (LPFK10.seated_yes hla (by rw [hak]; decide) t t' rs gs hy).1) s s'
      ⟨_, _, _, _, hS.2⟩
  obtain ⟨es, rs, c, hc, rfl⟩ := hs
  have hs : K10Step s (VerifiableInference.Desc.K9.putRec s ⟨none, c.1, c.2⟩) :=
    ⟨es, rs, c, hc, rfl⟩
  -- in front: no mark, the promise, the fence
  obtain ⟨hf0, hon0⟩ := hT.2.2.1
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hf0
  have hF := k10_out_of_groups h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp hK hT
  have A := P5J.k10_asks_at h (F := ⟨0, [], fun _ => 0, 0⟩) h.toAtMg.fence _
    ((P5J.At.N Zp cF).treesAt P5J.At.ps[14 * l + IM.nAt l + 5]?) p hp hK (Nat.le_refl _)
  have hC := P5J.k10_counts_at h _ p hp hK
  -- the input is as it was
  obtain ⟨⟨st, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨?_, ?_⟩
  · show (VerifiableInference.Desc.K9.putRec s ⟨none, c.1, c.2⟩).failed.isNone = true
    rw [VerifiableInference.Desc.First.Close.k10_step_mark hs, h0]
    rfl
  · show onAt (P5J.At.N Zp cF)
      (honest (mgAtAll h) (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
        (P5J.At.ms Zp Z.lay)) test) fullLinks P5J.At.ps[14 * l + IM.nAt l + 5 + 1]?
      (((openSets fullLinks P5J.At.ps (start fullLinks))[14 * l + IM.nAt l + 5 + 1]?).getD [])
      (((pubSets (mgAtAll h).more fullLinks P5J.At.ps)[14 * l + IM.nAt l + 5 + 1]?).getD [])
      (y.2.st.input.x.pub, VerifiableInference.Desc.K9.putRec s ⟨none, c.1, c.2⟩) noStrs
    rw [ei]
    exact k10_promise_at (P5J.At.N Zp cF) _ fullLinks P5J.At.ps _ p P5J.fit_full P5J.next_full hp
      hK (P5J.k10_kept_at h.toAtMg _ p hp hK) hC.1 hC.2 _ _ (m.st.input.x.pub, s)
      m.st.input.x.pub noStrs noStrs es rs c hc hon0 (fun _ => trivial)
      (fun e => A.inOrder _ _ _ hF hs e) (fun e => A.pub _ _ _ hF hs e)
      (fun e => A.pubP _ _ _ hF hs e) (fun e => A.held _ _ _ hF hs e)
      (fun _ _ _ _ => ⟨trivial, trivial⟩)

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.k10_place_head
#print axioms ProofFile.Honest.K10.k10_out_of_groups
#print axioms ProofFile.Honest.K10.k10_form_behind
