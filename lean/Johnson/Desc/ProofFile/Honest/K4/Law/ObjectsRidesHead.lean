-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ObjectsRidesHead.lean: CONDITIONAL.

What is here. THE ITEM `Item.formsT m 2 "objects"` RIDES FORWARD PAST THE MEMBER OF THE LAYERS' OWN
ROUNDS (kind K4): the threads' debt `RidesPastAtS` (Honest/Thread/SharesS.lean) at that item, at the
first chain's thread at the library's own parameters (`lettersHead`), at K4's own member. What the
item says in front of the member, at any one witness (the thread spends it at the prover's own), it
says behind, at every state behind that the member's clause of keeps allows. `k4_objects_on_all`
(Law/ObjectsOnAll.lean) has the item's sentence forward over a step with `K4Keeps`, where the
promise's public test accepts in front. Here its hypotheses are met at the thread: the clause from
hK; the public test from the thread's own form (`thr_tests`, `ePubAt_of_held`, Law/FrontHead.lean);
the link, its two runs and the head's link from h (`nine_head`, Law/ElevenHead.lean); that the
data's list of segments is the written one from the library's `k4Fill_all`
(Johnson/Road/K4/K4FillAll.lean). The thread's sentence at the item is the library's by unfolding
(`mgAll_formsT`, Johnson/Desc/Sound/MgAll.lean). Words: as in Law/ElevenHead.lean.

  `k4_ridesPastAtS_objects_at`   **from A (the member's number, segment and place stand in the
      written lists) and hK.**
  `k4_ridesPastAtS_objects_head`   the same from hp, hm, hs and hK: the place written out.

Limits. CONDITIONAL: on h; on A, or on hp · hm · hs, which are public facts on the written lists
(the library's `atK4_full` has A at each g < 12); and on hK: the thread's parameter Kp at the
member's place gives `K4KeepsM` (Law/KeepsStep.lean). A Kp that never holds meets it emptily: of h
together with hK at a Kp that holds of a step of a run no example is known to us. THE STATEMENTS
SPEAK ONLY WHERE THE THREAD STANDS IN FRONT OF THE MEMBER, keeps holds and the item's sentence holds
in front: where the thread stands nowhere they hold emptily. THAT THE THREAD STANDS AT ANY RUN IS
NOT SHOWN; of h together with the thread in front, keeps and the item's sentence no example is known
to us. NO HYPOTHESIS OF ITS OWN ON THE ROWS' ENTRIES: that the rows which the lookup heard name no
entry is still asked, inside the promise's public test in front (the public name "K4.rowsBare"),
which the thread's form holds; the lookup's accept makes it (the library's `rowsBareB_made`: shown
where the lookup's own decision accepts, not for the lookup as it is seated in the chain). THAT A
FORM IS WORTH 0 ANYWHERE is not said. Of the item's second run, "guests", only this is used: at a
layers' segment it has no forms. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h
holds of any files is not shown here: the side library AtFullSide proves, with no hypothesis, that h
has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth). Beneath `k4_objects_on_all` and `nine_head` stand
comparisons by Lean's own kernel that no independent checker has replayed. IT IS A LAW, NOT A PART:
it rests on modules under Johnson/Goal/: no file that defines a part may build on it; it states no
goal. Nothing on soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ObjectsOnAll
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Road.K4 (AtK4 k4Fill_all)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT linksFull mgAll_more_base)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (laid_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, A and hK. **`RidesPastAtS` AT THE ITEM, AT K4's OWN MEMBER.** -/
theorem k4_ridesPastAtS_objects_at
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) (b m : Nat) {p : Place}
    (A : AtK4 linksFull PS b m p) (hK : ∀ s s', Kp p s s' → K4KeepsM s s') :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
      Said b (Item.formsT m 2 "objects") := by
  obtain ⟨g, x, blk, Lh⟩ := laid_head h A
  obtain ⟨hH, -, -, ⟨l, runO, runG, hlk, -, fO, oRun, fG, gRun⟩, -⟩ := nine_head h Lh
  intro c s mm E s' ps v hT hk h0
  have K : K4Keeps s s' := (hK s s' (hk p A.here)).1
  obtain ⟨-, t2, -⟩ := thr_tests h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT.1
  have hE := ePubAt_of_held (Dm := h.𝔇)
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
    (mgAll_more_base h.𝔇) t2
  have h1 := (h0 : _ ∧ _).1
  refine And.intro ?_ fun e => absurd e (by decide)
  exact k4_objects_on_all (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) hH A
    (k4Fill_all h VerifiableInference.Desc.K13.Law.LFull).links hlk fO oRun fG gRun K hE h1

/-- CONDITIONAL: on h, hp, hm, hs and hK. **THE SAME WITH THE PLACE WRITTEN OUT.** -/
theorem k4_ridesPastAtS_objects_head
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) (b m : Nat) {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hm : p = { chain := 1, link := some m, piece := 3, kind := .K4 })
    (hs : linksFull[m]? = some .layers) (hK : ∀ s s', Kp p s s' → K4KeepsM s s') :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
      Said b (Item.formsT m 2 "objects") :=
  k4_ridesPastAtS_objects_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said b m
    ⟨hp, by rw [hm], hs, by rw [hm]⟩ hK

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_ridesPastAtS_objects_at
#print axioms ProofFile.Honest.K4.k4_ridesPastAtS_objects_head
