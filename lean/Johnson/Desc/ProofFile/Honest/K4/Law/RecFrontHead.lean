-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/RecFrontHead.lean: CONDITIONAL. Statements with their proofs.

What is here: wherever the first chain's thread stands in front of the member of the feed-forward
layers' own rounds (sub-protocol K4), at the library's own values (`lettersHead`,
Honest/Thread/FirstHead.lean), THE OPEN SEGMENT's PART OF THE VERIFIER's STATE READS AS THE PLAN
SAYS: the library's `RecIs` (Johnson/Road/K4/Rec/Whole.lean), under h, the hypothesis on the public
files (`P5J.AtMgA`), `LaidK4` (Law/SeatedHead.lean) and the thread alone: no step of the member is
asked. Among its fields: the number of the message that holds the segment's mask row is the plan's
term (`maskP`); the book seats each message where the plan's list does (`seatP`); a message's row
bits are the plan's (`rowBitsP`). AND SO: there are a message number o and a seat x, among the seats
of the segment's first sending, with: the frame's mask row's message is o, and the book seats o at
x.
How. `ownFront_at_all` (Law/FrontHead.lean) has the library's `More.OwnFront` there; the library's
`recIs_at_state` (Johnson/Road/K4/More/RecAtState.lean) makes `RecIs` of nine of its lines. The
seat: `RecIs.maskSeat` and the field maskP of the library's `K4RowPlan`
(Johnson/Road/K4/K4RowOfMeans.lean), had by `k4RowPlan_wide`.

Not shown here. THAT THE THREAD HOLDS AT ANY RUN: hT is a hypothesis. That h can hold: the side
library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with hT no example is known to us (`LaidK4`: h gives it at each group:
`laid_at`, Law/LaidAtGroup.lean). WHAT THE PLAN's TERMS ARE WORTH: which number o is, which seat x
is, that the mask table has no row bits: the library's `MaskPlan` (Johnson/Road/K4/Rec/Pins.lean)
says that of the plan; it is not called here: Law/W/MaskSixHead.lean calls it. THE FULL SIZE's
WRITTEN LISTS ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). WHAT THIS FILE's
IMPORTS REACH, by a program's walk from import to import that stops, unopened, at every module under
Johnson/Goal/, Johnson/D/ or ThirdParty/ and at the names RecCompile.Honest…, RecCompile.Both… and
RecCompile.PassH…: it stopped at 70 modules under Johnson/Goal/ and at 2 under ThirdParty/; it saw
46 modules whose names hold RecCompile, none under Johnson/D/ and none of the three names. What lies
behind the 72 is not counted: all five numbers are floors. They come with h and with
Law/ElevenHead.lean. A LAW, NOT A PART: no file that defines a part of the proof file's description
may import this one. Nothing on soundness, on completeness or on any other property.
No property is claimed.

  `recIs_front_all`   `RecIs` at a state in front, at the composed meaning's own public tests
  `recIs_front_head`   **`RecIs` where the thread stands**
  `maskSeat_front_head`   **the mask row's message and its seat are there**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (AtK4 K4OnX K4OnD K4NamedW CellsK parOf k4DataWide k4RowPlan_wide)
open OnBytes.Road.K4.Rec (RecIs recPlanOf recIs_at_state)
open OnBytes.Road.K4.More (PS K4Fence)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Wit)
open VerifiableInference.Desc.First (S pubAll ePubAt bookAt)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.K9 (segAt? seatAt)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT MgData WideData mgBase linksFull moreAll mgAll_more_base)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-! ## 1 At the composed meaning's own public tests -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Dm : MgData Xi P Tok rows cols nR X} {E : WideData P}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

variable {k m : ℕ} {pl : Place} {par : Par}
  {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
  {layout : Option ByteArray} {n : ℕ}

/-- CONDITIONAL on every hypothesis named. **At a state in front of the member the open segment's
part reads as the plan says.** -/
theorem recIs_front_all (hH : isLay Dm.links (headLink X) = false) (H : AtK4 linksFull PS k m pl)
    (Sx : K4OnX X pol KL layout m par) (Sd : K4OnD Dm m par n) (Sn : K4NamedW Dm E k m par told n)
    {z : P} {s : S} (hE : ePubAt (pubAll Dm.pubD (Bm).pub) moreAll linksFull PS k (z, s) = true)
    (hb : bookAt Dm.N PS[k]? s = true) (Fc : K4Fence Dm E m s) :
    ∀ a, segAt? s = some a →
      RecIs a (recPlanOf (k4DataWide Dm E Bm) (k4DataWide Dm E Bm).sd)
        ((k4DataWide Dm E Bm).N.msgsAt PS[k]?) m := by
  intro a ha
  have OF := ownFront_at_all hH H Sx Sd Sn hE hb Fc
  exact recIs_at_state ha OF.live OF.fresh OF.seats OF.shapes OF.sent OF.trees OF.codes OF.places
    OF.msgs

end

/-! ## 2 At the thread with the library's own values -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh and hT. **`RecIs` WHERE THE THREAD STANDS IN FRONT OF THE MEMBER.** -/
theorem recIs_front_head
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    ∀ a, segAt? s = some a →
      RecIs a
        (recPlanOf (k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase)
          (k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase).sd)
        ((k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase).N.msgsAt
          PS[k]?) m := by
  have A := atK4_of_laid Lh
  obtain ⟨hH, Sx, Sd, _, hbd⟩ := nine_head h Lh
  have Sn := named_head h Lh
  obtain ⟨_, t2, t3⟩ := thr_tests h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  have heard := k4_heard_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) hH A Sx Sd c s mm E hT
  have Fc := k4Fence_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A.here A.link
    (by rw [A.piece]; exact Nat.le_succ 2) (by omega) hT heard
  exact recIs_front_all hH A Sx Sd Sn
    (ePubAt_of_held (Dm := h.𝔇)
      (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
      (mgAll_more_base h.𝔇) t2) t3 Fc

/-- CONDITIONAL: on h, Lh and hT. **THE MASK ROW's MESSAGE AND ITS SEAT ARE THERE**, among the seats
of the segment's first sending. -/
theorem maskSeat_front_head
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    ∀ a, segAt? s = some a → ∃ (o : ℕ) (y : ℕ × ℕ), maskOracle a.L.check.frame = some o ∧
      seatAt (h.𝔇.N.sent m 0) a.d.book o = some y := by
  intro a ha
  have R := recIs_front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT a ha
  have A := atK4_of_laid Lh
  obtain ⟨hH, Sx, Sd, _, _⟩ := nine_head h Lh
  have Pl := k4RowPlan_wide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) A Sx Sd
    (named_head h Lh)
  have e := OnBytes.Road.K4.Rec.mask_plan R _ Pl.maskP
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 e
  obtain ⟨o, ho, hs⟩ := Option.bind_eq_some_iff.1 hy
  exact ⟨o, y, ho, hs⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.recIs_front_all
#print axioms ProofFile.Honest.K4.recIs_front_head
#print axioms ProofFile.Honest.K4.maskSeat_front_head
