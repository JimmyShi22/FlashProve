-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskSixHead.lean: CONDITIONAL. One definition, statements
with their proofs.

What is here. ON THE MASK ROW OF THE SEGMENT OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol
K4): ONE MESSAGE NUMBER o AND ONE MEMBER u OF THE WITNESS's LIST OF MEMBERS (`h.𝔇.ms`), HAD FROM THE
PUBLIC SIDE ALONE, BEFORE ANY PROVER, SCRIPT, COIN OR STATE IS NAMED; and three facts on the
verifier's state at that o and u, wherever the frame's thread with the library's own values
(`lettersHead`) stands in front of the member. `MaskRowPub`: what the plan says of o and u: u's seat
and u's shape are written ones: those that the plan gives the first message with mask rows, behind
the kept ones; u is the member of the list that is found at its seat (`memAt`); u's shape has a mask
row; the lookup's place at the segment has no more entries of the mask row (its field ns) than the
mask code's length; and the three lines of the library's `MaskPlan` (Johnson/Road/K4/Rec/Pins.lean)
at o and u's seat. `maskRowPub_head`: UNDER h, `LaidK4` AND hx THERE ARE SUCH o AND u.
`maskRowPub_one`: AT ONE SEGMENT AT MOST ONE PAIR: each is a function's value. `maskRow_of_recIs`,
`maskRow_front_head`: at every such o and u, at the open segment's part a of the state: (i) the
frame's mask row's message is o; (ii) the book seats o, among the seats of the segment's first
sending, at u's seat; (v) the mask table of o has no row bits. `maskAt_front_head`: these three are
the library's `MaskAt` (Johnson/Top/H0/MergeLaw/MaskRow.lean) at the member u and 0 row bits. The
numbers (i) to (vi) are those of six facts by which a reader of the mask row is tied to the witness:
(i), (ii), (v) as above; (iii) u is the first member of the list at that seat, as `List.find?`
returns it: `maskRow_find`; (iv) the member's number in the witness is `numOf h.𝔇.arr u`, by that
function's definition: no clause; (vi) the pad's test `padB` says no below the row's last place: a
lemma on `padB` alone, not typed here.
How. A yes of the library's test `maskPlanB` gives `MaskPlan` (a field of `K4PinsTests`:
`pinsTests_head`, Law/W/ReadersHead.lean). The library's `SitsIn` (Johnson/Road/K4/K4PinsRead.lean),
had by `sitsIn_head` (Law/W/ReadersHead.lean), finds a member of the list, of that message's shape,
at the seat. `RecIs`, which `recIs_front_head` (Law/RecFrontHead.lean) has where the thread stands,
carries the plan's three lines to the state.

Not shown here. THAT THE THREAD HOLDS AT ANY RUN: hT is a hypothesis. WHERE NO SEGMENT IS OPEN the
statements on the state say nothing; that one is open where the thread stands is not shown here.
That h can hold: the side library AtFullSide proves, with no hypothesis, that h has a member at one
place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say
what it is worth). BESIDE h: `LaidK4`, which h gives at each group (`laid_at`,
Law/LaidAtGroup.lean), and hx in `maskRowPub_head`; the other statements take P (`MaskRowPub`:
`maskRowPub_head` has it); `maskRow_of_recIs` hR besides; the two on a state `LaidK4` and hT, and
`maskAt_front_head` ha (a segment is open: `seg_open_head`, Law/W/MaskBelowHead.lean, has one under
hT): of h together with `LaidK4`, P, ha and hT no example is known to us. hx names the lookup's
place at the segment; it is there under h and `LaidK4` (Law/W/LayAtHead.lean). THE FIELD room IS TWO
STEPS FROM A FENCE AGAINST THE PAD: it lets an entry be the row's last place, which is the pad's
place by the library's test `padB` (Johnson/Desc/SeatAt.lean: at one answer); and that the entries
which the member's rounds spend lie below xl.ns is not shown here. Law/W/MaskEllHead.lean has the
first step (xl.ns and one more are within the length), Law/W/MaskBelowHead.lean the second, of the
entries that the tie `K4MaskTieAt` asks, where the thread stands. The library has a sharper line for
a built segment, in other letters: its number of entries and the shape's number of answers together
are within the mask code's length (`built_ns_le`, Johnson/Road/K4/Rec/BuiltTests.lean); it is not
called here. That u's shape has ONE mask row: the field rows says at least one. THAT THE NUMBERS
`numOf h.𝔇.arr u` OF TWO SEGMENTS DIFFER is not shown. Nothing is said on what the witness holds at
any place. u's seat, number and shape as terms that name no u: Law/W/MaskRowWritten.lean. THE FULL
SIZE ALONE, and the format's second hash function alone. IT RESTS, through `sitsIn_head` and
`pinsTests_head`, ON STATEMENTS OF FILES UNDER Johnson/Goal/: Law/W/ReadersHead.lean's head names
them. A program's walk from import to import, which reads import lines alone and stops unopened at
Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under
Johnson/Goal/: a floor. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one. Nothing on soundness, on completeness or on any other property.
No property is claimed.

  `MaskRowPub`   what the plan says of o and u
  `maskRowPub_head`   **there are such o and u, from the public side alone**
  `maskRowPub_one`   at one segment at most one pair
  `maskRow_find`   (iii), as `List.find?` returns it
  `maskRow_of_recIs`   the three facts on a state's part that reads as the plan says
  `maskRow_front_head`   **the three facts where the thread stands, at every such o and u**
  `maskAt_front_head`   the three as the library's `MaskAt`
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ReadersHead
import Johnson.Road.K4.Rec.PinsBools
import Johnson.Top.H0.MergeLaw.MaskRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open Johnson.Pack (pMask)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (layAt_plan memAt memAt_some k4DataWide)
open OnBytes.Road.K4.Rec (RecPlan RecIs recPlanOf maskPlan_of_B maskEllP_at)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (layAt messagesAt keptAt sigListCalls)
open VerifiableInference.Desc.First.MergeLaw (MaskAt)
open VerifiableInference.Desc.First.FillSent (maskP)
open VerifiableInference.Desc.First.RecordPlan (seatP rowBitsP)
open VerifiableInference.Desc.K9 (segAt? seatAt)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (MsgT Mem seatOf mgBase)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **What the plan says of the segment's mask row, at a message number o and a member u of the
witness's list.** R: what the plan holds (`RecPlan`); n: the number of messages sent (not the
member's number in the witness); m: the segment; xl: the lookup's place at the segment. This defines
the form of a conclusion (`maskRowPub_head`) and of a hypothesis (the other statements); the
definition claims nothing. -/
structure MaskRowPub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (R : RecPlan) (n m : ℕ)
    (xl : VerifiableInference.Desc.First.Look.Place) (o : ℕ) (u : Mem) : Prop where
  /-- u's seat and shape are those that the plan gives the first message with mask rows -/
  seat : ∃ (mI : ℕ) (hm : (keptAt h.𝔇.sent xl.link).length + mI <
      (sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link).length),
    ((messagesAt h.𝔇.sent xl.link).findIdx? fun y => y.shape.maskRows != 0) = some mI ∧
    seatOf u = h.𝔇.l3.seat xl.link false ((keptAt h.𝔇.sent xl.link).length + mI) ∧
    (u.1.l.get u.2).1 = ((sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link).get ⟨_, hm⟩).1
  /-- u is the member that is found at its seat -/
  mem : memAt h.𝔇.ms (seatOf u) = some u
  /-- u's shape has a mask row -/
  rows : 0 < (u.1.l.get u.2).1.maskRows
  /-- the place's number of entries of the mask row is within the mask code's length -/
  room : xl.ns ≤ (pMask h.𝔇.cs (u.1.l.get u.2).1).ell
  /-- the library's `MaskPlan`, its line on the mask row's message -/
  oracle : maskP R.shape R.d m = some o
  /-- its line on that message's seat -/
  seated : seatP (h.𝔇.N.sent m 0) R.L.places n o = some (seatOf u)
  /-- its line on the mask table's row bits -/
  oneRow : rowBitsP R.M n o .mask = 0

/-- CONDITIONAL on h, Lh and hx. **THERE ARE SUCH o AND u: FROM THE PUBLIC SIDE ALONE**: no prover,
script, coin or state is named. -/
theorem maskRowPub_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl) :
    ∃ (o : ℕ) (u : Mem), MaskRowPub h
      (recPlanOf (k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase)
        (k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase).sd)
      ((k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase).N.msgsAt
        PS[k]?) m xl o u := by
  have hs := sitsIn_head h Lh hx
  have Pt := pinsTests_head h Lh
  have N := nine_head h Lh
  obtain ⟨x₁, hx₁, el, _, _, _, en⟩ := layAt_plan N.Sx.pubOf N.Sx.notHead N.Sx.step N.Sx.plan
  have ex : x₁ = xl := Option.some.inj (hx₁.symm.trans hx)
  rw [ex] at el en
  have hk := Lh.num
  have hm := Lh.seg
  subst hk hm
  obtain ⟨MP⟩ := maskPlan_of_B _ (Pt.maskPlan xl el en)
  have hell := Pt.ell xl el en
  rw [maskEllP_at _ MP] at hell
  obtain ⟨_, u, hu, hsh⟩ := hs ⟨_, MP.member⟩
  have es := (memAt_some hu).2
  refine ⟨MP.o, u, ⟨MP.mI, MP.member, MP.first, es, hsh⟩, ?_, ?_, ?_, MP.oracle, ?_, MP.oneRow⟩
  · rw [es]
    exact hu
  · rw [hsh]
    exact MP.rows
  · rw [hsh]
    exact hell
  · rw [es]
    exact MP.seated

/-- CONDITIONAL on P and P'. **At one segment at most one pair**: o, u's seat and u are each a
function's value. -/
theorem maskRowPub_one {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh} {R : RecPlan} {n m : ℕ}
    {xl : VerifiableInference.Desc.First.Look.Place} {o o' : ℕ} {u u' : Mem}
    (P : MaskRowPub h R n m xl o u) (P' : MaskRowPub h R n m xl o' u') : o = o' ∧ u = u' := by
  have e1 : o = o' := Option.some.inj (P.oracle.symm.trans P'.oracle)
  subst e1
  have e2 : seatOf u = seatOf u' := Option.some.inj (P.seated.symm.trans P'.seated)
  have m1 := P.mem
  rw [e2] at m1
  exact ⟨rfl, Option.some.inj (m1.symm.trans P'.mem)⟩

/-- CONDITIONAL on P. (iii): u is the first member of the list at its seat, as `List.find?` returns
it. -/
theorem maskRow_find {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh} {R : RecPlan} {n m : ℕ}
    {xl : VerifiableInference.Desc.First.Look.Place} {o : ℕ} {u : Mem}
    (P : MaskRowPub h R n m xl o u) :
    h.𝔇.ms.find? (fun z => decide (seatOf z = seatOf u)) = some u :=
  P.mem

/-- CONDITIONAL on P and hR. **The three facts on a part of the state that reads as the plan
says.** -/
theorem maskRow_of_recIs {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh} {R : RecPlan} {n m : ℕ}
    {xl : VerifiableInference.Desc.First.Look.Place} {o : ℕ} {u : Mem}
    (P : MaskRowPub h R n m xl o u) {a : VerifiableInference.Desc.K9.Part} (hR : RecIs a R n m) :
    maskOracle a.L.check.frame = some o ∧
      seatAt (h.𝔇.N.sent m 0) a.d.book o = some (seatOf u) ∧ a.d.st.rowBits o .mask = 0 :=
  ⟨hR.mask.trans P.oracle, (hR.seat _ o).trans P.seated, (hR.rowBits o .mask).trans P.oneRow⟩

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hT and P. **THE THREE FACTS WHERE THE THREAD STANDS, AT EVERY o AND u OF
WHICH THE PLAN SAYS `MaskRowPub`**: one o and one u for all provers, scripts, coins and states. -/
theorem maskRow_front_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {xl : VerifiableInference.Desc.First.Look.Place} {o : ℕ} {u : Mem}
    (P : MaskRowPub h
      (recPlanOf (k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase)
        (k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase).sd)
      ((k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase).N.msgsAt
        PS[k]?) m xl o u) :
    ∀ a, segAt? s = some a → maskOracle a.L.check.frame = some o ∧
      seatAt (h.𝔇.N.sent m 0) a.d.book o = some (seatOf u) ∧ a.d.st.rowBits o .mask = 0 :=
  fun a ha =>
    maskRow_of_recIs P (recIs_front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT a ha)

/-- CONDITIONAL on h, Lh, hT, P and ha. **The three facts as the library's `MaskAt`**, at the member
u and 0 row bits, where a segment is open. -/
theorem maskAt_front_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {xl : VerifiableInference.Desc.First.Look.Place} {o : ℕ} {u : Mem}
    (P : MaskRowPub h
      (recPlanOf (k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase)
        (k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase).sd)
      ((k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase).N.msgsAt
        PS[k]?) m xl o u)
    {a : VerifiableInference.Desc.K9.Part} (ha : segAt? s = some a) :
    MaskAt (h.𝔇.N.sent m 0) u 0 s :=
  ⟨a, o, ha, maskRow_front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT P a ha⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.maskRowPub_head
#print axioms ProofFile.Honest.K4.W.maskRowPub_one
#print axioms ProofFile.Honest.K4.W.maskRow_find
#print axioms ProofFile.Honest.K4.W.maskRow_of_recIs
#print axioms ProofFile.Honest.K4.W.maskRow_front_head
#print axioms ProofFile.Honest.K4.W.maskAt_front_head
