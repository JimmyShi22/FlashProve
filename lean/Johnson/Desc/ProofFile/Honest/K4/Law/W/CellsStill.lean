-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/CellsStill.lean: CONDITIONAL.

What is here. THE HYPOTHESIS hc OF THE EXCHANGE AT THE OWN ITEM OF THE FEED-FORWARD LAYERS' OWN
ROUNDS (sub-protocol K4), AT EVERY CONTINUATION OF THE CHALLENGES, FROM THE SAME SENTENCE AT WHAT
WAS HEARD, WHERE THE SCRIPT's MESSAGES AT THE SEATS OF `pinSeats` TURN NO MORE. hc (`CellIsList`,
Law/W/CellsTieOf.lean) holds the honest cells against the list of integers that the library's
meaning reads off the script's witness for the group; it reads that list's images in the field
alone. By `matsAre_head` (Law/W/MatsAreHead.lean) these images are, at every witness, the matrices
that the caller of the lookup on the link's calls reads off the witness. That caller's tuple of
messages (`layMs`, Johnson/Desc/First/Look/K3LayGoodIn.lean) reads of a witness its cells and, for
each member of the caller's list, the message and the pad at that member's seat (the library's
`msgsOf_congr`, Johnson/Desc/Sound/ReadsAtMg.lean); and each such seat is one of `pinSeats N m`
(`sitsIn_head`, Law/W/ReadersHead.lean): the seats of the segment's first moment, `N.sent m 0`, and
the seat of the index (Johnson/Road/K4/K4Pins.lean). SO THE SEATS OF THE SEGMENT's LATER MOMENTS ARE
NOT READ. A hypothesis over the segment's whole group of seats would take in seats whose messages,
by a reading of the library's table, are sent behind K4's member.

  `layMs_congr_head`   two witnesses that agree in the cells and, at the seats of `pinSeats`, in
      message and pad, give the caller one tuple.
  `casts_congr_head`   so the images of the group's list are the same.
  `cellIsList_congr`   so `CellIsList` goes over from one to the other.
  `cellIsList_heard`   **at every continuation, from what was heard**; hfix: numbers on the script.
  `cellIsList_thr`   **the same where the thread stands**, from the frame's test on the script.

Not shown here. h0: THAT THE HONEST CELLS ARE THE LIST's, at what was heard: a hypothesis on the
script and the trace: all that hc says of values is left in it. hfix: each message at a seat of
`pinSeats` reads no more challenges than were heard. hQf: the frame's test with code on the script
accepts (`Script.msgsFit`, Honest/Thread/ScriptFit.lean). hb0: at each seat of `pinSeats` the
message's number lies below nMsg, and the message is born at or in front of the member (born n: the
border behind the member that sends message n, the first at which an item may speak of it, by that
file's words): hypotheses. TWO LAYINGS OF THE PARAMETERS WOULD MAKE hQf AND hb0 FALSE TOGETHER, by a
reading: nMsg must count no more than the first chain's messages (the numbers `arr` run over all
three chains, and hQf stands at the first chain's thread); and at a message that is sent again as a
kept copy under the same number born is the border behind its FIRST sender. By the same reading the
seats of `N.sent m 0` hold the carried message, kept copies, the segment's own arrays and a fresh
mask, and in segment 0 the messages at the start (`rolesOf`, Johnson/P5T/PlanSeats.lean). The
library has, under h, its own test on the fence (`P5J.AtMg.fence`, Johnson/P5T/FenceAtMg.lean;
`fencedB_at_k4`, Johnson/Road/K4/K4PinsFence.lean): every sampled tenant of an open pin sits in a
tree that members in front have told; it is not called here, and nothing ties it to born. WHETHER
hb0 AND hQf CAN HOLD TOGETHER AT AN HONEST SCRIPT IS NOT SHOWN AND NOT TESTED. What speaks for it is
a reading of the library's table of the segments' pieces (`segRow`,
Johnson/Desc/First/Borders.lean): the piece 1 + o puts out `.pin m 0`, in segment 0 with `.pinI`;
K4's own piece 3 + o has `.pin m 0` and `.pinI` in its context; the pieces 4 + o and 6 + o put out
`.pin m 1` and `.pin m 2`; `.pin m t` reads `N.sent m t` and `.pinI` reads `[N.index]`. A test with
code on that table, which can fail, stands for `.pinI`: at the full size's written lists it is open
in front of K4's sub-protocol at all twelve places (`k4_pinI_front_full`, with the control
`pinI_shut_at_two`, Johnson/Road/K4/W/PinIFront.lean). `.pin m 1` and `.pin m 2` are open there at
none of the twelve: said here without a theorem; no theorem of this folder shows it. BORN AGAINST
THE TABLE IS HELD BY NO STATEMENT: the frame's own file says that nothing holds born against the
description's table of sendings. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
The side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Lh (`LaidK4`, Law/SeatedHead.lean) and, in the first three statements, hx: on public
lists and numbers (`layAt_laid`, Law/W/LayAtHead.lean, has hx under h and Lh). Of h together with
Lh, hQf, hb0, hT and h0 (`cellIsList_thr`) no example is known to us; nor of h together with Lh,
hfix and h0 (`cellIsList_heard`). hcl, hm and hp (the first three statements, with Lh and hx;
`cellIsList_congr` takes h0 besides): that two witnesses agree in the cells and, at the seats of
`pinSeats`, in message and pad; a witness with itself meets them, and there the three say nothing.
Law/ExchangeOwnStill.lean calls `cellIsList_thr`. THAT THE THREAD STANDS AT ANY RUN. No test holds
any of the five statements against a case that could refute it. THE FULL SIZE ALONE, and the
format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness, on completeness or on
any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. They
come with h, through Law/W/MatsAreHead.lean, whose head names the statements under Johnson/Goal/ on
which `matsAre_head` rests. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MatsAreHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellsTieOf
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LayAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ScriptFit
import Johnson.Desc.Sound.ReadsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (HTailF2)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open OnBytes.Road.K4 (pinSeats)
open OnBytes.Road.Rows.Norms (castM)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (layAt MatsAre sigListCalls)
open VerifiableInference.Desc.Sound (MsgT msgsOf_congr)
open VerifiableInference.OnPublicFiles (layMs)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead wit_msg_more wit_msg_at)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 Two witnesses -/

/-- CONDITIONAL: on h, Lh, hx, hcl, hm and hp. **The caller's tuple of messages hangs on the witness
through its cells and the seats of `pinSeats` alone.** xl: the lookup's place at the segment. -/
theorem layMs_congr_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (w w' : WtF) (hcl : w.cells = w'.cells)
    (hm : ∀ y ∈ pinSeats h.𝔇.N m, w.msg (h.𝔇.arr y.1 y.2) = w'.msg (h.𝔇.arr y.1 y.2))
    (hp : ∀ y ∈ pinSeats h.𝔇.N m, w.pad y.1 y.2 = w'.pad y.1 y.2) :
    layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr
        h.𝔇.l3.msgW w =
      layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr
        h.𝔇.l3.msgW w' := by
  have hs := sitsIn_head h Lh hx
  rw [← Lh.seg] at hs
  funext i
  rcases i with _ | i
  · exact VerifiableInference.Desc.First.Look.Stored.msgW_cells w w' hcl
  · exact msgsOf_congr h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link)
      (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr w' w i (hm _ (hs i).1) (hp _ (hs i).1)

/-- CONDITIONAL: as `layMs_congr_head`. **So do the images of the group's list.** -/
theorem casts_congr_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (w w' : WtF) (hcl : w.cells = w'.cells)
    (hm : ∀ y ∈ pinSeats h.𝔇.N m, w.msg (h.𝔇.arr y.1 y.2) = w'.msg (h.𝔇.arr y.1 y.2))
    (hp : ∀ y ∈ pinSeats h.𝔇.N m, w.pad y.1 y.2 = w'.pad y.1 y.2) :
    castM ((h.𝔇.H.hid w).MG g) = castM ((h.𝔇.H.hid w').MG g) := by
  have e1 := matsAre_head h Lh hx w
  have e0 := matsAre_head h Lh hx w'
  unfold MatsAre at e1 e0
  rw [← e1, ← e0, layMs_congr_head h Lh hx w w' hcl hm hp]

/-- CONDITIONAL: as `layMs_congr_head`, and on h0. **`CellIsList` goes over.** wi: the honest side's
small input. -/
theorem cellIsList_congr (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (w w' : WtF) (hcl : w.cells = w'.cells)
    (hm : ∀ y ∈ pinSeats h.𝔇.N m, w.msg (h.𝔇.arr y.1 y.2) = w'.msg (h.𝔇.arr y.1 y.2))
    (hp : ∀ y ∈ pinSeats h.𝔇.N m, w.pad y.1 y.2 = w'.pad y.1 y.2)
    {Qp : K4Pub} {wi : K4In} {tl : HTailF2} (h0 : CellIsList Qp wi ((h.𝔇.H.hid w').MG g) tl) :
    CellIsList Qp wi ((h.𝔇.H.hid w).MG g) tl :=
  fun i a b hi hn ha hb =>
    (h0 i a b hi hn ha hb).trans
      (congrFun (congrFun (congrFun (casts_congr_head h Lh hx w w' hcl hm hp) i) a) b).symm

/-! ## 2 The script's witness at what was heard and at a continuation -/

variable {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- CONDITIONAL: on h, Lh, hfix and h0. **`CellIsList` AT EVERY CONTINUATION, FROM `CellIsList` AT
WHAT WAS HEARD.** hd: the challenges heard. -/
theorem cellIsList_heard (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (c : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn)
    (hfix : ∀ y ∈ pinSeats h.𝔇.N m, Q.fixedMsg (h.𝔇.arr y.1 y.2) ≤ hd.length)
    {Qp : K4Pub} {wi : K4In} {tl : HTailF2}
    (h0 : CellIsList Qp wi ((h.𝔇.H.hid (Q.wit c v hd)).MG g) tl) (d : List Fmt.Drawn) :
    CellIsList Qp wi ((h.𝔇.H.hid (Q.wit c v (hd ++ d))).MG g) tl := by
  obtain ⟨xl, hx, -⟩ := layAt_laid h Lh
  exact cellIsList_congr h Lh hx (Q.wit c v (hd ++ d)) (Q.wit c v hd) rfl
    (fun y hy => wit_msg_more Q c v hd d _ (hfix y hy)) (fun _ _ => rfl) h0

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Ky X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh, hQf, hb0, hT and h0. **THE SAME WHERE THE THREAD STANDS**, from the
frame's test on the script. born, nMsg: that test's parameters. -/
theorem cellIsList_thr {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {born : Nat → Nat} {nMsg : Nat}
    (hQf : Q.msgsFit (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.front
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs born nMsg = true)
    (hb0 : ∀ y ∈ pinSeats h.𝔇.N m,
      h.𝔇.arr y.1 y.2 < nMsg ∧ born (h.𝔇.arr y.1 y.2) ≤ k)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {Qp : K4Pub} {wi : K4In} {tl : HTailF2}
    (h0 : CellIsList Qp wi ((h.𝔇.H.hid (Q.wit c mm.st.input mm.st.heard)).MG g) tl)
    (d : List Fmt.Drawn) :
    CellIsList Qp wi ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g) tl := by
  obtain ⟨xl, hx, -⟩ := layAt_laid h Lh
  exact cellIsList_congr h Lh hx (Q.wit c mm.st.input (mm.st.heard ++ d))
    (Q.wit c mm.st.input mm.st.heard) rfl
    (fun y hy => wit_msg_at (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Q
      hQf (hb0 y hy).1 (hb0 y hy).2 hT.2.1 c d) (fun _ _ => rfl) h0

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.layMs_congr_head
#print axioms ProofFile.Honest.K4.W.casts_congr_head
#print axioms ProofFile.Honest.K4.W.cellIsList_congr
#print axioms ProofFile.Honest.K4.W.cellIsList_heard
#print axioms ProofFile.Honest.K4.W.cellIsList_thr
