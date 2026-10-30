-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/NuHead.lean: CONDITIONAL.

What is here. THE LOOKUP's OWN SENTENCE ON THE PLANES (`K3Planes`) COMES OUT OF THE THREAD, at the
thread with the library's own values (`lettersHead`, Honest/Thread/FirstHead.lean), in front of the
member of the feed-forward layers' own rounds (sub-protocol K4): the item `Item.worth m 2 "planes"`
is one of the eight that the member's row asks, so it is open in front of the member and the thread
holds its sentence; by the library's `mgAll_worth_lay_planes` (Johnson/Desc/Sound/MgAllAt.lean) that
sentence is `K3Planes` at all rounds whose end values are what the lookup has heard, at the reading
`layNu` of the lookup's caller (Johnson/Desc/First/Look/K3LayGoodIn.lean). Law/W/NuCutHead.lean
spends it for `LookNuAt`. Each proof is a chain of calls.

  `planes_item_head`, `planes_lay_head`   the item's sentence out of the thread; the same in the
      lookup's own terms. After `rider_item_head` and `rider_lay_head` (Law/W/OpenAtHead.lean).

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN: hT
: Thr is a hypothesis. THAT THE ITEM's SENTENCE IS EVER MADE TRUE: it is owed behind the member of
the lookup on the calls, whose row opens the item; no file of the honest side shows it there. A,
hpc, hna, hx, ht: on public lists and numbers. NOTHING ON THE MASK ROW: the tie of its two readers,
below the place's number of slots, is Law/W/ReadersHead.lean's (`maskCut_head`). The side library
AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with A, hT, hpc, hna, hx and ht no example is known to us. THE FULL SIZE
ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness, on completeness
or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. A LAW,
NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LookHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Road.K4 (AtK4)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Look (attAt layAt tlAt pubAt stepOf)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase linksFull mgAll_worth_lay_planes)
open VerifiableInference.OnPublicFiles (layWorthPlanes)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-! ## 1 The item's sentence -/

/-- CONDITIONAL: on h, A and hT. **THE SENTENCE OF `Item.worth m 2 "planes"` OUT OF THE THREAD**, at
every continuation of the challenges heard. -/
theorem planes_item_head
    {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (ds' : List Fmt.Drawn) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.means mm.st.input
      (Item.worth m 2 "planes") (mm.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.strs E)
      (Q.wit c mm.st.input (mm.st.heard ++ ds')) :=
  item_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT
    (open_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) onePass_full
      (i := Item.worth m 2 "planes")
      (by
        rw [asks_k4 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) A]
        exact .tail _ (.head _))) ds'

/-- CONDITIONAL: on h, A, hT, hpc, hna, hx and ht. **THE SAME IN THE LOOKUP's OWN TERMS.** x: the
lookup's place at the segment. tl: the sub-proof's plan there. -/
theorem planes_lay_head
    {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (ds' : List Fmt.Drawn) (hpc : VerifiableInference.Desc.K3.pieceAt (P5J.At.X Zp) m false = 2)
    {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (hna : attAt (P5J.At.X Zp) m = none) (hx : layAt (P5J.At.X Zp) m = some x)
    (ht : tlAt (P5J.At.X Zp) m = some tl) :
    layWorthPlanes x (pubAt (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) tl h.𝔇.sent h.𝔇.l3.rad
      h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc (fun j => h.𝔇.l3.seat x.link false j.1)
      h.𝔇.l3.arr h.𝔇.l3.msgW (fun t : TS => t.fork?) (fun t : TS => t.lookHeard?) s
      (Q.wit c mm.st.input (mm.st.heard ++ ds')) := by
  have q := planes_item_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A hT ds'
  have q' : (mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX }
      mgBase).worth m 2 "planes" (mm.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.strs E)
      (Q.wit c mm.st.input (mm.st.heard ++ ds')) := q
  rw [← hpc, mgAll_worth_lay_planes _ _ m hna hx ht] at q'
  exact q'

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.planes_item_head
#print axioms ProofFile.Honest.K4.W.planes_lay_head
