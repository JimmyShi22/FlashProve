-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/JoinPubHead.lean: CONDITIONAL. Statements with their proofs.

What is here: THE EIGHT PUBLIC FACTS OF `JoinPubLeft`, WHICH STAND IN THE PLACE OF `JoinWorth` IN
Law/W/FootB1.lean (the cap on the lookup's tables; the verifier's eight lines of calls; the floor on
the tables' sizes; the lookup's shape; the weights' sizes; the number of layers; profile 4; the
tables' padding keys) HOLD UNDER THE LIBRARY's HYPOTHESIS ON THE PUBLIC FILES (h: `P5J.AtMgA`), at
the library's reference sizes and tables. The group g and its plan hp stand in the hypotheses alone
(the library's statement is asked at a group): the eight name neither. `joinPubLeft_head`: at every
public data Q of the feed-forward layers' own rounds (the sub-protocol K4) whose layers' data are
the public structure's. `joinPubLeft_member`: at the member's own public data (`k4PubAt`,
Law/DearTop.lean), under `LaidK4`.
How. Each of the eight is a field of the library's `PubLines` (Johnson/Road/K4/PubAt.lean), to the
letter; `refPub_in_scope` (Johnson/Road/K4/RefInScope.lean) has that structure under h.

Not shown here. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). BESIDE h: hg and hG (the group has a plan) and hP (Q's public
numbers are the public parameters' own), or `LaidK4`, which h gives at each group (`laid_at`,
Law/LaidAtGroup.lean). THE FULL SIZE ALONE, and the format's second hash function alone. s0 stands under ∃;
the field shape0 says of which function it is the value; its tie to the lookup's shape in the
layout: Law/W/JoinPubFo.lean. What Law/W/FootB1.lean asks beside these eight, above all the lookup's
own sentence. PUBLIC FACTS ALONE. Its imports reach files under Johnson/Goal/: a program's walk
from import to import, which reads import lines alone and stops unopened at Johnson/Goal/,
ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 71 modules under Johnson/Goal/:
a floor (with h; `refPub_in_scope` calls a statement of such a file): A LAW, NOT A PART: no file
that defines a part of the proof file's description may import this one. Nothing on soundness, on
completeness or on any other property. No property is claimed.

  `joinPubLeft_head`   **the eight, under h**
  `joinPubLeft_member`   at the member's own public data
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FootB1
import Johnson.Desc.ProofFile.Honest.K4.Law.DearTop
import Johnson.Road.K4.RefInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4 (refPub_in_scope)
open OnBytes.Maker (WholeD)
open Inst.Model (tbRef)
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h, hg, hG and hP. **THE EIGHT PUBLIC FACTS, UNDER h.** -/
theorem joinPubLeft_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) {Q : K4Pub}
    (hP : Q.P = (P5J.At.X Zp).layers) :
    ∃ s0, JoinPubLeft (Verify.layerShape (P5J.At.X Zp).P) Dim.ref Q
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y) tbRef s0 := by
  obtain ⟨s0, HL, -⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  have L := HL (P5J.At.X Zp).layers.tokv
  refine ⟨s0, ?_⟩
  exact
    { cap := L.hc
      lines := by rw [hP]; exact L.hN
      floor := L.hfl
      shape0 := by rw [hP]; exact L.hs0
      sizedW := L.Zw
      L := L.hsL
      p4 := L.h4
      pad := by rw [hP]; exact L.hpad }

/-- CONDITIONAL on h and `LaidK4`. At the member's own public data. -/
theorem joinPubLeft_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) :
    ∃ s0, JoinPubLeft (Verify.layerShape (P5J.At.X Zp).P) Dim.ref (k4PubAt cF k x)
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y) tbRef s0 :=
  joinPubLeft_head h Lh.lt Lh.hp Lh.P

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.joinPubLeft_head
#print axioms ProofFile.Honest.K4.W.joinPubLeft_member
