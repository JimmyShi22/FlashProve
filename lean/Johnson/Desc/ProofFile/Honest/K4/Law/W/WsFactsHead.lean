-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/WsFactsHead.lean: CONDITIONAL.

What is here. At the member's own parameters, under the library's head h, the eight public
hypotheses on the weights' layout that the top statements of Law/W/FootJoin.lean ask beside K4Plan
(`wsFacts_head`): the layout is one that wsLayOf returns, at the shape that the verifier makes of
the public parameters (`Verify.weightShape`) and the library's number of column bits; its widths d
and fe are the layer sub-proof's; four inequalities; a token's number has at least one bit. So at
the head these eight are no hypotheses. By `ws_facts` (Johnson/Road/K4/C/WsFacts.lean) at
`plan_head` (Law/W/PlanHead.lean) and two fields of the library's PubLines
(Johnson/Road/K4/PubAt.lean), which `refPub_in_scope` (Johnson/Road/K4/RefInScope.lean) has under h.

  `wsFacts_head`   the eight.

Not shown here. h (the library's head of the threads' letters) and LaidK4 (Lh): hypotheses; the side
library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth); under h, `laid_at` (Law/LaidAtGroup.lean) has a member of LaidK4 at each of the twelve
groups g, at k = 28 g + 4 and m = 2 g. h STANDS AT THE LIBRARY's FULL-SIZE STRUCTURE AND AT THE
FORMAT's EARLIER HASH: THE STATEMENT HOLDS THERE ALONE. A LAW, NOT A PART: it rests, through
refPub_in_scope, on Meaning.P34.pub34_all, a statement of a file under Johnson/Goal/: no file that
defines a part may import this one. The import closure holds what Law/W/PlanHead.lean's holds.
Nothing on soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PlanHead
import Johnson.Road.K4.C.WsFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (parOf refPub_in_scope)
open OnBytes.Road.K4.C (ws_facts)
open OnBytes.Maker (WholeD)
open Inst.Model.All (DF)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **THE EIGHT PUBLIC FACTS ON THE WEIGHTS' LAYOUT AT THE MEMBER's OWN PARAMETERS.** CONDITIONAL:
on h and Lh. -/
theorem wsFacts_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    wsLayOf (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y) true Inst.Model.Layout.kRef =
        .ok (parOf x).P.wsLay ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).d = (parOf x).P.y.h.d ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).fe = (parOf x).P.y.h.fe ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).dq ≤ (parOf x).P.y.dq ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).f ≤ (parOf x).P.y.h.f ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).fe ≤ (parOf x).P.y.h.f ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).NE ≤ (parOf x).P.y.h.NE ∧
      1 ≤ (parOf x).P.y.h.lt := by
  obtain ⟨_, HL, _, _⟩ := (refPub_in_scope h.scope h.reads h.pubOne Lh.lt).lines x.2.hp Lh.hp
  have PL := HL #[]
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := ws_facts (plan_head h Lh) PL.Zw
  refine ⟨?_, f1, f2, f3, f4, f5, f6, by rw [f7]; decide⟩
  show wsLayOf _ true _ = .ok x.2.P.wsLay
  rw [Lh.P]
  exact PL.hlw

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.wsFacts_head
