-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/Kinds/Law/HeadCutsAtHead.lean: THE FIELD head_cuts OF THE TOWER's STRUCTURES FiveF
AND ThreeF, IN THE FIELD's OWN LETTERS AT THE COMPOSED MEANING's CONSTANT, FROM THE CONSTANT's HEAD
ALONE, WHERE THE PROOF FILE's LIST OF ENTRY TESTS HOLDS THE PUBLIC TEST madeRow (as
ProofAsksFirstThirteenTests.lean's does). One theorem: two calls.

  head_cuts_at_head   Law/HeadCutsFive.lean's head_cuts_of_guard; its premise is
                      asks_made_at (Johnson/Desc/Laid/ProofAsksForms.lean) at the head's own fields
                      h.laid.asks ("every entry test accepts") and h.laid.pub (the maker's public
                      plan). The scope is not read for it.

THE CALL. ThreeF.mk (head_cuts_at_head h) _ _ and FiveF.mk (head_cuts_at_head h) _ _ _ _ stand at
h.Three L and h.Five L n, at every L and n (Law/HeadCutsFive.lean's three_head and five_head show
the fit; a maker calls the constructor, not these two).
WHAT IT IS NOT. An implication. THE HEAD h IS A PREMISE: a member of the head is proved at storedPublicFiles and
zGap alone (at secondHashFunction; side library AtFullSide/Top/). "FROM THE HEAD
ALONE" IS TRUE ONLY WITH THE LIST's VERSION NAMED: the head names the list LPFD.lawsAsk
(Johnson/Desc/Laid/ProofAsks.lean) by name, so h says more over ProofAsksFirstThirteenTests.lean's list (thirteen
rows) than over ProofAsksFirstEightTests.lean's (eight rows, which do not hold the test): THE TEST HAS MOVED
INTO h; whoever has h.laid from the verifier's accept has it from there. The head's other fields
(the tests on the list of rounds, headAt, cols13, opts, k3) stay as they were. A joining: the weight
lies in the files beneath. Nothing on a prover, a run or an error bound. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Johnson.Desc.Kinds.Law.HeadCutsFive
import Johnson.Desc.Laid.ProofAsksForms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (ppAtFiles)
open OnBytes.Maker (WholeD)
open OnBytes.Flat (putReq numsFull)
open P5J (AtMgA TS F0T At.X At.cs At.arr At.ms At.N At.layout At.num At.d₀ At.EAt At.Tok
  hidAtSeat HidAt tokVOf dtK CellsM colsAt)

/-- **THE FIELD head_cuts IN ITS OWN LETTERS, FROM THE HEAD ALONE.** -/
theorem head_cuts_at_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA o Z D r Zp Np cF x) :
    P5J.HeadCuts (ppAtFiles Z.pol Z.KL) putReq
      (hidAtSeat (At.X Zp) (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF)
        (Meaning.sizesOf (At.X Zp))
        (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp)
          (Meaning.sizesOf (At.X Zp))) tokVOf
        (fun a => (Meaning.backReq ((fun q : ProofFile.InstPub => q.request) a.1)).getD At.d₀)
        (fun a y => dtK (At.EAt Z) o Zp Np cF h.plan.shape 0 y.cell a) h.plan.hN h.plan.hG :
        HidAt (At.X Zp) (F0T o Zp Np cF).XiPub (Wit (CellsM numsFull) At.Tok MsgT) numsFull.rows
          (colsAt numsFull))
      (h.toAtMg.𝔇 h.𝔇).headPart :=
  head_cuts_of_guard h (LPFD.asks_made_at h.laid.asks h.laid.pub)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.head_cuts_at_head
