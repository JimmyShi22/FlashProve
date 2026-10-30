-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingFront.lean: `FrontAsksD` (K12/ShapeAllDense.lean) at
the verifier's record in front of the first chain's closing proximity test, under the library's head,
at a state reached at that test's border: of its hypotheses on the state on entry two are paid here
and two stand as premises.

  `frontAsksD_at_L`   at a job whose state on entry at one input and front is that record: where the
                      public test `frontFiveB` passes at the record's shape and the test on the open
                      rows `claimsB` passes at the record, `FrontAsksD` holds at some plain data

By what. `frontAsksD_of_five` (K12/FrontAtShapeDense.lean); `four_at_finish`
(K12/AtProof/FieldsAtFinish.lean): the statement is tidy; `taken_dense_entered`
(Johnson/AtFull/Shape/TakenRowsDense.lean): the rows taken in are dense.

Hypotheses. h: the head. hr, he: the state is reached at border 354 and the way in returns the
record. hJ: the job's state on entry there is the record. hE: the place's masks come early. h5, hc: the
two premises.

Limits.
- `frontFiveB` reads the shape; `claimsB` reads the open rows' summands. No theorem here shows
  either: `claimsB_at_L` (ClosingClaims.lean) gives the second from the first.
- "Reached" is with the test on the words in front of each decision: a thread gives it by
  `reach_below` (Thread/SaidOk.lean) at `SaidOk`.
- At the format's own hash, at the full size; the head has a member at named public files alone.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.FieldsAtFinish
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShapeDense
import Johnson.AtFull.Shape.TakenRowsDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes (Codes)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open H2K.First (Plain)
open H2K.Member (codesFull)
open ProofFile.Honest.Sh (testSh claimsB)
open P5J (AtMgA)

variable {W X : Type}
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`FrontAsksD` at the verifier's record in front of the test.** -/
theorem frontAsksD_at_L (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (J : TestJob W X) (w : W)
    (fr : Front X) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) {T : T12}
    (he : enterFinish s = .ok T) (hJ : J.rec₀ w fr = T) (hE : J.p.early = true)
    (h5 : frontFiveB J.p codesFull (testSh T) = true) (hc : claimsB T = true) :
    ∃ Dp : Plain, FrontAsksD J w fr codesFull Dp := by
  refine frontAsksD_of_five J w fr codesFull hE ?_ ?_ ?_ ?_
  · rw [hJ]
    exact h5
  · rw [hJ]
    exact (AtProof.four_at_finish h.toAtMg hr he).1
  · rw [hJ]
    exact Johnson.AtFull.Shape.taken_dense_entered h hr he
  · rw [hJ]
    exact hc

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.frontAsksD_at_L
