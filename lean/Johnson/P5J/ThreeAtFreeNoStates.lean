-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ThreeAtFreeNoStates.lean: `h.Three h.free` WITH NO FACT ON REACHED STATES LEFT.
One theorem.

`three_at_free_row` (Johnson/P5J/ThreeAtFreeRow.lean) leaves hr, T, hNum and hEnd, the one fact on
reached states. `hEnd_at_head_under` (Johnson/Desc/Book/EndTwoAtHead.lean) pays hEnd from
the head, at L the value of `laidAtCodes Zp.first.codes Zp.made.proof.1` and at
M := `msgsOfChain Zp.made.proof.1`. Here it is called, under the head's own `typed`.

  **`three_at_free_no_states`**: h.Three h.free. WHAT STAYS, BY NAME. NO FACT ON REACHED STATES IS
  AMONG THEM:
    hr: one row of tests on the public part (Johnson/P5J/ThreeAtFreeRow.lean says what it carries).
    hB: at every opening of the files to this head's public part and first chain, one test with code
      accepts (`sendsAreB` at 358). A ∀ over openings in form; under the head there is exactly one
      (`h.laid.opened`, `IM.Open.unique`), by reading: so it is one test with code, closed beneath
      the head, as T and hNum are. Its payer: `Meaning.K2.hB_paid` (Johnson/IMR/EndFiveMade.lean),
      under `madeRow`.
    hL: `laidAtCodes` returns a value L. Its payer, where the laws ask thirteen rows or more
      (by the file's rule that tests are only appended: Johnson/Desc/Laid/ProofAsks.lean; this
      library's list has fourteen):
      `AtMg.laid_codes_at_head` (Johnson/P5J/PlanSitsCore.lean).
    T (`PlanSits`) · hNum: closed, at that L and M; nW stays a letter, fixed by hNum.

Read against Johnson/P5J/ThreeAtFreeRow.lean and Johnson/Desc/Book/EndTwoAtHead.lean, which may
still turn.
Limits. A joining: it pays nothing by itself. That what stays can be met is not shown here.
THE WEIGHT OF THE FACT ON REACHED STATES HAS NOT GONE: it rests on
`IM.hEnd_paid` (Johnson/IMR/EndTwoPaid.lean), which `hEnd_at_head_under` calls. "No fact on reached
states is left" is said of this theorem's list of premises.
At the second hash function `OnBytes.secondHashFunction` alone. No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.ThreeAtFreeRow
import Johnson.Desc.Book.EndTwoAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ

open VerifierAndGoals.AtTheName
open VerifiableInference.Desc (Chain KindName)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

open ToldDesc (PlanSits)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB sendsAreB snAt laidAtCodes
  msgsOfChain)
open Johnson.Desc.First.Walk.Tied (Reach)

open VerifiableInference.PlanWritten (madeRow keyOfScan fullKey)

/-- **`h.Three h.free` with no fact on reached states left.** -/
theorem three_at_free_no_states
    (hr : (!Decidable.decide (keyOfScan Zp.p.X.P = fullKey) || madeRow Zp) = true)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B →
      sendsAreB Zp.made.proof.1 358 (snAt Zp Bs.G₀ IM.placesW) = true)
    {L : VerifiableInference.Desc.K12.Door.Laid}
    (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) {nW : ℕ}
    (T : PlanSits L (msgsOfChain Zp.made.proof.1) (LLT25.vAt Zp (At.N Zp cF)) (At.N Zp cF).indexNo
      nW)
    (hNum : (At.N Zp cF).msgsAt none = nW + wMsgs Zp) : h.Three h.free :=
  three_at_free_row h hr
    (VerifiableInference.Desc.Book.hEnd_at_head_under h.toAtMg hB hL h.toAtMg.typed) T hNum

end P5J

#print axioms P5J.three_at_free_no_states
