-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/OutputHeadDeliversAtTheFirstThread.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of
the online proof): CONDITIONAL ON TWO PREMISES, "THE MAKER RETURNS AT THE BASE FILLING OVER THE
MATRICES" AND THE LIBRARY's HYPOTHESIS AT THAT RETURN: BEHIND THE MEMBER's ACCEPTING STEP WHAT THE
MEMBER OWES IS DELIVERED (the statement ExchangeS at border 341), AT THE FIRST CHAIN's THREAD AT
THAT RETURN (firstThread, Honest/Thread/TheFirstThread.lean) WITH THE FIRST CHAIN's SCRIPT AS A
VALUE (firstScriptAt, AtFullSide/K1/FirstScript.lean). No premise on the Script, on the valid
inputs, on the book or on the trace is left.

WHAT IT IS NOT. It is one of the five statements that a member owes at its border, not all five, and
it is not completeness: it does not say that the verifier accepts. It speaks only of states at which
the thread's invariant holds in front of the member, with the letter Said: where that holds nowhere,
it holds for nothing; that it holds somewhere is not shown here. "The maker returns" and the
library's hypothesis at the return are premises. It is at the base filling, not at that filling read
through readers, which is the form of the honest prover's own filling. The trace of matrixInput is a
definition by choice at the full size, which no program runs. That the prover's sides of the code
switch play the Script's texts is not said here. The full size and the format's second hash function alone.
It stands at a filling that its reviewer has cleared as the base for the proofs; two named debts
stand before anything at it counts: that W's rows are ready where their sender plays (number 356),
and that the lent words of the message o_sp are tied at the tests U and O (numbers 9 and 10 of the
shared chain). Closed facts that Lean's kernel decided by evaluation at written values lie beneath,
replayed by no independent checker: on the book, on the written places of the code switches, on
their closings, on the layout. THE BOOK's TEST BENEATH (lendsPart, by makers_book_one and
switch_lends_at_written, AtFullSide/K14/) asks name, count and that the owners' cuts fit: it holds
as well at a book that lends another owner's coins of that count. The first clause of ReadyInput,
which is spent here whole, holds tests on the table's key: whoever takes this thread toward a
statement on hiding must know it. Nothing on soundness or on what a proof hides.

WHAT IT IS. deliversAtTheMatrices (AtFullSide/E2E/OutputHeadBelowAtTheHonestProver.lean) at these
values. The seat: seatAtTheBase (Honest/K6/Term/SideAtFilling.lean). The nine premises of
HeadBelowDebts and the two that read the index: AtFullSide/E2E/OutputHeadDebtsAtTheFirstScript.lean.
The code switch's closings: closing_at_head (Honest/K2/Law/ClosingAtHead.lean). The description's
test on the instance: the first clause of ReadyInput, which the thread's invariant holds of its
input.

  exchangeAtTheFirstScript   the statement with the thread's other letters free
  exchangeAtTheFirstThread   the statement at the first chain's thread

WORDS. As in Statements.lean of the folder Johnson/Desc/ProofFile/Honest/K6/Term/: a border is the
point in front of a member of a chain's flat list; a thread is the structure of parameters of one
chain's invariant, and its parameters are called letters; the seat is the sentence "the prover's
first side at the member's place is this kind's row". Besides: the maker is the function that makes
the prover, its book of coins and its ground from the public files and a filling (the choice of the
prover's sides); the Script is what the honest prover's messages are, as functions of a run's coins,
the input and the challenges heard.
-/
import AtFullSide.E2E.OutputHeadBelowAtTheHonestProver
import AtFullSide.E2E.OutputHeadDebtsAtTheFirstScript
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.K6.Term.SideAtFilling
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.OutputHead
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain Strs Place)
open ProofFile.Honest (Coins Local Mid OnlineProverWithDescription onlineProverFromPublicFiles atPure_at_laid_ground IndexCommitterCoins OnlineProverArguments ReadyInput
  ExchangeS onlineProverPartsInUse)
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.K6.Term
open ProofFile.Honest.FirstThread (WtF lettersHead HeadAtReturn FirstThreadParts firstThread
  firstLetters)
open P5J (AtMgA TS F0T)

variable {files : VerifierAndGoals.PublicFiles} {Op : OnlineProverArguments} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins ProofFile.Honest.Cells Unit Unit}

/-- CONDITIONAL on the library's hypothesis h at the return's public part and on "the maker returns
at the base filling"; it speaks only where the thread's invariant holds in front of the member.
**BEHIND THE MEMBER's ACCEPTING STEP WHAT THE MEMBER OWES IS DELIVERED, at the first chain's Script,
the returned prover and ReadyInput**; the thread's other letters are free. -/
theorem exchangeAtTheFirstScript {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction files D r A.Z Np cF x)
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ : Nat) (Rd : Nat → Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells) Unit → Prop) :
    ExchangeS (lettersHead h A.H (ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref Op A cF) test
      carryX item n₁ n₂ 339 (ReadyInput (F0T OnBytes.secondHashFunction A.Z Np cF) A.H) Rd Kp w).thread Said
      341 := by
  refine deliversWhereItDeliversAtAValidInput fun ready => ?_
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, sameGround, -⟩ := atPure_at_laid_ground h.laid O.blank makerReturns
  have closingsReturn : ∀ p ∈ ProofFile.Honest.K2.switchPlaces A.Z A.G,
      ProofFile.Honest.K2.closingOk ProofFile.Honest.K2.freshTable
        ((ProofFile.Honest.K2.segmentsOf A.Z A.G).take p.link) p = true := by
    rw [sameGround]
    exact ProofFile.Honest.K2.Law.closing_at_head h.toAtMg O
  obtain ⟨p, debts⟩ := debtsAtTheFirstScript h makerReturns closingsReturn test carryX item n₁ n₂
    Rd Kp w Said
  exact deliversAtTheMatrices h makerReturns (seatAtTheBase h matrixInput Sz.ref Op makerReturns)
    debts ready.1 (fun valid => readyInputCarriesTheTrace makerReturns valid)
    (fun _ i holds => firstScriptsCellsHoldTheIndex w i holds)

/-- CONDITIONAL on "the maker returns at the base filling" and on the head at the return, which
holds the library's hypothesis; it speaks only where the thread's invariant holds in front of the
member. **THE SAME AT THE FIRST CHAIN's THREAD AT THAT RETURN**, at parts whose Script is the first
chain's Script; the falls' stated numbers are free. -/
theorem exchangeAtTheFirstThread
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (head : HeadAtReturn files A) (parts : FirstThreadParts A)
    (scriptIsTheFirstScript :
      parts.script = ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref Op A head.firstChain)
    (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells) Unit → Prop) :
    ExchangeS (firstThread head parts w) Said 341 := by
  unfold firstThread firstLetters
  rw [scriptIsTheFirstScript]
  exact exchangeAtTheFirstScript head.head makerReturns _ _ _ _ _ _ _ w Said

end AtPublicFiles.AtFiles.HonestTerm.OutputHead

#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.exchangeAtTheFirstScript
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.exchangeAtTheFirstThread
