-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/OutputHeadFiveAtTheNamedFiles.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of the
online proof): ALL FIVE STATEMENTS THAT THE MEMBER OWES AT ITS BORDER (FiveAtBorder at border 341,
Honest/Thread/FiveAtBorder.lean), AT THE FIRST CHAIN's THREAD AT THE RETURN OF THE MAKER AT THE BASE
FILLING OVER THE MATRICES, WITH THE FIRST CHAIN's SCRIPT AS A VALUE: AT ALL PUBLIC FILES IN SCOPE AT
WHICH THE LIBRARY's TEST protocolDataWellFormed PASSES, AND SO, WITH NO PREMISE, AT THE TWO NAMED SETS OF PUBLIC
FILES (VerifierAndGoals.NamedFiles).

WHAT IT IS NOT. "NO PREMISE LEFT" IS NOT "NOT EMPTY". THAT THE THREAD's INVARIANT HOLDS AT ANY STATE
IN FRONT OF MEMBER 341 IS SHOWN BY NOBODY, AND WHERE IT HOLDS NOWHERE ALL FIVE SAY NOTHING. That any
input is valid (ReadyInput) at these values is shown at one of the two named sets of files alone,
storedPublicFiles, clause by clause and not under that name (inputAroundTheStart_atStoredFiles,
AtFullSide/HonestTrace/EntersAtStoredFilesInput.lean, with no premise); at the other, zGap, by
nobody. FOUR OF THE FIVE ARE LIGHT: they follow from the seat and the kind's own clause of what a
step keeps; the weight lies in the fifth, ExchangeS. It is not completeness, and it does not say
that the verifier accepts. It is one member's share, of 358 members of one of three chains. Each of
the five speaks only of states at which the thread's invariant holds in front of the member, with
the parameter Said. It is at the base filling, not at that filling read through readers, which is
the form of the honest prover's own filling. The trace of matrixInput is a definition by choice at
the full size, which no program runs. That the prover's sides of the code switch play the Script's
texts is not said here. The full size and the format's second hash function alone. It stands at a filling
that its reviewer has cleared as the base for the proofs; two named debts stand before anything at
it counts: that W's rows are ready where their sender plays (number 356), and that the lent words of
the message o_sp are tied at the tests U and O (numbers 9 and 10 of the shared chain). Closed facts
that Lean's kernel decided by evaluation at written values lie beneath, replayed by no independent
checker, among them "protocolDataWellFormed passes" at the two named sets of files. THE BOOK's TEST BENEATH
(lendsPart, by makers_book_one and switch_lends_at_written, AtFullSide/K14/) asks name, count and
that the owners' cuts fit: it holds as well at a book that lends another owner's coins of that
count. Nothing on soundness or on what a proof hides.

WHAT IT IS.
  allFiveAtTheBaseProver   the five under "the maker returns at the base filling" and the head at
                           the return: four by fourAtTheBaseProver
                           (Honest/K6/Term/AtTheFirstThread.lean), the fifth by
                           exchangeAtTheFirstThread
  AllFiveAt                the statement at a set of public files: the maker at the base filling
                           (baseMaker, E2E/BaseMaker.lean) returns; there is a
                           head at the return; and at every head there, at all stated numbers of the
                           falls, inputs, Said and fall, the five hold
  allFiveInScope           it holds in scope where protocolDataWellFormed passes: the maker returns
                           (maker_returns_matrix, AtFullSide/K1/MakerReturnsBase.lean) and there is
                           a head at the return (headAtReturn_base, AtFullSide/K1/HeadAtReturn.lean)
  allFiveAtTheNamedFiles   it holds at the two named sets of files (premises_zFull, premises_zGap,
                           AtFullSide/Bind/LiveAtNamed.lean)

WORDS. As in Statements.lean of the folder Johnson/Desc/ProofFile/Honest/K6/Term/: a border is the
point in front of a member of a chain's blocksInOrder list; a thread is the structure of parameters of one
chain's invariant, and its parameters are called letters; the seat is the sentence "the prover's
first side at the member's place is this kind's row". Besides: the maker is the function that makes
the prover, its book of coins and its ground from the public files and a filling (the choice of the
prover's sides); the Script is what the honest prover's messages are, as functions of a run's coins,
the input and the challenges heard.
-/
import AtFullSide.E2E.OutputHeadDeliversAtTheFirstThread
import AtFullSide.K1.MakerReturnsBase
import AtFullSide.Bind.LiveAtNamed
import E2E.BaseMaker
import Johnson.Desc.ProofFile.Honest.K6.Term.AtTheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.OutputHead
open OnBytes.HonestTrace (Sz)
open ProofFile.Honest (Coins Local Mid OnlineProverWithDescription onlineProverFromPublicFiles IndexCommitterCoins OnlineProverArguments FiveAtBorder onlineProverPartsInUse
  openHonest)
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.K6.Term
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts FallNumbers firstThread)
open P5J (TS)

/-- CONDITIONAL on "the maker returns at the base filling" and on the head at the return; each of
the five speaks only where the thread's invariant holds in front of the member. **ALL FIVE AT BORDER
341, at the first chain's thread at that return**, at parts whose Script is the first chain's
Script.
-/
theorem allFiveAtTheBaseProver {files : VerifierAndGoals.PublicFiles} {Op : OnlineProverArguments}
    {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins ProofFile.Honest.Cells Unit Unit}
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (head : HeadAtReturn files A) (parts : FirstThreadParts A)
    (scriptIsTheFirstScript :
      parts.script = ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref Op A head.firstChain)
    (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    FiveAtBorder (firstThread head parts w) Said fall 341 :=
  have four := fourAtTheBaseProver matrixInput Sz.ref Op makerReturns head parts w Said
  { plays := four.1
    behind := four.2.1
    exchange := exchangeAtTheFirstThread makerReturns head parts scriptIsTheFirstScript w Said
    ridesPast := four.2.2.1
    accepted := four.2.2.2 fall }

/-- **The statement at a set of public files.** The maker returns at the base filling over the
matrices; there is a head at the return; and at every head at the return, at all stated numbers of
the falls, all inputs, all Said and all fall, the five statements hold at border 341 of the first
chain's thread with the first chain's Script. A definition. -/
def AllFiveAt (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins ProofFile.Honest.Cells Unit Unit,
    ProofFile.Honest.Term.baseMaker files = .ok A ∧
    Nonempty (HeadAtReturn files A) ∧
    ∀ (head : HeadAtReturn files A) (numbers : FallNumbers)
      (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells)
      (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells) Unit → Prop)
      (fall : Nat → TS → List Fmt.Drawn → Option String),
      FiveAtBorder (firstThread head
        ⟨ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩ w)
        Said fall 341

/-- CONDITIONAL on "the public files are in scope" and on "the library's test protocolDataWellFormed passes"; each
of the five speaks only where the thread's invariant holds in front of the member. **ALL FIVE AT
BORDER 341.** -/
theorem allFiveInScope (files : VerifierAndGoals.PublicFiles) (inScope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) : AllFiveAt files := by
  obtain ⟨A, makerReturns⟩ :=
    ProofFile.Honest.K1.maker_returns_matrix files Sz.ref openHonest inScope live
  obtain ⟨head, -⟩ := ProofFile.Honest.K1.headAtReturn_base files matrixInput Sz.ref openHonest inScope
    live makerReturns
  exact ⟨A, makerReturns, ⟨head⟩, fun head numbers w Said fall =>
    allFiveAtTheBaseProver makerReturns head _ rfl w Said fall⟩

/- Lean compares the stored files by their names: no step here reads their bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles VerifierAndGoals.zGap

/-- NO PREMISE; each of the five speaks only where the thread's invariant holds in front of the
member. **ALL FIVE AT BORDER 341 AT THE TWO NAMED SETS OF PUBLIC FILES.** -/
theorem allFiveAtTheNamedFiles (files : VerifierAndGoals.PublicFiles) (named : VerifierAndGoals.NamedFiles files) :
    AllFiveAt files := by
  rcases named with rfl | rfl
  · exact allFiveInScope _ AtFullSide.Tie.premises_zFull.1 AtFullSide.Tie.premises_zFull.2.2
  · exact allFiveInScope _ AtFullSide.Tie.premises_zGap.1 AtFullSide.Tie.premises_zGap.2.2

end AtPublicFiles.AtFiles.HonestTerm.OutputHead

#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.allFiveAtTheBaseProver
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.allFiveInScope
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.allFiveAtTheNamedFiles
