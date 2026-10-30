-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheLetters.lean: the letters of the proof file's three chains, as definitions.

The protocol has three parts, named by what a user holds. offline: the proof in the key file, on the
committed table. link: from a further encoding to the first. online: the proof for a request (the
proof file). The online part has three chains of sub-protocols: the first, the shared, the second.
Each chain's invariant, and each law on it, stands at values of the same letters: thread, Said, keeps,
riders, falls, J, lastAt, numbers, rand, later, G. Here each letter has one value, at the base return
of the maker, or is a named hole. TheOneObject and every payer are to import these files, so that
Lean holds the fit.

What is left open here stands in OpenLast, OpenFiles and OpenG: these files lay no value of them.
OpenShared has its value, openZero.
Two values are read from the plan with a default: sharedBlocks with the empty list, the place of the
test on G_omega with U's. At a plan where these are missing the value would be wrong; that the plan
has them is a premise of IOP's laws (hb, hO), not shown here.

Six points on the letters.
  1  The last chain's letter Said: said₃ below: the field letter at BaseTied with the clause
     TiedToEnds, the object's first form. A five paid at the letter without the clause does not pay
     this one by itself.
  2  Riders: shared chain: none; last chain: lastParts lays doorRider in front of lastRiders []: three
     clauses, at borders 0, 0 and 1. So «2 ≤ lo» holds only of the list behind these, and «0 < lo» only
     of the shared chain's.
  3  Keeps: shared chain: keepsAtBase at keepsOff, a choice; last chain:
     lastKeeps at the clause that says nothing, with K14's clause at member 0 laid by lastThread
     itself; first chain: kpBy fHeadJ, in firstThread.
  4  lastAt: one value of LastLetters: last below, with ends := endsAt: a function of the input, so
     that thread₃ and G's third thread are one term.
  5  By kind or by number at the first chain: the debts are asked by number, and kinds pay at
     P5J.At.ps[b] or at h.firstChain.blocksInOrder[b]. NumberIsPlace states the join; not proved here.
  6  The six names that mean two objects: none of them is used here. Two G's
     remain, of two types: theG here is the base's, over IndexCommitterCoins, the one index privacy stands at;
     completeness states its sides at the online return, over the table's coins, in TheOneObject. The
     crossing between them is the base read through the table's coins (A.thru; ThreadsP.thru). G's
     letter Said is SaidOk, the threads' SaidWalk: see theG.

The letters stand chain by chain in TheLettersFirst.lean, TheLettersShared.lean and TheLettersLast.lean,
so that a chain's payers stand over that chain's files alone; here only G.

Imports. No file is imported for a law. Files that hold definitions read here also hold theorems:
E2E/TheG.lean here, and AtFullSide/K12/LettersAtHead.lean in TheLettersLast. AtFullSide/K12/LaterDefs.lean
in TheLettersShared and K12/AtFile/WLaidDefs.lean in TheLettersLast hold definitions alone.
-/
import AtFullSide.Honest.TheLettersLast
import E2E.TheG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput readsBase laterBase keepsAtBase baseFilling)
open ProofFile.Honest.K1 (firstScriptAt)
open VerifiableInference.Desc (Place Block)
open OnBytes (TableKey)
open VerifierAndGoals (PublicFiles)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

/-! ## G -/

/-- **A named hole of G**: the kinds' rows at the base filling.
-/
structure OpenG (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (Z : PublicFiles) where
  rows : AtPublicFiles.TheSides.KindRows (baseFilling Z) A.Z A.G

/-- **What the three threads take, as G reads it.** -/
def parts {O : OpenShared A} (P : OpenLast h O) : AtPublicFiles.TheG.ThreadParts A WtShared where
  first := first h
  reads := reads h
  shared := shared h O
  last := lastParts h (first h) (last h P)

/-- **G**, at the base filling. Its letters Said are SaidOk (E2E/TheG.lean), which the threads' own
said₁, said₂ imply (saidOk_of_walk): these are two objects, and the step from one to the other is
the payer's. -/
abbrev theG {O : OpenShared A} (P : OpenLast h O) (K : OpenG A Z) :=
  ProofFile.Honest.Term.theGAtBase h (parts h P) K.rows

/-- **G at the description that the return holds**, at the base maker's return. -/
abbrev theGOfBase (made : ProofFile.Honest.Term.baseMaker Z = .ok A) {O : OpenShared A} (P : OpenLast h O)
    (K : OpenG A Z) :=
  AtPublicFiles.TheG.theGOfReturn made h (parts h P) K.rows

end AtFullSide.Honest.TheLetters
