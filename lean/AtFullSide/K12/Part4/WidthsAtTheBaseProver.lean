--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/WidthsAtTheBaseProver.lean: THE PROXIMITY TEST OF THE LAST CHAIN (the kind K12,
at the place W of the proof file): THE WIDTHS OF THE THREE TREES THAT IT TAKES OVER, AT THE BASE
PROVER's OWN TABLES, UNDER THE HEAD AND THE MAKER's RETURN ALONE. One statement, as a definition of
type Prop, and its proof: a joining of laws.

WHAT IT IS NOT.
  * A WIDTH IS A PUBLIC NUMBER: how many words a column of a tree's table has. Nothing is said of
  what
    the tables hold, nor that they are the tables which the test's job reads.
  * Not the structure WidthsAt itself (Honest/K12/AtFile/WTable.lean): its three
    fields are written out, at tb₁ := the table of the first chain's Script at the base prover and
    tb₂ := tableShared. Whoever holds that file closes the structure with the three, at every r₁ and
    toCommon, which the structure does not read.
  * That the first thread's Script IS firstScriptAt, and the shared thread's table IS tableShared,
  is
    the threads' letters' matter.
  * AT THE BASE PROVER (the filling onlineProverPartsInUse), not read through.
  * CONDITIONAL on the library's hypothesis at the full size and on the maker's return. That either
    can be met is not shown here.
  * It stands over files of three houses that lie in no sealed tree: the first chain's Script and
    what lies beneath it (AtFullSide/K1/FirstScript.lean), tableShared and what lies beneath it
    (Honest/K12/AtFile/TableShared.lean), and Honest/K12/Part4/Widths.lean.
  * No run is named; nothing on completeness, on soundness or on what a proof hides.

WHAT IT IS. The law of Honest/K12/Part4/Widths.lean asks, at the members 2 and 356 of the first
chain, three fields of the shared sending's record and that the thread's table is the job's own
text; and of the book that it is the one which the maker's routine returns at the written
description. At the base prover all are theorems under the head and the return: k1Seated_first,
ownTrees_first_two, ownTrees_first_w (AtFullSide/K1/FirstScript.lean) and makers_book_one
(AtFullSide/K14/MakersBookOne.lean, sealed). So no premise is left but these two.
-/
import AtFullSide.K1.FirstScript
import AtFullSide.K14.MakersBookOne
import Johnson.Desc.ProofFile.Honest.K12.Part4.Widths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open OnBytes (TableKey)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.K1 (firstScriptAt k1Seated_first ownTrees_first_two ownTrees_first_w witB jobTwoAt
  jobWAt)
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.AtFile (tableShared)

/-- **THE THREE WIDTHS AT THE BASE PROVER's OWN TABLES**, under the head and the maker's return
alone: the fields masks, own and omega of WidthsAt, written out. -/
def WidthsAtTheBaseProver : Prop :=
  ∀ (W₀ : Type) (Z : VerifierAndGoals.PublicFiles) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)
    (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) (D : WholeD) (r : LPFD.Full.RunPF) (Np : H2U.Places4)
    (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place),
    AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x →
    onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A →
    ∀ (Ws Rs Xs : Type) (weights : Ws → Weights) (rand : Rs → TableRand)
    (testOnU testOnOmega : TestJob (Common Ws Rs TableKey) Xs) (ownShared : Xs),
    (∀ k v hd, ((firstScriptAt I S Op A cF).table (.own 1) k v hd).2.words = 3) ∧
    (∀ k v hd, ((firstScriptAt I S Op A cF).table (.own 82) k v hd).2.words = 12) ∧
    ∀ (k : Coins A.B) v hd,
      (tableShared (VerifiableInference.Desc.K1.qAt A.Z Np) weights rand testOnU testOnOmega
        ownShared (.own 1) k v hd).2.words = 36

theorem widthsAtTheBaseProver : WidthsAtTheBaseProver := by
  intro W₀ Z I S Op A D r Np cF x h hA Ws Rs Xs weights rand testOnU testOnOmega ownShared
  obtain ⟨B, hB, -, -, -, hall⟩ := AtFullSide.K14.makers_book_one h
  obtain ⟨eB, -⟩ := hall _ _ _ _ _ _ A hA
  have hB' : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok A.B := by
    rw [eB]
    exact hB
  -- the first chain's two, at the thread whose one input is the input that is asked about
  have first : ∀ v : K1.LocB W₀, (∀ k u hd, ((firstScriptAt I S Op A cF).table (.own 1) k u hd).2.words = 3) ∧
      ∀ k u hd, ((firstScriptAt I S Op A cF).table (.own 82) k u hd).2.words = 12 := by
    intro v
    obtain ⟨⟨blockOpening, K2⟩, -, ⟨blockLast, KW⟩⟩ := k1Seated_first h hA (fun _ _ => none)
      (fun _ _ _ _ => True) 0 0 0 0 (fun _ => True) (fun _ _ _ => True) (fun _ _ _ => True) v
    exact firstChainsTakenTreesHaveTheirWidths _ _ _ _ Z D r A.Z Np cF x h _ _ A.H A.B
      (firstScriptAt I S Op A cF) (fun _ _ => none) (fun _ _ _ _ => True) 0 0 0 0 (fun _ => True)
      (fun _ _ _ => True) (fun _ _ _ => True) v (witB I A.Z) (jobTwoAt S A.Z A.G)
      (jobWAt Op A.Z A.G) () (fun _ => 0) (fun _ => 0) blockOpening blockLast K2.member
      K2.shape.2.2 K2.hasCoins
      (ownTrees_first_two h hA (fun _ _ => none) (fun _ _ _ _ => True) 0 0 0 0 (fun _ => True)
        (fun _ _ _ => True) (fun _ _ _ => True) v)
      KW.member KW.shape.2.2 KW.hasCoins
      (ownTrees_first_w h hA (fun _ _ => none) (fun _ _ _ _ => True) 0 0 0 0 (fun _ => True)
        (fun _ _ _ => True) (fun _ _ _ => True) v)
  exact ⟨fun k v hd => (first v).1 k v hd, fun k v hd => (first v).2 k v hd,
    sharedChainsTakenTreeHasItsWidth OnBytes.secondHashFunction Z D r A.Z Np cF h.toAtMg A.B Ws Rs Xs weights
      rand testOnU testOnOmega ownShared hB'⟩

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.widthsAtTheBaseProver
