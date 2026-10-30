--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/WidthsAtW.lean: THE PROXIMITY TEST OF THE LAST CHAIN (the kind K12, at the place
W of the proof file): THE STRUCTURE WidthsAt (Honest/K12/AtFile/WTable.lean) AT THE
BASE PROVER's OWN TABLES, UNDER THE HEAD AND THE MAKER's RETURN ALONE. One theorem: three fields laid
into the structure.

WHAT IT IS NOT. What AtFullSide/K12/Part4/WidthsAtTheBaseProver.lean's head says: three public
numbers; nothing on what the tables hold; that the threads' tables are these two terms is their
letters' matter; at the base prover, not read through; conditional on the head and on the maker's
return. The letters r₁ and toCommon of the structure are read by none of its fields: the theorem
holds at all of them. Nothing on completeness, on soundness or on what a proof hides.
-/
import AtFullSide.K12.Part4.WidthsAtTheBaseProver
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open OnBytes (TableKey)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)
open ProofFile.Honest.K1 (firstScriptAt)
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.AtFile (tableShared WidthsAt)

/-- **WidthsAt at the base prover's own tables**: the first chain's Script's table and the shared
chain's tableShared; at every r₁ and toCommon. -/
theorem widthsAtW {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (Op : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {Ws Rs Xs : Type} (weights : Ws → Weights) (rand : Rs → TableRand)
    (testOnU testOnOmega : TestJob (Common Ws Rs TableKey) Xs) (ownShared : Xs) (r₁ : Nat)
    (toCommon : K1.LocB W₀ → Common Ws Rs TableKey) :
    WidthsAt r₁ toCommon (firstScriptAt I S Op A cF).table
      (tableShared (VerifiableInference.Desc.K1.qAt A.Z Np) weights rand testOnU testOnOmega
        ownShared) :=
  have a := widthsAtTheBaseProver W₀ Z I S Op A D r Np cF x h hA Ws Rs Xs weights rand testOnU
    testOnOmega ownShared
  ⟨a.1, a.2.1, a.2.2⟩

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.widthsAtW
