-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/CommittedColumnsAtMaker.lean: CommittedColumns at the prover that the maker
returns at the online filling before it is read through: what runC_rows_thru asks of the columns, in
scope, at every matrix and randomness.
-/
import AtFullSide.Honest.CommittedColumns
import Johnson.Desc.ProofFile.Honest.ThruAtPure
import E2E.TheHonestProver

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open K5 AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge AtPublicFiles.Committed
open OnBytes.Slice (frS)
open P5J

local instance (priority := high) padsColumnsAtMaker : Nonempty PadZ := pads_nonempty frS 402653181

/-- **The columns of the maker's return are the committer's**, in scope. -/
theorem committedColumns_atFilling (Z : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (o' : ProofFile.SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse matrixInput o' S O) = .ok A)
    (M : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) :
    CommittedColumns (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H id (tableCoins Z) M ρ := by
  intro it p
  have hs : A.H.stored = (onlineProverPartsInUse matrixInput o' S O).enc A.Z :=
    congrArg (fun A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit => A₀.H.stored) (eq_ofFill base)
  have hz := (parts_of_atPure base).1.pub
  show ((if it == 0 then (cmAlong (AZ Z) PadZ (holdZ Z)).enc M ρ p else none).map
      (List.map OnBytes.Slice.ofF)) =
    (A.H.stored M (tableCoins Z ρ) it p).map (List.map OnBytes.Slice.ofF)
  rw [hs]
  exact committedColumnsWords Z scope hz M ρ it p

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.committedColumns_atFilling
