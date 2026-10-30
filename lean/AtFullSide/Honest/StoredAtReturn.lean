-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/StoredAtReturn.lean: the maker's prover has every stored column that the
description declares.

1. returned is what the online maker returns.
2. stored_at_return: at every index and table randomness, every stored table that a round of the
   description declares has, at every position below its depth, a column of the declared width in
   returned.H. This is the hypothesis hst of ProofFile.Honest.planServes (Honest/Law/PlanGives.lean).
3. It reads no request: a matrix out of range and a request that is not served are covered too.
4. Its premises: the table is the committer's (TableIsTheCommitters); scope, the test on the public
   files and LaidAt at the return's public part, places and first chain. stored_at_the_maker has the
   table from tableIsTheCommitters at a return of the maker.
5. The column is the committer's (cmAt, E2E/TiedAtFiles.lean). The item is 0 by itemsZero_of_data,
   the depth by the plan's test and DataFits, the width by width_atFiles.
6. Nothing here is about soundness, completeness or what a view shows.
-/
import AtFullSide.Honest.HonestProverLaws
import AtFullSide.Honest.TableIsTheCommitters
import E2E.RoadPublicRows
import E2E.BridgePaidAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open P5J

local instance (priority := high) : Nonempty PadZ := pads_nonempty OnBytes.Slice.frS 402653181

variable {files : PublicFiles}

/-- **The maker's prover has every declared stored column, at its width.** -/
theorem stored_at_return (returned : OnlineReturn files) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl) (table : TableIsTheCommitters returned)
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction files.pol files.lay files.KL D r returned.Z places firstChain)
    (i : FullSizeMatrix) (ri : (protocolAtFiles files).EncodingRandomness) :
    ∀ d ∈ (descZ returned.Z places firstChain).roundsDeclaredByBlocks.1 ++
        (descZ returned.Z places firstChain).roundsDeclaredByBlocks.2.1 ++
        (descZ returned.Z places firstChain).roundsDeclaredByBlocks.2.2,
      ∀ t ∈ d.stored, ∀ y, y < 2 ^ t.sh.a →
        ∃ u, returned.H.storedWords i ri t.item y = some u ∧ u.length = t.sh.W := by
  intro d hd t ht y hy
  have hit : AtPublicFiles.AtZero.ItemsZero (descZ returned.Z places firstChain) :=
    AtPublicFiles.AtZero.itemsZero_of_data L.data
  have hD := dataFits_atFiles files returned.Z places firstChain scope live L
  have hdepth : t.sh.a ≤ frS.P.T.a :=
    le_of_eq ((((descZ returned.Z places firstChain).planOk_ok).1 L.planOk).depth d hd t ht |>.trans
      hD.depth.symm)
  have hy' : y < 2 ^ frS.P.T.a := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hdepth)
  have hw := width_atFiles files returned.Z places firstChain scope L d hd t ht
  refine ⟨(colF (AZ files) PadZ (holdZ files) i ri ⟨y, hy'⟩).map OnBytes.Slice.ofF, ?_, ?_⟩
  · unfold ProofFile.Honest.Prover.storedWords
    rw [table.2, hit d hd t ht]
    simp [cmAlong, cmAt, hy']
  · simp [colF, hw]

/-- **The same at a return of the maker, the table by `tableIsTheCommitters`.** -/
theorem stored_at_the_maker (returned : OnlineReturn files)
    (made : onlineMaker files = .ok returned) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction files.pol files.lay files.KL D r returned.Z places firstChain)
    (i : FullSizeMatrix) (ri : (protocolAtFiles files).EncodingRandomness) :
    ∀ d ∈ (descZ returned.Z places firstChain).roundsDeclaredByBlocks.1 ++
        (descZ returned.Z places firstChain).roundsDeclaredByBlocks.2.1 ++
        (descZ returned.Z places firstChain).roundsDeclaredByBlocks.2.2,
      ∀ t ∈ d.stored, ∀ y, y < 2 ^ t.sh.a →
        ∃ u, returned.H.storedWords i ri t.item y = some u ∧ u.length = t.sh.W :=
  stored_at_return returned places firstChain (tableIsTheCommitters files scope made) scope live L
    i ri

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.stored_at_return
#print axioms AtPublicFiles.AtFiles.HonestTerm.stored_at_the_maker
