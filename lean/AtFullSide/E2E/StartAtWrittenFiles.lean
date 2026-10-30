-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/E2E/StartAtWrittenFiles.lean: THE PROOF FILE'S FIRST TEST ON AN INSTANCE ACCEPTS EVERY
INSTANCE OF THE TYPE, AT EVERY OOD SAMPLE, AT THE LIBRARY'S TWO NAMED SETS OF PUBLIC FILES
(`VerifierAndGoals.storedPublicFiles`, `VerifierAndGoals.zGap`, Ladder/Stored.lean): `StartHeld` (E2E/StartAtFiles.lean), which was
a premise, is shown there. Statements and proofs, by calls; nothing is evaluated here. Toward
completeness; nothing is claimed.

Why. E2E/StartInScope.lean leaves one clause of `StartHeld` open in scope: at every string of the
request file's length the request's item is made, and its comparison with the public part
(`Verify.statementHeld`) accepts. The side library lean/AtFullSide/ has that clause at these two
sets of files (`AtFullSide.Top.item_zFull`, `item_zGap`).

What is shown.
  `laid_of_live`: where the test `protocolDataWellFormed` accepts (`protocolDataWellFormed (asDescriptionFiles Z) = true`) the proof file's
    description is laid: there are letters with `LaidAt` (Johnson/P5J/LaidOpens.lean). At every Z.
  **`startHeld_zFull`**, `startHeld_zGap`: at whatever letters the description is laid there:
    `StartHeld secondHashFunction ProofFile.pureRoad.links Zp`.
  **`okStart_zFull`**, `okStart_zGap`: so the description's first test accepts `instanceAsPlainRecord z` at every
    z.
  **`okStart_zFull_whole`**, `okStart_zGap_whole`: NO PREMISE: there are such letters (`protocolDataWellFormed`
    accepts there: `AtFullSide.Top.theLive_zFull`, `theLive_zGap`), and the test accepts at every z.

Limits.
- storedPublicFiles AND zGap ARE TERMS WRITTEN IN THIS LIBRARY. No Lean code ties them to any file on a disk.
- THE FIRST TEST ON AN INSTANCE ALONE: it reads no prover. Nothing on any later test, round or
  decision.
- At the format's second hash function (`OnBytes.secondHashFunction`), not at a variable.
- It stands over the side library, which no independent checker has replayed (through `lay_size`, by
  which `AtFullSide.Top.item_zFull` and `item_zGap` are paid).
- Nothing on completeness as such, on soundness or on what is hidden.
-/
import E2E.StartInScope
import Johnson.Desc.ProofFile.Law.CarryAtLaw
import Johnson.Goal.Files.FilesReadProof
import AtFullSide.Top.ItemAtFull
import AtFullSide.Top.LiveAtPolicies

set_option autoImplicit false

namespace AtPublicFiles.Start
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord XF)
open OnBytes.Flat (RecFull)
open VerifiableInference.Desc (Chain)
open P5J
open VerifierAndGoals (asDescriptionFiles storedPublicFiles zGap)
open FlashProve (protocolDataWellFormed)

/-- Where the test `protocolDataWellFormed` accepts, the proof file's description is laid. -/
theorem laid_of_live {Z : VerifierAndGoals.PublicFiles} (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ D r Zp Np cF, LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF := by
  obtain ⟨_, P, -, -, hP, -⟩ := FlashProve.theLiveAt_made secondHashFunction (asDescriptionFiles Z) live
  have hP' : LPFD.Full.proofDataAndDecisionOfPublicFiles secondHashFunction Z.pol Z.lay Z.KL = .ok (P.1, P.2) := hP
  obtain ⟨Zp, Np, cF, Ld⟩ := laid_opens hP'
  exact ⟨P.1, P.2, Zp, Np, cF, Ld⟩

variable {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl}

/-! ## At storedPublicFiles -/

theorem startHeld_zFull (Ld : LaidAt secondHashFunction storedPublicFiles.pol storedPublicFiles.lay storedPublicFiles.KL D r Zp Np cF) :
    StartHeld secondHashFunction ProofFile.pureRoad.links Zp := by
  refine startHeld_of_laid VerifierAndGoals.filesRead.full.1 Ld ?_
  rw [(ProofFile.Law.pub_files Ld.pub).1, (ProofFile.Law.pub_files Ld.pub).2]
  exact AtFullSide.Top.item_zFull Ld.publicO

theorem okStart_zFull (Ld : LaidAt secondHashFunction storedPublicFiles.pol storedPublicFiles.lay storedPublicFiles.KL D r Zp Np cF)
    (z : XF × RecFull) : (F0T secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z) = true :=
  okStart_of_public Np cF (startHeld_zFull Ld) z

theorem okStart_zFull_whole :
    ∃ D r Zp Np cF, LaidAt secondHashFunction storedPublicFiles.pol storedPublicFiles.lay storedPublicFiles.KL D r Zp Np cF ∧
      ∀ z : XF × RecFull, (F0T secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z) = true := by
  obtain ⟨D, r, Zp, Np, cF, Ld⟩ := laid_of_live AtFullSide.Top.theLive_zFull
  exact ⟨D, r, Zp, Np, cF, Ld, okStart_zFull Ld⟩

/-! ## At zGap -/

theorem startHeld_zGap (Ld : LaidAt secondHashFunction zGap.pol zGap.lay zGap.KL D r Zp Np cF) :
    StartHeld secondHashFunction ProofFile.pureRoad.links Zp := by
  refine startHeld_of_laid VerifierAndGoals.filesRead.other.1 Ld ?_
  rw [(ProofFile.Law.pub_files Ld.pub).1, (ProofFile.Law.pub_files Ld.pub).2]
  exact AtFullSide.Top.item_zGap Ld.publicO

theorem okStart_zGap (Ld : LaidAt secondHashFunction zGap.pol zGap.lay zGap.KL D r Zp Np cF)
    (z : XF × RecFull) : (F0T secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z) = true :=
  okStart_of_public Np cF (startHeld_zGap Ld) z

theorem okStart_zGap_whole :
    ∃ D r Zp Np cF, LaidAt secondHashFunction zGap.pol zGap.lay zGap.KL D r Zp Np cF ∧
      ∀ z : XF × RecFull, (F0T secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z) = true := by
  obtain ⟨D, r, Zp, Np, cF, Ld⟩ := laid_of_live AtFullSide.Top.theLive_zGap
  exact ⟨D, r, Zp, Np, cF, Ld, okStart_zGap Ld⟩

end AtPublicFiles.Start

#print axioms AtPublicFiles.Start.laid_of_live
#print axioms AtPublicFiles.Start.startHeld_zFull
#print axioms AtPublicFiles.Start.okStart_zFull
#print axioms AtPublicFiles.Start.okStart_zFull_whole
#print axioms AtPublicFiles.Start.startHeld_zGap
#print axioms AtPublicFiles.Start.okStart_zGap
#print axioms AtPublicFiles.Start.okStart_zGap_whole
