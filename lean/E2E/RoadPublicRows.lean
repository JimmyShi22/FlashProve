-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/RoadPublicRows.lean: two hypotheses of `honFit_atFiles` (E2E/BridgeJoinAtFiles.lean) that read
the description `descZ Zp Np cF` alone, and no prover, at a description that `LaidAt`
(Johnson/P5J/LaidOpens.lean) ties to three public files Z in scope. Toward completeness; nothing is
claimed.

  `width_atFiles`: the clause `width` of `PlainAt`: every declared stored table has the encoder's
    width, 2 ^ `frS.P.v`. In scope, under `LaidAt`
  `start_of_item`: the hypothesis h₀: the description's first test accepts one written instance. In
    scope, under `LaidAt`, FROM ONE PUBLIC CLAUSE THAT STAYS A HYPOTHESIS (item, below)
  `width_decl`: general, at every value F of `FileDescription` (Johnson/Desc/Block.lean) for which
    `FileDescription.data` returns: if every stored table of the data's second chain has the width n, every
    declared stored table of F has it
  `widthFit`, `widthFit_proofFull`, `width_writtenP`: a test with code on a file's plain data, its
    yes at the library's written data of the proof file, and what that yes says

By what. `width_decl`: the first and the third chain declare no stored table (`declared_stored`,
Johnson/FrontRoad/StoredItemZeroDeclared.lean); a round of the second chain's data keeps its
declared round's list of stored tables (`zip_stored`, same file). `width_atFiles`: in scope the laid
data are the written ones (`LPFD.Full.laidPOf_written`), as in `nonZero_atFiles`
(E2E/BridgeNonZero.lean). `start_of_item`: `okStart_of_item` (E2E/StartInScope.lean) at the instance
`(dataAtFiles flashProveData Z).G.z₀`.

Hypotheses. scope: `InScope Z = true`. L: `LaidAt` holds of Z's files and (Zp, Np, cF). item: at
every string of the request file's length the request's item is made, and its comparison with the
public part accepts (the field `item` of `StartHeld`, E2E/StartAtFiles.lean).

Limits.
- By inspection, with no theorem: we found no test of the makers' behind `FileDescription.data` that pins a
  stored table's width (`storedFit`, OnBytes/Maker/WholeOf.lean, reads its depth and its item;
  whether the comparison of whole shapes in `Three.Whole.fits` reaches a stored table was not
  traced). So the width is had here in scope alone, off the written data.
- `widthFit_proofFull` is an evaluation in Lean's kernel, over `whole_proofFull`
  (Johnson/G/DryProofTestsFull.lean), which rests on evaluations of its own. That the written data
  are the planner's is no theorem here.
- item is shown of no files here.
- Whether any public files are in scope and meet `LaidAt` is not shown here.
- Statements on declared rounds: nothing on completeness, soundness or hiding.
-/
import E2E.BridgeNonZero
import E2E.StartInScope
import Johnson.FrontRoad.StoredItemZeroDeclared
import Johnson.G.DryProofTestsFull

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Written
open VerifiableInference.Desc
open OnBytes OnBytes.Maker
open OnBytes.Slice (frS)

variable {Xi : Type}

/-- A test with code: every stored table that a round of the second chain's plain data opens has the
width n. -/
def widthFit (n : ℕ) (W : Three.Whole) : Bool :=
  W.ds₂.all fun d => d.stored.all fun s => s.sh.W == n

set_option maxRecDepth 1000000 in
/-- The test says yes at the library's written lists of the proof file, at the encoder's width. -/
theorem widthFit_proofFull :
    widthFit (2 ^ frS.P.v) (wholeAt (some Johnson.G.dryProofFull)) = true := by
  show widthFit (2 ^ frS.P.v) (Three.Whole.of Johnson.G.dryProofFull.1 Johnson.G.dryProofFull.2.1
    Johnson.G.dryProofFull.2.2) = true
  rw [Johnson.G.whole_proofFull]
  decide +kernel

/-- **The proof file's written data**: every stored table of the second chain's rounds has the
encoder's width. -/
theorem width_writtenP :
    ∀ d ∈ Johnson.G.writtenPFull.ds₂, ∀ t ∈ d.stored, t.sh.W = 2 ^ frS.P.v := by
  intro d hd t ht
  have hd' : d ∈ (wholeAt (some Johnson.G.dryProofFull)).ds₂.map rdtOf := hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd'
  have ht' : t ∈ c.stored := ht
  have h := widthFit_proofFull
  unfold widthFit at h
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 h c hc) t ht')

/-- **From the rounds of the data to the declared rounds**: where `F.data` returns D and every
stored table of D's second chain has the width n, every declared stored table of F has it. -/
theorem width_decl {F : FileDescription Xi} {file : String} {D : WholeD} {n : ℕ}
    (h : F.data file = .ok D) (hw : ∀ d ∈ D.ds₂, ∀ t ∈ d.stored, t.sh.W = n) :
    ∀ z ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ z.stored, t.sh.W = n := by
  obtain ⟨s1, -, s3⟩ := OnBytes.FrontRoad.declared_stored h
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, -, rfl⟩ := data_ok h
  obtain ⟨-, w₂, -⟩ := writtenOf_ok hR
  have k₂ : List.Forall₂ (fun (d : Three.RDL) (z : Fmt.DeclaredRound) => d.stored = z.stored)
      (Three.Whole.of R₁ R₂ R₃).ds₂ F.roundsDeclaredByBlocks.2.1 :=
    OnBytes.FrontRoad.zip_stored _ _ _ _ _ _ w₂ _ (sentBefore_length R₂)
  intro z hz t ht
  simp only [List.mem_append] at hz
  rcases hz with (hz | hz) | hz
  · rw [s1 z hz] at ht
    exact absurd ht List.not_mem_nil
  · obtain ⟨c, hc, e⟩ := OnBytes.FrontRoad.mem_of_forall₂ k₂ z hz
    have hc' : rdtOf c ∈ (Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf := List.mem_map_of_mem hc
    have ht' : t ∈ (rdtOf c).stored := by
      show t ∈ c.stored
      rw [e]
      exact ht
    exact hw (rdtOf c) hc' t ht'
  · rw [s3 z hz] at ht
    exact absurd ht List.not_mem_nil

end AtPublicFiles.Written

namespace AtPublicFiles.AtFiles
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open P5J

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

/-- **The clause `width` of `PlainAt`**, in scope, at a description that `LaidAt` ties to Z. -/
theorem width_atFiles (scope : InScope Z = true) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∀ d ∈ (descZ Zp Np cF).roundsDeclaredByBlocks.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.2,
      ∀ t ∈ d.stored, t.sh.W = 2 ^ frS.P.v :=
  AtPublicFiles.Written.width_decl L.data
    ((LPFD.Full.laidPOf_written scope L.laidPOf).symm ▸ AtPublicFiles.Written.width_writtenP)

/-- **The description's first test accepts one written instance**, in scope, at a description that
`LaidAt` ties to Z, where the public clause item holds. The instance is the makers' own default. -/
theorem start_of_item (scope : InScope Z = true) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (item : ∀ req : ByteArray, req.size = 4 * (Zp.p.X.T + 2) →
      ∃ it, Fmt.requestItem OnBytes.secondHashFunction Zp.pol Zp.KL req = some it ∧
        OnBytes.Model.Verify.statementHeld Zp.p.X it = .ok ()) :
    ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true :=
  ⟨(dataAtFiles flashProveData Z).G.z₀, AtPublicFiles.Start.okStart_of_item scope L item _⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Written.widthFit
#print axioms AtPublicFiles.Written.widthFit_proofFull
#print axioms AtPublicFiles.Written.width_writtenP
#print axioms AtPublicFiles.Written.width_decl
#print axioms AtPublicFiles.AtFiles.width_atFiles
#print axioms AtPublicFiles.AtFiles.start_of_item
