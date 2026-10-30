-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/ProofFile.lean: the premises on the proof file, as one structure, and a
theorem that they imply `ProofSound` (Johnson/Goal/Conditions/RowsAtTheRecord.lean). What they imply
is proved at a Z in scope whose files are read: `proofSoundAt_of_verify` (SoundOfVerifyMore.lean).

The prover writes three files: a key file, an entry file and a proof file. `ProofSound` is a
hypothesis on the proof file. From it and one hypothesis on each of the other two files,
Johnson/Goal/TopOfThree.lean derives `NearestSound` (Ladder/Package.lean) for the description
`VerifierAndGoals.theDescription`. None of the three is proved in this file: see TopOfThree.lean, (1).

The theorem used here is `proofSound_plainJB` (Johnson/Desc/Plain/BothAtDesc.lean). It reads the
proof file's protocol as three chains of rounds. The middle chain is shared by the requests of a
batch. Its errors have two parts: one depends on the key alone and is counted once for a batch, the
other is counted once for each request.
  `ProofLetters r b G`: the free variables of that theorem that are not fixed here: a witness; a
    `PlainFile` over the chains G (conditions on₀ on₁ on₂, claims L₁ L₂, a relation M, three
    reductions, three lists of errors); a type of keys; the key of the first chain's output; and
    that key as a function of the record `rec` and the stored table. All seven fields use the same
    choice.
  `RowsOfProofFile D L εs`: the premises of that theorem other than four equations, as seven
    fields, at a compiled description D.
  `proofSound_of_rows`: the seven fields and the four equations (on the input, the chains and the
    bound) give `CompilerSoundnessConditionStatements.proofSound`.
  `batch_is`, `no_late_part`, `shared_mark`: three of the four equations, for `theDescription`. The
    fourth is `eps_the` (RowsAtTheRecord.lean).
  `ProofFileAt Z`: there are a description FP of the proof file, a map instP of instances and a
    choice of the free variables such that `theProofRun (asDescriptionFiles Z)` is the run of FP pulled back
    along instP, and the seven fields hold at that run, at the chains and data of
    `dataAtFiles flashProveData Z`, with εs = 1 / 2^128.
  `proofSound_of_proofFileAt`: `ProofFileAt Z` at every Z in scope at which `protocolDataWellFormed` says yes
    gives `ProofSound`.

Limits. This file only combines statements. It proves none of the seven fields, so by itself it does
not show that the proof file's protocol is sound: `P5J.seven_of_owedF` (Johnson/P5J/TowerEnd.lean)
has the seven from named premises. No example is given here in which they hold together. That the
equation in `ProofFileAt` holds is not shown here; where it fails the last theorem says nothing.

In `ProofFileAt` the seven fields read FP through its
run alone: nothing here says that the `PlainFile` is made of FP's own chains, or that FP's data are
those of `dataAtFiles flashProveData Z`; whoever proves `yes_gives_the_chains` has to show that. The bound
1 / 2^128 is a bound on each round's error, counting the bits that the round's proof of work
(grinding) adds.

-/
import Johnson.Goal.Conditions.RowsAtTheRecord
import Johnson.Goal.Conditions.GatesAtThe
import Johnson.Desc.Block
import Johnson.Desc.Plain.BothAtDesc
import Johnson.Flat.ProofOfRowProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc
open _root_.Run (ckP)
open TypedOracleCompiler.Joined _root_.Iop
open _root_.Compile.Joined (Chains Desc)

/-! ## The premises as one structure, at any input of the compiler -/

/-- The free variables of `proofSound_plainJB` that are not fixed here. -/
structure ProofLetters (r : InnerCompilerInput) (b : SoundnessAnalysisData r) (G : Chains) where
  w₀ : b.Wn
  P : PlainFile G ((r.Instance × r.protocol.Rec) × (oneExternalString r.protocol.wordLength r.protocol.Symbol).Str)
  κ₁ : Type
  k₁ : P.A₁ → κ₁
  F₁ : r.protocol.Rec → (oneExternalString r.protocol.wordLength r.protocol.Symbol).Str → κ₁

/-- The premises of `proofSound_plainJB` other than four equations, as seven fields. -/
structure RowsOfProofFile {r : InnerCompilerInput} {b : SoundnessAnalysisData r} {G : Chains}
    (D : Desc G (r.Instance × r.protocol.Rec) (oneExternalString r.protocol.wordLength r.protocol.Symbol)) (L : ProofLetters r b G) (εs : ℝ≥0∞) :
    Prop where
  /-- The first chain takes on₀ to on₁, and L₁ of its output implies M, with errors ε₁ (`Leads`). -/
  first_chain_knows_means :
    L.P.K₁.Leads L.P.on₀ (fun a c => L.P.on₁ c ∧ (L.P.L₁ c → L.P.M a c)) L.P.ε₁
  /-- The shared chain takes on₁ to on₂, and L₂ of its output implies L₁ of its input (`LeadsBN`).
  ε₂ covers the error that depends on the key once, and one request's error maxBatchSize times. -/
  shared_joint_count :
    L.P.K₂.LeadsBN L.k₁ L.P.on₁ (fun c d => L.P.on₂ d ∧ (L.P.L₂ d → L.P.L₁ c)) r.protocol.maxBatchSize L.P.ε₂
  /-- The last chain takes on₂ to L₂ of its input, with errors ε₃ (`Leads`). -/
  leads3_last_chains_table : L.P.K₃.Leads L.P.on₂ (fun d _ => L.P.L₂ d) L.P.ε₃
  /-- The key of the first chain's output is a function of `rec` and the stored table y alone. -/
  shared_start_is_the_records :
    ∀ x rec y τ c, L.P.out₁ ((x, rec), y) τ = some c → L.k₁ c = L.F₁ rec y
  /-- Where D accepts, the three chains in a row give an output, at the instance `early x`. -/
  yes_gives_the_chains : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
    (L.P.links.all.out ((r.protocol.early x, rec), y) τ).isSome = true
  /-- Where D accepts and the first chain's output at `early x` is c: if on₀ implies M at c, the
  relation `relB` holds. -/
  tie : ∀ x rec y (τ : Tr G.sh) c, D.accept (x, rec) y τ = true →
    L.P.out₁ ((r.protocol.early x, rec), y) (Tr.fst (s := G.c₁) (t := G.c₂ ++ G.c₃) τ) = some c →
    (L.P.on₀ ((r.protocol.early x, rec), y) → L.P.M ((r.protocol.early x, rec), y) c) →
    r.protocol.relB b.Rno rec x y L.w₀
  /-- The largest error in the three lists (`worstMid`) is at most εs. -/
  proof_below : L.P.links.worstMid ≤ εs

/-- **The seven fields and four equations give `CompilerSoundnessConditionStatements.proofSound b`.** -/
theorem proofSound_of_rows {r : InnerCompilerInput} {b : SoundnessAnalysisData r} {G : Chains}
    (D : Desc G (r.Instance × r.protocol.Rec) (oneExternalString r.protocol.wordLength r.protocol.Symbol)) (hB : r.protocol.onlineBatch = D.batch)
    (hl : r.protocol.late = none) (hJ : G.aJ = RAnn.ofShared .sh G.rJ) (L : ProofLetters r b G)
    (εs : ℝ≥0∞) (hε : b.εs = εs) (R : RowsOfProofFile D L εs) : CompilerSoundnessConditionStatements.proofSound b :=
  proofSound_plainJB r.protocol D hB b.Rno L.w₀ L.P (κ₂ := Unit) (k₂ := fun _ => ()) hl
    ⟨R.first_chain_knows_means, R.shared_joint_count, R.leads3_last_chains_table⟩ hJ L.F₁
    R.shared_start_is_the_records (fun _ _ => ()) (fun _ _ _ _ => rfl) R.yes_gives_the_chains
    R.tie (hε.symm ▸ R.proof_below)

/-! ## At `VerifierAndGoals.theDescription` -/

/-- The compiler's input from which `theDescription` is made at the public files Z. -/
abbrev rZ (Z : PublicFiles) : InnerCompilerInput := innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)

/-- Other data that `CompilerSoundnessConditionStatements.proofSound` reads, among them the bound εs. -/
abbrev bZ (Z : PublicFiles) : SoundnessAnalysisData (rZ Z) := soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)

/-- The proof file's three chains at the data of `dataAtFiles flashProveData Z`. -/
abbrev chainsP (Z : PublicFiles) : Chains :=
  chainsOf (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
    (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty

/-- The compiled description of the proof file at these data, with the decision `run`. -/
abbrev descPr (Z : PublicFiles)
    (run : LPFD.Full.XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) :
    Desc (chainsP Z) ((rZ Z).Instance × (rZ Z).protocol.Rec) (oneExternalString (rZ Z).protocol.wordLength (rZ Z).protocol.Symbol) :=
  wholeDesc (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
    (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty silP run

/-- The input's batch is that description's, at the decision `(dataAtFiles flashProveData Z).runP`. -/
theorem batch_is (Z : PublicFiles) : (rZ Z).protocol.onlineBatch = (descPr Z (dataAtFiles flashProveData Z).runP).batch := by
  exact rfl

/-- At that input an instance has no late part. -/
theorem no_late_part (Z : PublicFiles) : (rZ Z).protocol.late = none := by exact rfl

/-- The round that joins the first two chains is marked as shared. -/
theorem shared_mark (Z : PublicFiles) : (chainsP Z).aJ = RAnn.ofShared .sh (chainsP Z).rJ := by
  exact rfl

/-- The seven fields at `descPr Z run`, where `run` is `(dataAtFiles flashProveData Z).runP`, give
`CompilerSoundnessConditionStatements.proofSound (bZ Z)`. -/
theorem proofSound_record_of_rows (Z : PublicFiles)
    (run : LPFD.Full.XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (e : (dataAtFiles flashProveData Z).runP = run) (L : ProofLetters (rZ Z) (bZ Z) (chainsP Z))
    (R : RowsOfProofFile (descPr Z run) L ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    CompilerSoundnessConditionStatements.proofSound (bZ Z) := by
  subst e
  exact proofSound_of_rows (descPr Z (dataAtFiles flashProveData Z).runP) (batch_is Z) (no_late_part Z)
    (shared_mark Z) L _ (eps_the Z) R

/-- **The open premises for the proof file at one set of public files Z.** -/
def ProofFileAt (Z : PublicFiles) : Prop :=
  ∃ (XiP : Type) (FP : FileDescription XiP) (instP : LPFD.Full.XF × RecFull → XiP)
    (L : ProofLetters (rZ Z) (bZ Z) (chainsP Z)),
    theProofRun (asDescriptionFiles Z) = (FP.pull instP).run ∧
      RowsOfProofFile (descPr Z (FP.pull instP).run) L ((2 : ℝ≥0∞)⁻¹ ^ 128)

/-- **`ProofFileAt Z` at every Z in scope at which `protocolDataWellFormed` says yes gives `ProofSound`.** -/
theorem proofSound_of_proofFileAt
    (proof_file : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ProofFileAt Z) :
    ProofSound :=
  fun Z hs hl => by
    obtain ⟨XiP, FP, instP, L, hseat, R⟩ := proof_file Z hs hl
    refine proofSound_record_of_rows Z _ ?_ L R
    rw [runP_the_at Z _ hseat, hl]
    rfl

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.proofSound_of_rows
#print axioms VerifierAndGoals.AtTheName.batch_is
#print axioms VerifierAndGoals.AtTheName.no_late_part
#print axioms VerifierAndGoals.AtTheName.shared_mark
#print axioms VerifierAndGoals.AtTheName.proofSound_record_of_rows
#print axioms VerifierAndGoals.AtTheName.proofSound_of_proofFileAt
