-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/TheSeam.lean: where completeness and zero knowledge as interactive oracle proofs, stated at the protocol of the
public files, meet the premises of the road to the final statement, stated at the verifier's input and at each reading.

1.  The protocol of the public files is the verifier's object; its work bits and its test on the copy's number do not move with the
    two public readings.
2.  Completeness at Hs passes to Hs made to refuse what is not served: on served instances nothing turns (completeInParts_refuse_iff).
3.  So the two statements at the protocol give the road's two premises on the provers, at one value of the provers.
Both statements are premises here: this file proves neither completeness nor zero knowledge of the protocol.
-/
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocol
import VerifiableInference.Final.RefuseUnserved
import Johnson.FrontRoad.AtBuiltNamed

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation.Seam
open Iop AtPublicFiles.AtFiles Prob
open VerifierAndGoals (PublicFiles readFiles)
open FlashProve (committerCoinCountLessOne flashProveDescription allZeroDigest flashProveData)
open OnBytes.FrontRoad (layoutsOfBuiltDescription)
open LPFD.Full (XF)

/-- The verifier's input at the reference readings; the family over the two readings. -/
abbrev inputAt (files : PublicFiles) : VerifiableInference.OnPublicFiles.InnerCompilerInput := flashProveDescription.input files allZeroDigest []
abbrev familyAt (files : PublicFiles) := layoutsOfBuiltDescription flashProveData allZeroDigest [] files
/-- The wiring at a reading. -/
abbrev wiringAt (files : PublicFiles) (reading : (familyAt files).D) :
    HashLayout ((flashProveDescription.F files).withProvers (flashProveDescription.P files)) (flashProveDescription.F files).annT (flashProveDescription.F files).annL :=
  { (layoutOf flashProveDescription files allZeroDigest []).toHashLayout with
    seedQueries := (familyAt files).Sd reading
    answerCode := (familyAt files).cA reading }

/-- The served requests, at the types of the object: the two inputs' types are one, and here Lean need not find that out. -/
def servedAt (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) : FullSizeMatrix → XF → Prop :=
  ServedRequest committerCoinCountLessOne Z hr

/-- (1) The protocol of the public files is the object of the verifier's input. -/
theorem protocol_eq (Z : PublicFiles) : protocolAtFiles Z = (inputAt Z).protocol := rfl

/-- (2) The work bits do not move with the readings. -/
theorem work_eq (Z : PublicFiles) (reading : (familyAt Z).D) : (wiringAt Z reading).work = workAtFiles Z := rfl

/-- (2') Nor at the wiring of the input. -/
theorem work_ofInput_eq (Z : PublicFiles) : ((layoutOf flashProveDescription Z allZeroDigest []).toHashLayout).work = workAtFiles Z := rfl

/-- (3) Nor does the test on the copy's number. -/
theorem num_at_reading (Z : PublicFiles) (reading : (familyAt Z).D) (k : ℕ)
    (π : Plains (inputAt Z).protocol.onlineBatch.loc.shape) :
    ((familyAt Z).Sd reading).num k π = decide (((chainsZ Z).plF π).copy = k) := rfl

theorem num_eq (Z : PublicFiles) (reading : (familyAt Z).D) :
    ((familyAt Z).Sd reading).num = copyNumberAtFiles Z := by
  funext k π
  exact (num_at_reading Z reading k π).trans (num_letters Z allZeroDigest [] k π).symm

/-- (5) **Completeness at the protocol gives the road's premise**, at one value of the provers, at every reading. -/
theorem road_complete (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) (Hs : HonestProvers (protocolAtFiles Z))
    (h : CompleteOnServedRequests Z hr Hs) :
    ∃ offlineError linkError onlineError : ℝ≥0∞,
      offlineError + linkError + onlineError ≤ completenessTarget ∧
      ∀ reading, CompleteInParts (inputAt Z).protocol (proversAtFiles Z hr Hs) (wiringAt Z reading).work
        ((familyAt Z).Sd reading).num (servedAt Z hr) offlineError linkError onlineError := by
  have h' : CompleteIOP (protocolAtFiles Z) Hs (workAtFiles Z) (copyNumberAtFiles Z) (servedAt Z hr)
      completenessTarget := h
  obtain ⟨-, a, b, c, hs, hp⟩ := h'
  have key : CompleteInParts (protocolAtFiles Z) (proversAtFiles Z hr Hs) (workAtFiles Z) (copyNumberAtFiles Z)
      (servedAt Z hr) a b c :=
    (completeInParts_refuse_iff (L := protocolAtFiles Z) (provers := Hs) (workAtFiles Z)
      (copyNumberAtFiles Z) a b c).2 hp
  refine ⟨a, b, c, hs, fun reading => ?_⟩
  rw [num_eq Z reading]
  exact key

/-- (6) **Zero knowledge at the protocol gives the road's premise.** -/
theorem road_zeroKnowledge (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) (Hs : HonestProvers (protocolAtFiles Z))
    (a b c : ℝ≥0∞) (h : ZeroKnowledgeOnServedRequests Z hr Hs a b c) :
    ∃ simulators : RunSimulators (inputAt Z).protocol,
      HonestVerifierZeroKnowledge ((layoutOf flashProveDescription Z allZeroDigest []).toHashLayout).work (proversAtFiles Z hr Hs) simulators
        rangeAtFiles (servedAt Z hr) (budgetAtFiles a b c) :=
  Exists.elim h.simulated fun s hz => Exists.intro s hz.1

end VerifiableInference.Compilation.Seam

#print axioms VerifiableInference.Compilation.Seam.protocol_eq
#print axioms VerifiableInference.Compilation.Seam.work_eq
#print axioms VerifiableInference.Compilation.Seam.work_ofInput_eq
#print axioms VerifiableInference.Compilation.Seam.num_eq
#print axioms VerifiableInference.Compilation.Seam.road_complete
#print axioms VerifiableInference.Compilation.Seam.road_zeroKnowledge
