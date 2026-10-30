-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OfflineAtTheTerm.lean: the offline clauses of the zero-knowledge statement (ZeroKnowledgeOnServedRequests) at the protocol's own offline prover (E2E/TheHonestProver.lean).

1.  Where the public files make a description, offlineProver is offlineProverWithEncodedTable at the prover of the value Parts.
2.  offlineClauses: its table is the object's, and its exact line and its private stops hold, from Owed at the key file's rows, that the
    rows are the prover's, the key's names and no second stop. Its simulator is simKey at the rows' simulators.
3.  zeroKnowledgeOnServedRequests_atTheRows: so the statement at the protocol's honest provers asks of the offline prover these alone;
    the error of the offline and the link proof is 0 there.
4.  No value of any premise is given here. This file proves zero knowledge of nothing: no member of Owed at the key file is given here.
-/
import Johnson.T3.OfflineAtFiles
import Johnson.T3.OnlineAtTheTerm

set_option autoImplicit false
set_option maxRecDepth 20000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Sides Owed relAt)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open P5J

local instance (priority := high) offlineAtTheTermInstance1 : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) offlineAtTheTermInstance2 : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) offlineAtTheTermInstance3 : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles}

/-- Where the public files make a description, the offline prover is the shell at the prover of the parts. -/
theorem offlineProver_of_description {d : OfflineDescription} (h : offlineDescription files = .ok d)
    (parts : Parts files) :
    offlineProver parts = offlineProverWithEncodedTable files (keyFileDescription d.source d.numbers d.later) parts.book (parts.prover d)
      runValueBytes runValueBytes (offlineStart d) := by
  unfold offlineProver
  rw [h]

/-- **The offline simulator**, made of the description, the book, the rows' simulators and the public stops. -/
abbrev offlineSimulatorAt (d : OfflineDescription) (parts : Parts files)
    (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
      ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState) :=
  simKey files (keyFileDescription d.source d.numbers d.later) parts.book runValueBytes runValueBytes (offlineStart d)
    GK (parts.prover d) GK.sims

/-- **The three offline clauses at the protocol's offline prover.** -/
theorem offlineClauses {d : OfflineDescription} (h : offlineDescription files = .ok d) (parts : Parts files)
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (named : KeyNamed files d.source d.numbers d.later)
    (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
      ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
    (isProver : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
    (x₀ : XF)
    (owed : Owed (keyFileDescription d.source d.numbers d.later) parts.book ((cmKey files).proverAt 0 (parts.prover d))
      GK.mute (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
    (owns : GK.owns = true) (quiet : AtPublicFiles.Stops.NoSecondStop (parts.prover d)) :
    (∀ i r e, (offlineProver parts).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
      ExactOutsideStops (offlineProver parts) (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
        (workAtFiles files).offline.cleared (offlineSimulatorAt d parts GK) ∧
      PrivateStopsAtMost (offlineProver parts) (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
        (workAtFiles files).offline 0 := by
  have paid := key_paid files d.source d.numbers d.later scope live named
  rw [offlineProver_of_description h]
  exact ⟨fun _ _ _ => rfl,
    exactOutsideStops_of_keyOneExact _
      (oneExact_keyZ_at files (keyFileDescription d.source d.numbers d.later) parts.book runValueBytes runValueBytes
        (offlineStart d) GK (parts.prover d) isProver (fun i _ => inRange i) x₀ paid.1 paid.2.1 paid.2.2.1
        paid.2.2.2 owed owns)
      (validTied_key files x₀ fun _ h => h) _,
    offline_stops_of_quiet files runValueBytes runValueBytes (parts.prover d) _ (offlineStart d) quiet _ _⟩

/-- **The zero-knowledge statement at the protocol's honest provers, the offline clauses at the rows.** Of the offline prover it asks Owed at the key file and the
rows' four side conditions; the link adds no error. -/
theorem zeroKnowledgeOnServedRequests_atTheRows {zHid : ℝ≥0∞}
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : VerifierAndGoals.readFiles files = .ok pp) {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place} {A : ProofFile.Honest.Term.OnlineReturn files} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
    {G : Sides A.F A.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey ProofFile.Honest.Cells Unit Unit}
    {more : List (String × Bool)}
    (hd : ProofFile.Honest.AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x (ProofFile.Honest.Term.onlineFilling files) A G
      (t3Asks files A ++ more))
    (debts : RowDebtsP A G ((cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 A.H)
      (relAt (ansAt (AZ files) PadZ (holdZ files)) (ServedRequest FlashProve.committerCoinCountLessOne files hr) LPFD.Full.instanceAsPlainRecord))
    (owns : G.owns = true)
    (hid : HidSmall (onlineProver files)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles files).validB (ServedRequest FlashProve.committerCoinCountLessOne files hr) w a) zHid)
    (faithful : (workAtFiles files).Faithful) (two : TwoIndicesServeOneRequest files hr)
    {d : OfflineDescription} (hdesc : offlineDescription files = .ok d) (parts : Parts files)
    (named : KeyNamed files d.source d.numbers d.later)
    (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
      ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
    (isProver : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
    (x₀ : XF)
    (owedKey : Owed (keyFileDescription d.source d.numbers d.later) parts.book ((cmKey files).proverAt 0 (parts.prover d))
      GK.mute (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
    (ownsKey : GK.owns = true) (quiet : AtPublicFiles.Stops.NoSecondStop (parts.prover d)) :
    ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) 0 0 zHid :=
  have c := offlineClauses hdesc parts scope live named GK isProver x₀ owedKey ownsKey quiet
  zeroKnowledgeOnServedRequests_atTheProvers files scope live hr hd debts owns hid faithful two parts
    _ c.1 c.2.1 c.2.2

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.offlineProver_of_description
#print axioms VerifiableInference.Compilation.offlineClauses
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_atTheRows
