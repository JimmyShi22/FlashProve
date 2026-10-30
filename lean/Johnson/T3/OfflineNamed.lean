-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OfflineNamed.lean: the two public premises of the offline clauses of the zero-knowledge statement, as theorems.

1.  Wherever the test on the public files says yes, they make an offline description, and it is the
    one that the verifier's seat makes (key_sourced).
2.  So offlineClauses and zeroKnowledgeOnServedRequests_atTheRows hold without the premises hdesc and named.
3.  This file proves zero knowledge of nothing: no member of Owed at the key file is given here.
-/
import Johnson.T3.OfflineAtTheTerm
import E2E.TheHonestProverStatements

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

local instance (priority := high) offlineNamedInstance1 : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) offlineNamedInstance2 : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) offlineNamedInstance3 : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles}

/-- **The public files make the description that the verifier's seat makes.** -/
theorem offlineDescription_sourced (files : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    ∃ d, offlineDescription files = .ok d ∧ KeySourced files d.source d.numbers d.later := by
  obtain ⟨X, N, P, hs⟩ := key_sourced files live
  obtain ⟨X₀, m, h0, hm, hX, hN, hP⟩ := hs.source
  refine ⟨⟨X, N, P⟩, ?_, hs⟩
  simp only [offlineDescription, h0, hm, hX, hN, hP, bind, Except.bind, pure, Except.pure]

/-- **The proposition OfflineDescriptionNamed.** -/
theorem offlineDescriptionNamed (files : PublicFiles) : OfflineDescriptionNamed files :=
  offlineDescription_sourced files

/-- **The two public premises.** -/
theorem offlineDescription_named (files : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    ∃ d, offlineDescription files = .ok d ∧ KeyNamed files d.source d.numbers d.later :=
  (offlineDescription_sourced files live).imp fun _ h => ⟨h.1, h.2.named⟩

/-- **The three offline clauses, without the public premises**: the description is obtained. -/
theorem offlineClauses_of_live (parts : Parts files) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      ∀ (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
          ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
        (_ : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
        (_ : XF)
        (_ : Owed (keyFileDescription d.source d.numbers d.later) parts.book
          ((cmKey files).proverAt 0 (parts.prover d)) GK.mute
          (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
        (_ : GK.owns = true) (_ : AtPublicFiles.Stops.NoSecondStop (parts.prover d)),
        (∀ i r e, (offlineProver parts).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
          ExactOutsideStops (offlineProver parts)
            (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
            (workAtFiles files).offline.cleared (offlineSimulatorAt d parts GK) ∧
          PrivateStopsAtMost (offlineProver parts)
            (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
            (workAtFiles files).offline 0 := by
  obtain ⟨d, hd, hn⟩ := offlineDescription_named files live
  exact ⟨d, hd, fun GK isProver x₀ owed owns quiet =>
    offlineClauses hd parts scope live hn GK isProver x₀ owed owns quiet⟩

/-- **The zero-knowledge statement at the protocol's honest provers, at the rows, without the public premises.** -/
theorem zeroKnowledgeOnServedRequests_of_live {zHid : ℝ≥0∞}
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
    (parts : Parts files) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      ∀ (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
          ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
        (_ : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
        (_ : XF)
        (_ : Owed (keyFileDescription d.source d.numbers d.later) parts.book
          ((cmKey files).proverAt 0 (parts.prover d)) GK.mute
          (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
        (_ : GK.owns = true) (_ : AtPublicFiles.Stops.NoSecondStop (parts.prover d)),
        ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) 0 0
          zHid := by
  obtain ⟨d, hdesc, hn⟩ := offlineDescription_named files live
  exact ⟨d, hdesc, fun GK isProver x₀ owedKey ownsKey quiet =>
    zeroKnowledgeOnServedRequests_atTheRows scope live hr hd debts owns hid faithful two hdesc parts hn
      GK isProver x₀ owedKey ownsKey quiet⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.offlineDescription_sourced
#print axioms VerifiableInference.Compilation.offlineDescriptionNamed
#print axioms VerifiableInference.Compilation.offlineDescription_named
#print axioms VerifiableInference.Compilation.offlineClauses_of_live
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_of_live
