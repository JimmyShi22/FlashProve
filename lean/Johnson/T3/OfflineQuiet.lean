-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OfflineQuiet.lean: THE OFFLINE PROVER HAS NO SECOND STOP: no part of its first or last chain has
one that fires, at any parts and any description. Each part's second stop is none by its text: the
sendings, the lookups, the batching and the proximity tests write it so. No premise on the senders: the
fields of KeyParts left free are public data and readers, and no half takes its stop from them.
This file proves neither completeness nor zero knowledge of a protocol: it is about the second stops of the
offline prover.
-/
import Johnson.T3.OfflineAtTheTerm
import E2E.KeyNoStop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Stops
open ProofFile.Honest
open AtPublicFiles.KeyFile (KeyParts keyProver)

section Halves
variable {V W X : Type}

/-- The second stop of a part of the proximity test says nothing. -/
theorem testHalf_quiet (J : K12.TestJob W X) :
    ∀ p ∈ (K12.proverSideOfProximityTest J : Placed V W X).parts, ∀ u l o, p.hid u l o = none := by
  intro p hp u l o
  simp only [K12.proverSideOfProximityTest, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · unfold K12.firstPart
    cases J.fresh <;> rfl
  · rfl

/-- A guard on the field leaves the second stop as it is. -/
theorem needsField_quiet (h : Placed V W X)
    (q : ∀ p ∈ h.parts, ∀ u l o, p.hid u l o = none) :
    ∀ p ∈ h.needsField.parts, ∀ u l o, p.hid u l o = none := by
  intro p hp u l o
  obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
  exact q p' hp' u l o

/-- A sending. -/
theorem sendHalf_quiet (J : K1.SendJob W X) :
    ∀ p ∈ (K1.proverSideOfSending J : Placed V W X).parts, ∀ u l o, p.hid u l o = none := by
  intro p hp u l o
  obtain rfl := List.mem_singleton.1 hp
  rfl

end Halves

section Look
variable {V₁ W₁ X₁ Wk : Type}

/-- A lookup's row. -/
theorem lookSeat_quiet (R : K3.Reads) (J : K3.LookJobs Wk) (wit : W₁ → Wk) (a : K3.At) :
    ∀ p ∈ (K3.proverSideOfLookupInChainAtOneOwner R J wit a : Placed V₁ W₁ X₁).parts, ∀ u l o, p.hid u l o = none := by
  intro p hp u l o
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hq
  show (K3.partOf (V := Unit) R J a x.1 x.2).hid () l o = none
  unfold K3.partOf
  split <;> rfl

end Look

section Batch
variable {W₀ Rc Xi Tr X : Type}

/-- The batching's row. -/
theorem k13Half_quiet (weights : W₀ → Weights) (pile : K13.PileOf Xi)
    (p : VerifiableInference.Desc.K13.Where) :
    ∀ q ∈ (K13.proverSideOfClaimCombination weights pile p : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).parts,
      ∀ u l o, q.hid u l o = none := by
  intro q hq u l o
  simp only [K13.proverSideOfClaimCombination, K13.k13Row, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> rfl

end Batch

variable {W₀ Rc X₀ X Wk : Type}

/-- **Where the two proximity tests left free have no second stop, the prover has none.** -/
theorem keyProver_quiet (K : KeyParts W₀ Rc X₀ X Wk)
    (hr : ∀ p ∈ K.rng.parts, ∀ u l o, p.hid u l o = none)
    (ho : ∀ p ∈ K.own.parts, ∀ u l o, p.hid u l o = none) : NoSecondStop (keyProver K) := by
  refine ⟨fun h hh => ?_, fun h hh => ?_⟩
  · simp only [keyProver, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sendHalf_quiet _
    · exact sendHalf_quiet _
    · exact fun p hp u l o => (quietHalf_lookOwned _ _ _ _ _ p hp).2 u l o
    · exact fun p hp u l o => (quietHalf_lookOwned _ _ _ _ _ p hp).2 u l o
    · exact hr
    · exact k13Half_quiet _ _ _
    · exact sendHalf_quiet _
  · obtain rfl := List.mem_singleton.1 hh
    exact ho

end AtPublicFiles.Stops

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed
open AtPublicFiles.Stops AtPublicFiles.AtFiles.HonestTerm ProofFile.Honest
open P5J

local instance (priority := high) offlineQuietPad : Nonempty PadZ := pads_nonempty OnBytes.Slice.frS 402653181
local instance (priority := high) offlineQuietValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) offlineQuietDefault : Inhabited RunValue := ⟨fun _ => 0⟩

/-- **The premise quiet: the offline prover has no second stop**, at any parts and description. -/
theorem quiet_parts {files : VerifierAndGoals.PublicFiles} (parts : Parts files) (d : OfflineDescription) :
    NoSecondStop (parts.prover d) :=
  keyProver_quiet _ (testHalf_quiet _)
    (needsField_quiet (K12.proverSideOfProximityTest _) (testHalf_quiet _))

attribute [-instance] Inst.Model.Scl.ref

/-- **The three offline clauses of the zero-knowledge statement, without the premise quiet.** -/
theorem offlineClauses_quiet {files : VerifierAndGoals.PublicFiles} {d : OfflineDescription}
    (h : offlineDescription files = .ok d) (parts : Parts files)
    (scope : VerifierAndGoals.InScope files = true) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (named : AtPublicFiles.AtFiles.KeyNamed files d.source d.numbers d.later)
    (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
      ((Cz files).Pad × (Cz files).Rnd) OnBytes.TableKey Unit parts.SharedState
      parts.OwnState)
    (isProver : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
    (x₀ : LPFD.Full.XF)
    (owed : Owed (keyFileDescription d.source d.numbers d.later) parts.book
      ((cmKey files).proverAt 0 (parts.prover d)) GK.mute
      (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
    (owns : GK.owns = true) :
    (∀ i r e, (offlineProver parts).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r) ∧
      ExactOutsideStops (offlineProver parts)
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y)
        (workAtFiles files).offline.cleared (offlineSimulatorAt d parts GK) ∧
      PrivateStopsAtMost (offlineProver parts)
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline 0 :=
  offlineClauses h parts scope live named GK isProver x₀ owed owns (quiet_parts parts d)

/-- **What IsProvK leaves free at the parts**: the senders store the table, at table 0 alone. -/
def SendersStoreTheTable {files : VerifierAndGoals.PublicFiles} (parts : Parts files) : Prop :=
  ∀ w rc it x, parts.senders.stored w rc it x = if it == 0 then (cmKey files).enc w rc x else none

/-- The key that the prover hands on is the committer's. -/
theorem key_parts {files : VerifierAndGoals.PublicFiles} (parts : Parts files) (d : OfflineDescription) :
    (parts.prover d).key = (cmKey files).key := rfl

/-- The table that the prover reads is the committer's, where the senders store it. -/
theorem stored_parts {files : VerifierAndGoals.PublicFiles} (parts : Parts files) (d : OfflineDescription)
    (h : SendersStoreTheTable parts) (w rc it x) :
    (parts.prover d).stored w rc it x = if it == 0 then (cmKey files).enc w rc x else none :=
  h w rc it x

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.key_parts
#print axioms VerifiableInference.Compilation.stored_parts
#print axioms VerifiableInference.Compilation.offlineClauses_quiet
#print axioms AtPublicFiles.Stops.testHalf_quiet
#print axioms AtPublicFiles.Stops.keyProver_quiet
#print axioms VerifiableInference.Compilation.quiet_parts
