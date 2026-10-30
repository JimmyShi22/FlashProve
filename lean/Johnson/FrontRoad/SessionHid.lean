-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SessionHid.lean: what the private part of the sessions' abort set is, at the
family famG (E2E/BridgeJoinAtFiles.lean), by definition. Four equations and one equivalence.
Terms of this folder: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  hid_famG_eq   at every number n of a copy, the set Hid of famG at a private input w and an
      instance a is the set Hid of the one-request honest prover (.one) of the structure honestBatchProverOfFile
      (Johnson/Desc/ProofFile/Honest/StratC.lean), at the prover provG, at w and at the instance
      that LPFD.Full.instanceAsPlainRecord builds from a.
  mem_hid_famG   a list ρ of verifier messages lies in that set if and only if the test hidB
      (Johnson/Desc/ProofFile/Honest/Record.lean) returns true at the index, the committer's
      randomness, that instance, and the first and the second chain's challenges of ρ.
  trace_provG   the trace function of provG is that of H: substituting the rows G, and the
      committer's stored table and key, does not change it (Johnson/Desc/ProofFile/Honest/Rule.lean,
      CommitterAt.lean).
  first_provG, second_provG   the first and the second chain's halves of provG are the rows of G of
      that chain, each at its place, with each part's simulator dropped.

How it fits. The condition sessionStops of PremWDebts (E2E/BridgeDebts.lean) bounds the measure of
that set. These are the steps by definition between that condition and lemmas on honestBatchProverOfFile's set.
Lemmas toward the condition HidSmall (E2E/BridgePrivacy.lean); not one of the release's goal
statements.

Limits.
  They say what a set is, not how large it is. No probability is named. Nothing is said on hiding,
      completeness or soundness.
  G (the rows), H (the prover of parts) and B (the library's ProverCoinCounts) are variables. hidB reads
      whatever trace H.trace returns; nothing here asks which. Where H.trace returns none hidB is
      false, so the set is empty there.
-/
import E2E.BridgeJoinAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open _root_.Run (ckP)
open ProofFile.Honest (Prover ProverCoinCounts Sides honestBatchProverOfFile hidB drawsLo)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_sessionHid : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_sessionHid {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- The private part of the abort set of famG at the copy's number n is that of the one-request
honest prover (.one) of honestBatchProverOfFile at the prover provG, at the instance that LPFD.Full.instanceAsPlainRecord builds.
-/
theorem hid_famG_eq (n : ℕ) (w) (a) :
    ((famG Z Zp Np cF run₂ run₃ B G H).at n).Hid w a =
      (honestBatchProverOfFile (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃ n) (shAt Zp Np cF) (extZ Z)).one.Hid w
        (LPFD.Full.instanceAsPlainRecord a) := rfl

/-- A list of verifier messages lies in that set if and only if the test hidB returns true at the
index, the committer's randomness, the instance that LPFD.Full.instanceAsPlainRecord builds, and the first and the
second chain's challenges. -/
theorem mem_hid_famG (n : ℕ) (w) (a) (ρ) :
    ρ ∈ ((famG Z Zp Np cF run₂ run₃ B G H).at n).Hid w a ↔
      hidB (descZ Zp Np cF) (provG Z Zp Np cF B G H) w.1 w.2.1 (LPFD.Full.instanceAsPlainRecord a)
        (drawsLo (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
          (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (Iop.Rho.lo _ ρ)) = true := Iff.rfl

/-- The trace function of provG is that of H. -/
theorem trace_provG : (provG Z Zp Np cF B G H).trace = H.trace := rfl

/-- The first chain's halves of provG are the first chain's rows of G, each at its place, with each
part's simulator dropped. -/
theorem first_provG :
    (provG Z Zp Np cF B G H).first = G.first.map fun L => ⟨L.place, L.row.map (·.1)⟩ := rfl

/-- The second chain's halves of provG are the second chain's rows of G, each at its place, with
each part's simulator dropped. -/
theorem second_provG :
    (provG Z Zp Np cF B G H).second = G.second.map fun L => ⟨L.place, L.row.map (·.1)⟩ := rfl

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_sessionHid
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_sessionHid
#print axioms OnBytes.FrontRoad.hid_famG_eq
#print axioms OnBytes.FrontRoad.mem_hid_famG
#print axioms OnBytes.FrontRoad.trace_provG
#print axioms OnBytes.FrontRoad.first_provG
#print axioms OnBytes.FrontRoad.second_provG
