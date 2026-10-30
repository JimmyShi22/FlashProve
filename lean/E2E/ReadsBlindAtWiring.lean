-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ReadsBlindAtWiring.lean: the three clauses of E2E/ReadsBlind.lean at the wiring of the three
files' protocols of the full size (`wireOfFullD`, Johnson/Flat/Dec/WiresAtSizes.lean), from which
the verifier is compiled. One statement and its proof.

What is shown.
  **`blind_wireOfFullD`**: at ANY claims, honest side, rounds' data DK, DP, ds, openings xs, three
    decisions, provers, number K of hash outputs for a verifier's message and depth of the key
    file's request tree: each of the wiring's three parts (the key file's, the copy's file's, the
    proof file's) has `BlindToWork` with its protocol: which positions the verifier reads is the
    same with all proof-of-work test bits set to 0, and hangs on no plain part of a prover's
    message. (The wiring is typed over a carrier that holds the three protocols' shapes and marks
    alone, Johnson/TypedOracleCompiler/RecCompile/Carrier.lean; the protocols are the object's own, with the marks
    of the wiring: `batTC`, `batLC` there.)

Limits. Those of E2E/ReadsBlind.lean. The statement is about the verifier's side alone, and it holds
at every data: no public file, no scope and no gate occurs in it. Nothing on hiding follows from
this file alone.


-/
import E2E.ReadsBlind
import Johnson.Flat.Dec.WiresAtSizes

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Reads
open OnBytes.Flat (RecFull)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP chalP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize wireOfFullD)
open TypedOracleCompiler.Compile.Batch.Cms (batTC batLC)

/-- **The three clauses at the wiring of the full size's three protocols.** -/
theorem blind_wireOfFullD {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
    (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
    (runK : RecFull → View → View → View → Bool)
    (runP : X × RecFull → View → View → View → Bool) (ds : List TypedOracleCompiler.Run.PQ.RD)
    (xs : List XO) (dec : RecFull × RecFull → View → Bool) (rK rP : RecFull)
    (depthReq : ℕ) (early : X → X) (salt : ℕ)
    (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
    (K depthReqT : ℕ) :
    BlindToWork
        (batTC ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P)
          (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annT)
        (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT).T.sh ∧
      BlindToWork
        (batLC ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P)
          (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annL)
        (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT).Lk.sh ∧
      BlindToWork ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).onlineBatch
        (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT).B.sh :=
  have hK := whole_blind (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
    (OnBytes.Flat.join₀ rK) ByteArray.empty OnBytes.Flat.silK runK
  have hL := linkW_blind (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec
    (TypedOracleCompiler.Run.PQ.wire0S (ckP .two) K (chalP .two K))
  have hP := whole_blind (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
    (OnBytes.Flat.join₀ rP) ByteArray.empty OnBytes.Flat.silP runP
  ⟨hK, hL, hP⟩

end AtPublicFiles.Reads

#print axioms AtPublicFiles.Reads.blind_wireOfFullD
