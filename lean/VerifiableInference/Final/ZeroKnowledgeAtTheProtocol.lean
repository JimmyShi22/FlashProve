-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean: honest-verifier zero knowledge before hashing, with our protocol plugged in.
One statement. This file proves nothing of it. `zkOnServedRequests_inScope`
(AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean) proves it, from three premises on the public files
(InScope; protocolDataWellFormed accepts; readFiles returns), of the honest provers at `thePartsAt`
(E2E/KeyArgumentsAt.lean), which holds named stand-ins, at offline 0, link 0 and online 2^-174; that
file's Limits go with it.

 1. THE PROTOCOL has out-of-domain samples, and its soundness is proved. Every table has an out-of-domain sample, and the
    offline, the link and the online proof each take it in their instance. (These are the committed tables' samples. Samples on
    oracles that a prover sends during a proof are rounds inside the three proofs: this file neither shows nor shuts them out.) In Lean it is protocolAtFiles Z, at public files Z: the same term as
    the object in the input of the soundness theorem's verifier (object_description). Every oracle of its three proofs is blinded
    (allBlinded_atFiles): so a run shows an oracle only where the verifier reads it.
 2. THE PROVERS are an argument, Hs. The statement is meant at the protocol's honest provers: the value honestProvers Z parts of
    E2E/TheHonestProver.lean, whose argument parts holds the offline prover's senders; that value lays fall-back states at named
    places (listed beside it: E2E/TheHonestProverStatements.lean, «The places where a sender falls back on a fixed value»). It is a statement about Hs made to refuse the
    requests that are not served (refuseUnserved). The simulators are bound behind Z and Hs and before every index: they may read the public
    files: what is hidden is the index beyond these, the outputs asked for and the bits.
 3. BESIDE COMPLETENESS (CompleteOnServedRequests): the same protocol, work bits (workAtFiles) and served requests (ServedRequest).
    Completeness is stated of Hs, this of Hs made to refuse; completeness holds of the one exactly if it holds of the other
    (completeOnServedRequests_refuse_iff).
 4. SERVED: the index is that of some weights, the request is well formed, and the model's result on it is the claimed output. It
    depends on the weights. WHERE THE MODEL's RESULT IS NONE no claimed output is served. The statement speaks of such a request
    too: the prover shows nothing, and the simulator is told so.
 5. THE RANGE: the matrices that hold an index; the index of any weights is one. It is wider than completeness's domain: the offline
    and the link prover owe exactness and rare stops at every such matrix, every table randomness and every seed.
 6. NUMBERS WITH A VALUE: 44,040,191 columns of one table may be shown; a run reads 62 (offline), 62 and 62 (link), 64 (online). So one
    commitment bears up to 710,324 further tables; each further table bears one link, to the first table, and up to 688,127 requests;
    no request is served on the first table. That is a premise on the honest committer's course: this file ties it to no committer. These are the tables' budgets alone: after hashing,
    the honest side's budget of hash queries bears fewer tables.
 7. THE THREE NUMBERS are arguments: for each prover, a bound on how often it stops for a private reason. The error for one commitment
    is offlineStops + copies · linkStops + copies · sessionsPerCopy · onlineStops: at the full life of line 6 that is 488,793,123,148
    (2^38.8) times onlineStops; no target is named. The conditional theorem in AtFullSide/T3/TheOneAtTheG.lean
    concludes at offline 0, link 0 and online 2^-174. The offline and the link prover have no private stop. The online number is the
    share of the kind K8, the smallness test (window_at_term); that no other kind has a private stop is no premise of that theorem. At
    the full life of line 6 the error is then below 2^-135. At a number of 1 or more the statement says nothing.
 8. IN IT AND NOT ABOUT HIDING: the work bits are the three verifiers' own (workFaithful_atFiles); each prover speaks of its own tables;
    two indices are in range (twoIndices_atFiles); some request is served (someRequestIsServed_holds); two different indices in range
    serve one and the same request (twoIndicesServeOneRequest). The names in brackets are theorems, the last two for Z in scope.
 9. MEANT AT Z in scope: public files that pass the verifier's first test. Exact match: a served request's claimed output is the
    model's own.
10. This file imports the release's description and carries its imports. No definition of zero knowledge imports this file.
-/
import VerifiableInference.Final.ZeroKnowledgeBeforeHashing
import VerifiableInference.Final.CompilerPublicAtFiles
import E2E.CompleteAsIOPAtFiles
import Johnson.FrontRoad.RangeOf

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles readFiles)
open FlashProve (committerCoinCountLessOne)

/-- **The range**: the matrices that hold an index. -/
abbrev rangeAtFiles : FullSizeMatrix → Prop := VerifiableInference.OnPublicFiles.Flat.InRange

/-- **The provers of which this statement speaks**: Hs, refusing in front of the first round where a request is not served. -/
def proversAtFiles (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) (Hs : HonestProvers (protocolAtFiles Z)) : HonestProvers (protocolAtFiles Z) :=
  Hs.refuseUnserved (ServedRequest committerCoinCountLessOne Z hr)

/-- **Two different indices in range serve one request.** Two indices in range and one served request at one index do not give the online
part its meaning; this does. -/
def TwoIndicesServeOneRequest (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) : Prop :=
  ∃ i i' x, i ≠ i' ∧ rangeAtFiles i ∧ rangeAtFiles i' ∧ ServedRequest committerCoinCountLessOne Z hr i x ∧
    ServedRequest committerCoinCountLessOne Z hr i' x

/-- **THE STATEMENT: the provers Hs are honest-verifier zero knowledge as an interactive oracle proof at Z.** The simulators are bound
first. The second part of «simulated» is the claim to read: all that is seen in the life of one commitment, one offline run, a link to each further table,
sessionsPerCopy requests on each. It follows from the first part (wholeLife_of_wholeView); it stands here by name.
MEANT AT Hs := the honest provers of the protocol (AtPublicFiles.AtFiles.HonestTerm.honestProvers Z parts); «parts», the offline prover's
senders, is an argument of that value, and that value lays fall-back states at named places
(listed beside it: E2E/TheHonestProverStatements.lean, «The places where a sender falls back on a fixed value»).
MEANT AT Z in scope. -/
structure ZeroKnowledgeOnServedRequests (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) (Hs : HonestProvers (protocolAtFiles Z))
    (offlineStops linkStops onlineStops : ℝ≥0∞) : Prop where
  /-- the online part is not idle -/
  someRequestIsServed : ∃ i x, rangeAtFiles i ∧ ServedRequest committerCoinCountLessOne Z hr i x
  /-- and the index is not told by that alone -/
  twoIndicesServeOneRequest : TwoIndicesServeOneRequest Z hr
  simulated : ∃ simulators : RunSimulators (protocolAtFiles Z),
    HonestVerifierZeroKnowledge (workAtFiles Z) (proversAtFiles Z hr Hs) simulators rangeAtFiles
        (ServedRequest committerCoinCountLessOne Z hr) (budgetAtFiles offlineStops linkStops onlineStops) ∧
      ∀ (copyNumber : ℕ → ℕ) (copies sessionsPerCopy : ℕ), copies ≤ 710324 → sessionsPerCopy ≤ 688127 →
        WholeLife (workAtFiles Z) (proversAtFiles Z hr Hs) simulators rangeAtFiles (ServedRequest committerCoinCountLessOne Z hr)
          (budgetAtFiles offlineStops linkStops onlineStops) copyNumber copies sessionsPerCopy

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.proversAtFiles
#print axioms VerifiableInference.Compilation.ZeroKnowledgeOnServedRequests
#print axioms VerifiableInference.Compilation.TwoIndicesServeOneRequest
