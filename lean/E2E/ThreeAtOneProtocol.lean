-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ThreeAtOneProtocol.lean: soundness, completeness and honest-verifier zero knowledge as
interactive oracle proofs, of one protocol and one triple of honest provers, tied by the parameters
of one structure. The file states no goal of its own and proves none of the three properties.

Why. The three statements at the public files (`SoundAsIOPAtFiles`, E2E/SoundAsIOPAtFiles.lean;
`CompleteOnServedRequests`, E2E/CompleteAsIOPAtFiles.lean; `ZeroKnowledgeOnServedRequests`,
VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean) are three definitions, each at the public
files `Z`. That they speak of one protocol is seen by unfolding each. Here the protocol is a
parameter that is bound once.

  `ThreeAtOneProtocol L provers work …`: the three library definitions (`IndexKnowledgeSoundIOP`,
      `CompleteIOP`, `HonestVerifierZeroKnowledge`) side by side, at one protocol `L`, one triple of
      provers over `L` and one value of the proof-of-work bits of `L`. General: no public files, no
      description
  `ThreeAtFiles Z hr Hs …`: the structure at the public files: `L := protocolAtFiles Z`
  `threeAtOne_of_statements`: for public files in scope, the three statements at `Z` give it at `L
      := protocolAtFiles Z`
  `statements_of_threeAtOne`: and it gives the three statements at `Z`, for public files in scope,
      given `TwoIndicesServeOneRequest Z hr`
  `protocol_is_the_compiled_verifiers`: the protocol object `protocolAtFiles Z` is the object in the input at
      which `VerifierAndGoals.verify` calls the compiled verifier
  `verifiers_at_every_provers`: the object's three verifiers are `protocolAtFiles Z`'s at every value of the
      object's honest provers
  `work_clears_as_soundness`, `work_passes_as_soundness`: the proof-of-work bits of completeness and
      zero knowledge clear and test as the three clearings and tests of soundness's bound on a
      probability (E2E/SoundAsIOPProbabilityAtFiles.lean)
  `records_are_one`: the two maps by which completeness and zero knowledge read the honest provers'
      record are one
  `served_is_true`: for public files in scope a served request lies in the relation of soundness
  `offline_prover_inside`, `link_prover_inside`: the offline and the link prover inside the triple
      are the honest provers' own
  `offline_prover_at_description`: and the offline one is the key file's prover, at the files' own
      description
  `complete_statement_is_at_the_triple`: the statement `TheProverIsCompleteAsIOP` is completeness at
      that same triple, for public files in scope that pass their own test
  `failure_reads_accept`, `soundness_reads_accept`: what «the offline verifier rejects» means in
      completeness and in soundness: one field, `(protocolAtFiles Z).offline.accept`

What the parameters give. `L` occurs once as a parameter and then in all three fields: no value of
the structure can speak of two protocols. `provers`, `work` and `served` occur once as parameters
and then in two fields, completeness and zero knowledge: these two cannot speak of two triples of
provers, of two values of the work bits or of two relations.

What they do not give. (1) Soundness reads neither `provers` nor `work`. Its tie to the work bits
stands outside the structure, in two theorems at the public files: `work_clears_as_soundness`,
`work_passes_as_soundness`. (2) The relations differ, as in the three statements: soundness stands
at a wider relation, the other two at the served requests; the field `servedIsTrue` says that the
one lies in the other. (3) The numbers stand over different distributions and are not to be
compared: `roundBound` (at the files 2^-128) is a share of all of one round's challenges, the bits
of proof of work among them; `completenessError` is over the provers' coins and the challenges that
pass the proof-of-work tests. (4) Soundness is here in its form in parts: online it speaks of a
batch, where the other two speak of one request; both read the one field `L.onlineBatch`. Its form for one
whole run and its bound on a prover's probability are further theorems on soundness
(E2E/SoundAsIOPAtFiles.lean, E2E/SoundAsIOPProbabilityAtFiles.lean) and no field here. (5) Soundness
reads more of `L` than its three verifiers (the decoder, the collisions, the extractor, the batch's
numbers): none of these reads the object's honest provers; the theorem that carries soundness from
one value of them to another is `soundAsIOPAtFiles_provers` (E2E/SoundAsIOPAtFilesProofs.lean), not
`verifiers_at_every_provers`. (6) The field `zeroKnowledge` is the first part of the field
`simulated` of `ZeroKnowledgeOnServedRequests`. That statement's claim on the whole life of a
commitment and its fields «some request is served» and «two indices serve one request» are not in
the structure. (7) The general structure does not ask that `served` holds of anything: where it
holds of nothing, `complete` says little. (8) Of the online prover inside the triple no theorem here
speaks: `offline_prover_inside` and `link_prover_inside` are of the other two. (9) Nothing in the
structure ties `L.encodeIndex` and `L.recOf`, which completeness and zero knowledge read, to the decoder and
the extractor, which soundness reads: that the extractor returns the honest index from an honest
table stands outside it.

What this file ties is the three statements. It imports no proof of any of them. A value of the
structure at the stops 0, 0, 2^-174, from proofs of the three, under the premise `FilesInUse files
parameters`, is `VerifiableInference.Compilation.threeAtFiles_in_use`
(AtFullSide/Face/TheThreeAtTheFiles.lean).

Limits. No property is proved here: both implications carry the three from one form to the other.
Nothing on the compiled prover and verifier beyond the one equation on the object. Before hashing.
-/
import E2E.SoundAsIOPAtFiles
import E2E.SoundAsIOPProbabilityAtFiles
import E2E.CompleteAsIOPServedLaws
import E2E.CompleteAsIOPAtTheTerm
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocolLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.OneProtocol
open Iop
open VerifiableInference.Compilation
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles readFiles InScope asDescriptionFiles)
open FlashProve (committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.Committed (PadZ pads_nonempty)
open OnBytes.Slice (frS)
open TypedOracleCompiler.Iop (RoundsQueryLayout.pass RoundsQueryLayout.cleared_clearing)
open TypedOracleCompiler.Compile.Batch.Cms (wTC wLC wBC)
open OnBytes.Prover (ThreeProvers)

local instance (priority := high) threeAtOnePads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) threeAtOneRunValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) threeAtOneRunValueInhabited : Inhabited RunValue := ⟨fun _ => 0⟩

/-- **The three properties at one protocol, one triple of provers and one value of the proof-of-work
bits, each bound once.** -/
structure ThreeAtOneProtocol {Index Request : Type} (L : HolographicProtocol Index Request) (provers : HonestProvers L)
    (work : PartsWork L) (copyNumberIn : ℕ → Plains L.onlineBatch.loc.shape → Bool)
    (served wide : Index → Request → Prop) (inRange : Index → Prop)
    (offlineMarks : RoundSplits L.offline.shape) (offlinePlaces : ℕ) (linkMarks : RoundSplits L.link.shape)
    (linkPlaces : ℕ) (roundBound completenessError : ℝ≥0∞) (budget : Budget) : Prop where
  /-- round-by-round knowledge soundness for the index, of L's three verifiers -/
  sound : L.IndexKnowledgeSoundIOP wide offlineMarks offlinePlaces linkMarks linkPlaces roundBound
  /-- completeness of these provers, against L's three verifiers -/
  complete : CompleteIOP L provers work copyNumberIn served completenessError
  /-- honest-verifier zero knowledge of these provers, in runs with L's three verifiers -/
  zeroKnowledge : ∃ simulators : RunSimulators L,
    HonestVerifierZeroKnowledge work provers simulators inRange served budget
  /-- what is served lies in the relation of soundness -/
  servedIsTrue : ∀ index request, served index request → wide index request

variable (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)

/-- The structure at the public files: L := `protocolAtFiles Z`, the provers Hs made to refuse what is not
served. -/
abbrev ThreeAtFiles (Hs : HonestProvers (protocolAtFiles Z)) (offlineStops linkStops onlineStops : ℝ≥0∞) : Prop :=
  ThreeAtOneProtocol (protocolAtFiles Z) (proversAtFiles Z hr Hs) (workAtFiles Z) (copyNumberAtFiles Z)
    (ServedRequest committerCoinCountLessOne Z hr) (relationAtFiles Z) rangeAtFiles (filesAt Z).annT (offlinePlaces Z)
    (filesAt Z).annL 1 ((2 : ℝ≥0∞)⁻¹ ^ 128) completenessTarget
    (budgetAtFiles offlineStops linkStops onlineStops)

variable {Z hr}

/-- **What is served lies in the relation of soundness**, for public files in scope. -/
theorem served_is_true (scope : InScope Z = true) (i : FullSizeMatrix) (x : LPFD.Full.XF)
    (h : ServedRequest committerCoinCountLessOne Z hr i x) : relationAtFiles Z i x :=
  servedRequest_below committerCoinCountLessOne Z scope hr h

/-- **The three statements at the public files give the structure at `protocolAtFiles Z`.** -/
theorem threeAtOne_of_statements {Hs : HonestProvers (protocolAtFiles Z)} {a b c : ℝ≥0∞}
    (sound : SoundAsIOPAtFiles Z (filesAt Z).fixedMessageProvers)
    (complete : CompleteOnServedRequests Z hr (proversAtFiles Z hr Hs))
    (zeroKnowledge : ZeroKnowledgeOnServedRequests Z hr Hs a b c) (scope : InScope Z = true) :
    ThreeAtFiles Z hr Hs a b c where
  sound := sound
  complete := complete
  zeroKnowledge := zeroKnowledge.simulated.elim fun simulators h => ⟨simulators, h.1⟩
  servedIsTrue := served_is_true scope

/-- **And the structure at `protocolAtFiles Z` gives the three statements**, for public files in scope, with the
one field of the statement on zero knowledge that reads no prover as a premise. -/
theorem statements_of_threeAtOne {Hs : HonestProvers (protocolAtFiles Z)} {a b c : ℝ≥0∞} (scope : InScope Z = true)
    (two : TwoIndicesServeOneRequest Z hr) (h : ThreeAtFiles Z hr Hs a b c) :
    SoundAsIOPAtFiles Z (filesAt Z).fixedMessageProvers ∧
      CompleteOnServedRequests Z hr (proversAtFiles Z hr Hs) ∧
      ZeroKnowledgeOnServedRequests Z hr Hs a b c :=
  ⟨h.sound, h.complete,
    h.zeroKnowledge.elim fun simulators hz => zeroKnowledgeOnServedRequests_of scope simulators two hz⟩

/-- **`protocolAtFiles Z` is the object in the input at which `VerifierAndGoals.verify` calls the compiled verifier**, at
every digest and further reading. -/
theorem protocol_is_the_compiled_verifiers (Z : PublicFiles) (c : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More) :
    objectOf ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) = ⟨FullSizeMatrix, LPFD.Full.XF, protocolAtFiles Z⟩ :=
  protocol_of_the_description Z c m

/-- **At every value `P` of the object's honest provers the three verifiers are `protocolAtFiles Z`'s.** -/
theorem verifiers_at_every_provers (Z : PublicFiles) (P : (filesAt Z).Provers) :
    ((filesAt Z).withProvers P).offline = (protocolAtFiles Z).offline ∧ ((filesAt Z).withProvers P).link = (protocolAtFiles Z).link ∧
      ((filesAt Z).withProvers P).onlineBatch = (protocolAtFiles Z).onlineBatch := ⟨rfl, rfl, rfl⟩

/-- **The challenges that pass: completeness's and zero knowledge's work bits clear as soundness's
three clearings do.** -/
theorem work_clears_as_soundness (Z : PublicFiles) :
    (∀ ρ, (workAtFiles Z).offline.cleared ρ = (offlineClearing Z).cleared ρ) ∧
      (∀ ρ, (workAtFiles Z).link.cleared ρ = (linkClearing Z).cleared ρ) ∧
      ∀ ρ, (workAtFiles Z).online.cleared ρ = (onlineClearing Z).cleared ρ :=
  ⟨fun ρ => (RoundsQueryLayout.cleared_clearing (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh ρ).symm,
    fun ρ => (RoundsQueryLayout.cleared_clearing (protocolAtFiles Z).link.shape (filesAt Z).annL (wLC (wiringAtFiles Z)).sh ρ).symm,
    fun ρ =>
      (RoundsQueryLayout.cleared_clearing (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann (wBC (wiringAtFiles Z)).sh ρ).symm⟩

/-- **And their tests of work are the three of which soundness's bound on a probability speaks.** -/
theorem work_passes_as_soundness (Z : PublicFiles) :
    (workAtFiles Z).offline.passes =
        RoundsQueryLayout.pass (protocolAtFiles Z).offline.shape (filesAt Z).annT (wTC (wiringAtFiles Z)).sh ∧
      (workAtFiles Z).link.passes =
        RoundsQueryLayout.pass (protocolAtFiles Z).link.shape (filesAt Z).annL (wLC (wiringAtFiles Z)).sh ∧
      (workAtFiles Z).online.passes =
        RoundsQueryLayout.pass (protocolAtFiles Z).onlineBatch.loc.shape (protocolAtFiles Z).onlineBatch.ann (wBC (wiringAtFiles Z)).sh := ⟨rfl, rfl, rfl⟩

/-- **The two maps from the library's record of three provers to a triple are one.** -/
theorem records_are_one {Index Request : Type} {L : HolographicProtocol Index Request} (Hs : ThreeProvers L) :
    OnBytes.Prover.ofRecs Hs = HonestProvers.ofThreeProvers Hs := rfl

/-- **The offline prover inside the triple is the honest provers' own.** -/
theorem offline_prover_inside (parts : Parts Z) :
    (proversAtFiles Z hr (HonestProvers.ofThreeProvers (honestProvers Z parts))).offlineProver =
      offlineProver parts := rfl

/-- **So is the link prover.** -/
theorem link_prover_inside (parts : Parts Z) :
    (proversAtFiles Z hr (HonestProvers.ofThreeProvers (honestProvers Z parts))).linkProver = linkProver Z := rfl

/-- **The offline prover is the key file's prover, at the files' own description.** -/
theorem offline_prover_at_description (parts : Parts Z) {d : OfflineDescription}
    (hd : offlineDescription Z = .ok d) :
    offlineProver parts =
      offlineProverWithEncodedTable Z (keyFileDescription d.source d.numbers d.later) parts.book (parts.prover d) runValueBytes
        runValueBytes (offlineStart d) := by
  unfold offlineProver
  rw [hd]

/-- **The statement `TheProverIsCompleteAsIOP` is completeness at that same triple.** -/
theorem complete_statement_is_at_the_triple (parts : Parts Z) :
    TheProverIsCompleteAsIOP Z parts hr ↔
      (InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
        CompleteOnServedRequests Z hr
          (proversAtFiles Z hr (HonestProvers.ofThreeProvers (honestProvers Z parts)))) := Iff.rfl

/-- **What «the honest offline run fails» is**: the prover aborts, or `(protocolAtFiles Z).offline.accept` says no.
-/
theorem failure_reads_accept (H : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (i : FullSizeMatrix) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (c : H.Coin) (ρ : Rho (protocolAtFiles Z).offline.shape) :
    FailsAt H (workAtFiles Z).offline ((protocolAtFiles Z).encodeIndex i r) (i, r, e) ((protocolAtFiles Z).recOf i r e) c ρ ↔
      (ρ ∈ H.withheld (i, r, e) ((protocolAtFiles Z).recOf i r e) ∨
        ∃ τ : Tr (protocolAtFiles Z).offline.shape,
          (workAtFiles Z).offline.sameButForNonces ((H.strat (i, r, e) ((protocolAtFiles Z).recOf i r e) c).run ρ).1 τ ∧
            (protocolAtFiles Z).offline.accept ((protocolAtFiles Z).recOf i r e) ((protocolAtFiles Z).encodeIndex i r) τ = false) := Iff.rfl

/-- **What soundness's offline clause is**: where no index is extracted the prover has lost towards
«`(protocolAtFiles Z).offline.accept` says no». -/
theorem soundness_reads_accept {errors : (protocolAtFiles Z).RoundErrors}
    (h : (protocolAtFiles Z).SoundInParts (relationAtFiles Z) errors) (firstTable : (protocolAtFiles Z).Table)
    (firstSample : (protocolAtFiles Z).Sample) (hc : ¬ (protocolAtFiles Z).hasCollisionAt firstTable firstSample.1)
    (hx : (protocolAtFiles Z).extractIndex firstTable firstSample = none) :
    Doomed (protocolAtFiles Z).offline.shape errors.offline fun transcript =>
      (protocolAtFiles Z).offline.accept firstSample firstTable transcript = false :=
  h.offline firstTable firstSample hc hx

end AtPublicFiles.OneProtocol

#print axioms AtPublicFiles.OneProtocol.threeAtOne_of_statements
#print axioms AtPublicFiles.OneProtocol.statements_of_threeAtOne
#print axioms AtPublicFiles.OneProtocol.protocol_is_the_compiled_verifiers
#print axioms AtPublicFiles.OneProtocol.served_is_true
#print axioms AtPublicFiles.OneProtocol.verifiers_at_every_provers
#print axioms AtPublicFiles.OneProtocol.work_clears_as_soundness
#print axioms AtPublicFiles.OneProtocol.work_passes_as_soundness
#print axioms AtPublicFiles.OneProtocol.records_are_one
#print axioms AtPublicFiles.OneProtocol.offline_prover_inside
#print axioms AtPublicFiles.OneProtocol.link_prover_inside
#print axioms AtPublicFiles.OneProtocol.offline_prover_at_description
#print axioms AtPublicFiles.OneProtocol.complete_statement_is_at_the_triple
#print axioms AtPublicFiles.OneProtocol.failure_reads_accept
#print axioms AtPublicFiles.OneProtocol.soundness_reads_accept
