-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/CompleteAtTheFiles.lean

This file proves completeness of the protocol's honest provers at the level of the interactive
oracle proof, on served requests, with error at most completenessTarget = 2^(-41). The main theorem
is complete_in_scope.

Terms.
  * Z : VerifierAndGoals.PublicFiles is a set of public files. InScope Z = true says that Z has the layout file of the
    stored full-size example, that readFiles Z succeeds with some parameters pp, that the policy
    file equals policyFile (freeLinesOf pp), and that the policy's theta is at least 2^8
    (Ladder.lean).
  * protocolDataWellFormed (asDescriptionFiles Z) = true says that a test of the verifier on the public files accepts: the
    plan and the descriptions of the key file and of the proof file can be built, and dataWellFormedAtFullSizeDepth accepts
    them (Johnson/Goal/Description/Live.lean).
  * theProvers Z (settingsOfRead pp) (thePartsAt Z) are the protocol's three honest provers
    (offline, link and online). They are honestProvers (E2E/TheHonestProver.lean) at the offline
    prover's arguments thePartsAt Z (E2E/KeyArgumentsAt.lean), changed in one point only: the online
    prover withholds every message at a request that is not served (refuseUnserved at the relation
    ServedAt; Johnson/Face/Protocol.lean, Johnson/Face/NeverBuilt.lean and
    Johnson/Face/HonestProversWithCompiledPart.lean). The offline and the link prover are unchanged.
  * ServedRequest committerCoinCountLessOne Z hr i x says that i is the index of some model weights, and that x is
    the instance that the verifier's builder makes of a prompt and output tokens, where these form a
    request and the model's result on that request is exactly these output tokens
    (E2E/CompleteAsIOPAtFiles.lean).
  * A run fails (FailsAt, Hiop/CompleteCore.lean) if the prover aborts, or the verifier rejects
    under some choice of nonces.
  * CompleteAtFiles Z (thePartsAt Z) hr (E2E/CompleteAsIOPAtNamed.lean) unfolds to CompleteIOP
    (Johnson/Face/CompleteAsIOP.lean) for these provers on the served requests. It says that there
    are an offline, a link and an online error that add up to at most completenessTarget, and that
    at every served request, at every randomness of the encoding, every value of (protocolAtFiles Z).OutOfDomainSeed and,
    for the online run, every copy number, each of the three runs fails with probability at most its
    error, over the prover's coins and over the verifier's challenges that pass the proof-of-work
    condition. It also says that this condition is the protocol's own (PartsWork.Faithful), and that
    the online run sends the copy number that the prover was given.
  * CompleteAtEveryCoin (Johnson/Prover/All/CompleteAsIOPForTheCompiler.lean) gives the same three
    bounds at every fixed coin of the prover, over the challenges alone.
  * The base construction is onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling: the function that
    builds the proof file's description and the prover's parts from the public files. HeadAtReturn Z
    A (Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean) collects, for a return A of that
    function, the data from which the online description is made and the library's facts on the
    public part of A.

Main statements. All three have the same conclusion: CompleteAtFiles Z (thePartsAt Z) hr, together
with errors a and c such that a + 0 + c ≤ completenessTarget and CompleteAtEveryCoin holds with
offline error a, link error 0 and online error c. The conclusion names the honest provers
themselves; the base construction occurs only in premises and inside the proofs, and no auxiliary
parameter of the proofs occurs in the conclusion. One such parameter, the field open₂ of
TheThreadsHalf, is set to zeros in the proofs (open₂_filled, OpenSharedFilled.lean of this folder);
this file does not show that another choice would serve as well.
  * complete_in_scope: from InScope Z = true, protocolDataWellFormed (asDescriptionFiles Z) = true and readFiles Z = .ok pp,
    with no other premise.
  * complete_at_the_files: from protocolDataWellFormed (asDescriptionFiles Z) = true, readFiles Z = .ok pp and two further
    premises: the base construction returns A (made), and h : HeadAtReturn Z A. The theorem
    complete_in_scope removes these two by showing that such an A and h exist.
  * complete_at_the_stored_files_whole: at Z = VerifierAndGoals.storedPublicFiles, the files of the stored full-size
    example, from readFiles Z = .ok pp alone.

Limits.
  * The statements are at the level of the interactive oracle proof: before any hashing or
    compilation. They say nothing about the C++ programs.
  * They are about the honest provers as they are defined in Lean, default values included. These
    are definitions, not programs that run. The definitions contain default branches, which apply
    where a construction step returns an error or a value is missing. This file does not show that
    these branches are never reached.
  * They are about served requests alone. A request at which the model has no result (its output
    option is none), or a result other than the claimed output tokens, is not a served request, and
    nothing is said of it. What else the relation ServedRequest excludes is not examined here.
  * That some request is served is not shown in this file. CompleteInScopeNotForNothing.lean shows
    it, at made-up weights only.
  * They hold for the full-size layout and for the format's second hash function, OnBytes.secondHashFunction,
    alone.
  * The proofs in this file only combine theorems of other files, so the result is worth what every
    file beneath it is worth. Some hundreds of closed facts beneath are checked by evaluation in
    Lean's kernel, and no independent checker has replayed them.
  * Nothing on soundness or hiding.

Built on.
  * complete_from_the_union (CompleteFromTheUnion.lean) and off_at_the_files
    (CompleteFromTheObjectAlone.lean), both in this folder.
  * baseMaker_returns and headAtReturn_baseMaker (AtFullSide/K1/HeadAtBaseMaker.lean).
  * scope_named and live_named (E2E/CompleteAsIOPAtNamed.lean).
-/
import AtFullSide.Honest.CompleteFromTheUnion
import AtFullSide.Honest.CompleteFromTheObjectAlone

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- The default instance Inst.Model.Scl.ref is removed, so that every statement that uses a table of
scales names that table explicitly. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtFullSide.Honest
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open OnBytes.Slice (frS)
open AtPublicFiles.Committed (PadZ pads_nonempty)
open ProofFile.Honest (OnlineProverWithDescription IndexCommitterCoins Cells onlineProverFromPublicFiles)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixFilling)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles settingsOfRead)
open FlashProve (committerCoinCountLessOne protocolDataWellFormed)
open OnBytes.Prover (CompleteAtEveryCoin)
open VerifiableInference.Compilation (theProvers)

local instance (priority := high) nonemptyPadZ_atTheFiles : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_atTheFiles : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_atTheFiles : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {pp : Inst.Model.ScalesAndPolicy}

/-- Completeness at public files that pass the verifier's test, given a return A of the base
construction and a HeadAtReturn Z A. The proof passes off_at_the_files to complete_from_the_union.
-/
theorem complete_at_the_files (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hr : readFiles Z = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (h : HeadAtReturn Z A) :
    CompleteAtFiles Z (thePartsAt Z) hr ∧
      ∃ a c : ℝ≥0∞, a + 0 + c ≤ completenessTarget ∧
        CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) (thePartsAt Z)) (workAtFiles Z)
          (ServedRequest committerCoinCountLessOne Z hr) a 0 c :=
  complete_from_the_union live hr made h (off_at_the_files h.head.scope live hr)

/-- **Completeness in scope**, from InScope, protocolDataWellFormed and readFiles alone. The return of the base
construction and the HeadAtReturn are shown to exist. -/
theorem complete_in_scope (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hr : readFiles Z = .ok pp) :
    CompleteAtFiles Z (thePartsAt Z) hr ∧
      ∃ a c : ℝ≥0∞, a + 0 + c ≤ completenessTarget ∧
        CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) (thePartsAt Z)) (workAtFiles Z)
          (ServedRequest committerCoinCountLessOne Z hr) a 0 c := by
  obtain ⟨A, made⟩ := ProofFile.Honest.K1.baseMaker_returns Z scope live
  obtain ⟨h, -⟩ := ProofFile.Honest.K1.headAtReturn_baseMaker Z scope live made
  exact complete_at_the_files live hr made h

/-- Completeness at the files of the stored full-size example, VerifierAndGoals.storedPublicFiles. -/
theorem complete_at_the_stored_files_whole (hZ : Z = VerifierAndGoals.storedPublicFiles) (hr : readFiles Z = .ok pp) :
    CompleteAtFiles Z (thePartsAt Z) hr ∧
      ∃ a c : ℝ≥0∞, a + 0 + c ≤ completenessTarget ∧
        CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) (thePartsAt Z)) (workAtFiles Z)
          (ServedRequest committerCoinCountLessOne Z hr) a 0 c :=
  complete_in_scope (scope_named (Or.inl hZ)) (live_named (Or.inl hZ)) hr

end AtFullSide.Honest

#check @AtFullSide.Honest.complete_at_the_files
#check @AtFullSide.Honest.complete_in_scope
#check @AtFullSide.Honest.complete_at_the_stored_files_whole
#print axioms AtFullSide.Honest.complete_at_the_files
#print axioms AtFullSide.Honest.complete_in_scope
#print axioms AtFullSide.Honest.complete_at_the_stored_files_whole
