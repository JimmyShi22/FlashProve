-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/ZeroKnowledgeFromTheOfflineLines.lean

This file takes zeroKnowledgeFromWhatIsLeftAtRecord
(AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeftAtRecord.lean) one step further: it proves the KindShare
of the kind K12, which is a premise there. Of the premises of
zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines (AtFullSide/T3/TheOneAtTheG.lean) there remain
scope, live, hr, made, h and the conditions on the offline prover. Honest verifier; interactive
oracle proof; served requests.

Terms
  * scope (InScope files = true) says that the layout file is that of the stored full-size example,
    that the reader accepts the files, that the parameter file is that example's but for eight free
    numbers, and that 2^8 ≤ theta. live (protocolDataWellFormed (asDescriptionFiles files) = true) says that the library's
    Boolean test protocolDataWellFormed accepts the public files. hr (readFiles files = .ok pp) says that the
    reader returns the parameters pp.
  * made says that the builder onlineProverFromPublicFiles, at OnBytes.secondHashFunction and at the argument baseFilling, returns A.
    h (HeadAtReturn files A) holds the data from which the online description is made at A.
  * A kind (VerifiableInference.Desc.KindName) is one of sixteen labels, K1 to K15 and frame, that
    the places of the proof file's description carry. KindShare
    (Johnson/Desc/ProofFile/Honest/Law/RowDebtsByKind.lean) bundles the three conditions that the
    theorem zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines (AtFullSide/T3/TheOneAtTheG.lean)
    asks of one kind. It asks them of thirteen kinds: all but K9, K15 and frame (Unlaid).

Main statements
  k12AtRecord
      Premises: scope, live, hr, made and h. Conclusion: the KindShare of the kind K12 at the sides
      theGAtRecord, the relation BaseRel and the family of invariants theFamily.
  TheOfflineLines
      A structure, meant as a premise. Its fields are parts (the offline prover's arguments), a (a
      bound), offlineSimulator, and the three conditions offlineTable, offline and offlineStops on
      the offline prover.
  zeroKnowledgeFromTheOfflineLines
      Premises: scope, live, hr, made, h, and off : TheOfflineLines files. Conclusion:
      ZeroKnowledgeOnServedRequests files hr at the provers HonestProvers.ofThreeProvers (honestProvers
      files off.parts), with the definition's three bounds offlineStops, linkStops and onlineStops
      at off.a, 0 and 2^-174.

Limits
  * This file adds no statement on what a proof hides beyond ZeroKnowledgeOnServedRequests, as
    defined in VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean.
  * A statement of this form alone is also met by a prover that stops publicly or sends fixed
    messages. AtFullSide/E2E/BothEndsAtOneTerm.lean states it beside completeness for the provers at
    thePartsAt files.
  * TheOfflineLines files is a premise, and this file does not show that it has a value; made and h
    are premises too. AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean supplies all three.
  * The two instances [Inhabited P5J.TS] and [Inhabited Desc.K14.St] are arguments of the
    statements.
  * The statements are at the level of the interactive oracle proof, before any hashing or
    compilation. They say nothing about the C++ programs.
  * They are about the honest provers as they are defined in Lean, default values included. That is
    a definition, not a program that runs.
  * The relation in the statements is ServedRequest: the model's result on the request is the
    claimed output. A request that is not served, and so every request at which the model has no
    result, enters the definition in one way only: proversAtFiles makes the provers refuse it, the
    field refuses of RunByRun asks that the online prover withholds at every message there, and the
    simulators are told of each request whether it is served
    (VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean).
  * Whether a request is served depends on the weights. The definition does not hide it: its
    simulators are told it for each request.
  * The definition asks that simulators exist. It puts no bound on their running time.
  * That some request is served (the field someRequestIsServed) is shown at made-up weights, by
    Meaning.served_met, and says nothing of a real model's weights.
  * They are at what onlineProverFromPublicFiles returns at baseFilling. They hold for the full-size layout, and for the
    format's second hash function OnBytes.secondHashFunction, alone.
  * A KindShare speaks only of the lists of its kind that are present in the sides G, and of the
    parts that a run calls. Where there are none it holds vacuously. That such lists are present is
    stated beside the theorems of some kinds and not of others, and it is not stated in this file.
  * A KindShare leaves unasked the fields of Good that concern completeness, and asks its condition
    On only at the parts that a run has called. A prover whose early block is always refused would
    therefore meet the later conditions vacuously. Completeness for the same provers excludes that,
    and it is not called in this file.
  * The proofs in this file only combine theorems of other files, and every limit of these files
    applies here.

Built on
  * AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeftAtRecord.lean: zeroKnowledgeFromWhatIsLeftAtRecord,
    theHalf, thePartsOfTheThreads, theGAtRecord, theFamily.
  * AtFullSide/K12/Part4/ShareK12AtTheRecord.lean: k12_share_at_the_record.
  * AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeft.lean: baseRel_is_tied.
-/
import AtFullSide.E2E.ZeroKnowledgeFromWhatIsLeftAtRecord
import AtFullSide.K12.Part4.ShareK12AtTheRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- The default instance for the table of scales is removed, so that a statement that reads such a
table has to name it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (OnlineProverWithDescription Cells onlineProverFromPublicFiles KindShare)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)

attribute [local instance high] oneAtGPad oneAtGValue oneAtGDefault

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {files : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}

/-- The KindShare of the kind K12 at theGAtRecord, BaseRel and theFamily, by k12_share_at_the_record
at theHalf, thePartsOfTheThreads and baseRel_is_tied. -/
theorem k12AtRecord (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) :
    KindShare A (theGAtRecord live hr made h) A.H (BaseRel files hr)
      (theFamily scope live hr made h) .K12 :=
  AtFullSide.K12.k12_share_at_the_record made (theHalf live hr made h)
    (thePartsOfTheThreads live hr made h) (baseRel_is_tied scope hr h)

/-- What zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines asks of the offline prover. A
definition, meant as a premise. -/
structure TheOfflineLines (files : PublicFiles) where
  /-- The arguments of the offline prover. -/
  parts : Parts files
  /-- The bound that offlineStops states for the offline prover. -/
  a : ℝ≥0∞
  offlineSimulator : Compile.Lifetime.SimOf (protocolAtFiles files).offline
  offlineTable : ∀ i r e, (offlineProver parts).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r
  offline : ExactOutsideStops (offlineProver parts)
    (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline.cleared
    offlineSimulator
  offlineStops : PrivateStopsAtMost (offlineProver parts)
    (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline a

/-- ZeroKnowledgeOnServedRequests at off.parts and off.a, from scope, live, hr, made, h and the
conditions off on the offline prover. -/
theorem zeroKnowledgeFromTheOfflineLines (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) (off : TheOfflineLines files) :
    ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files off.parts))
      off.a 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) :=
  zeroKnowledgeFromWhatIsLeftAtRecord scope live hr made h
    { k12 := k12AtRecord scope live hr made h
      parts := off.parts
      a := off.a
      offlineSimulator := off.offlineSimulator
      offlineTable := off.offlineTable
      offline := off.offline
      offlineStops := off.offlineStops }

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.k12AtRecord
#print axioms VerifiableInference.Compilation.zeroKnowledgeFromTheOfflineLines
