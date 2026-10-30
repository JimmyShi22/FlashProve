-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeftAtRecord.lean

This file takes zeroKnowledgeFromWhatIsLeft (AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeft.lean) one
step further: three fields of its premise WhatIsLeftOfT3 are filled with named values. The premises
that remain are collected in the structure WhatIsLeftAtRecord. Honest verifier; interactive oracle
proof; served requests.

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
  theHalf
      The value of TheThreadsHalf h hr that is the first half of theOneObjectValue made live
      (AtFullSide/Honest/TheOneObjectValue.lean). It fills the field half.
  thePartsOfTheThreads, theGAtRecord, theFamily
      The arguments of the three threads at theHalf; the sides at these arguments and at the rows
      theKOfRecord A h.head (E2E/TheKValue.lean); and the family of invariants that theHalf gives at
      these sides and at the relation BaseRel.
  WhatIsLeftAtRecord
      A structure, meant as a premise. Its fields are k12 (the KindShare of the kind K12 at
      theGAtRecord, BaseRel and theFamily), parts (the offline prover's arguments), a (a bound),
      offlineSimulator, and the three conditions offlineTable, offline and offlineStops on the
      offline prover.
  WhatIsLeftAtRecord.toWhatIsLeftOfT3
      From a value of WhatIsLeftAtRecord to a value of WhatIsLeftOfT3: half is theHalf, rows is
      theKOfRecord A h.head, and shares comes from sharesAtTheKOfRecord_paid at the field k12.
  zeroKnowledgeFromWhatIsLeftAtRecord
      Premises: scope, live, hr, made, h, and left : WhatIsLeftAtRecord scope live hr made h.
      Conclusion: ZeroKnowledgeOnServedRequests files hr at the provers HonestProvers.ofThreeProvers
      (honestProvers files left.parts), with the definition's three bounds offlineStops, linkStops
      and onlineStops at left.a, 0 and 2^-174.

Limits
  * This file adds no statement on what a proof hides beyond ZeroKnowledgeOnServedRequests, as
    defined in VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean.
  * A statement of this form alone is also met by a prover that stops publicly or sends fixed
    messages. AtFullSide/E2E/BothEndsAtOneTerm.lean states it beside completeness for the provers at
    thePartsAt files.
  * WhatIsLeftAtRecord is a premise, and this file does not show that it has a value; scope, live,
    hr, made and h are premises too. AtFullSide/E2E/ZeroKnowledgeFromTheOfflineLines.lean proves the
    field k12, and AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean supplies the rest.
  * The two instances [Inhabited P5J.TS] and [Inhabited Desc.K14.St] are arguments of the
    statements.
  * theOneObjectValue is a value at what onlineProverFromPublicFiles returns at baseFilling; most of its fields are
    implications whose premise is an invariant of a thread; and its parameter open₂ is set to zeros.
  * theHalf is taken from theOneObjectValue, whose field owes₃ is filled by owes₃_whole_filled
    (AtFullSide/Honest/LastSocketsFilled.lean). That statement bears the library's label "NOT IN
    FRONT OF A LAW OVER COINS" (Johnson/Bind/ForProver/FiveFieldsAt.lean). Its tied premise is that
    of a tied run; baseRel_is_tied shows that every input of BaseRel is a tied request, at every
    value of the table's coins and of the seed. zkOnServedRequests_inScope has no premise beyond the
    three on the public files, so Lean has checked that tied premise wherever its proof uses the
    statement.
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
  * They hold for the full-size layout, and for the format's second hash function OnBytes.secondHashFunction,
    alone.
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
  * AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeft.lean: zeroKnowledgeFromWhatIsLeft, WhatIsLeftOfT3,
    baseRel_is_tied.
  * AtFullSide/E2E/TheSharesAtTheKOfRecord.lean: sharesAtTheKOfRecord_paid.
  * AtFullSide/Honest/TheOneObjectValue.lean: theOneObjectValue.
  * E2E/TheKValue.lean: theKOfRecord. E2E/TheG.lean: theGOfReturn, theGOfReturn_prover.
-/
import AtFullSide.E2E.ZeroKnowledgeFromWhatIsLeft
import AtFullSide.E2E.TheSharesAtTheKOfRecord
import AtFullSide.Honest.TheOneObjectValue

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
open AtPublicFiles.TheG (ThreadParts theGOfReturn theGOfReturn_prover)
open AtPublicFiles.TheSides (KindRows theKOfRecord)
open ProofFile.Honest (Sides OnlineProverWithDescription Cells ThreadsP ready onlineProverFromPublicFiles KindShare)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixInput tableCoins)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open LPFD.Full (instanceAsPlainRecord XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed committerCoinCountLessOne)
open AtFullSide.Honest (TheThreadsHalf TiedRequest TiedRun)

attribute [local instance high] oneAtGPad oneAtGValue oneAtGDefault

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {files : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}

section Values
variable (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
  {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
  (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
  (h : HeadAtReturn files A)

/-- The first half of theOneObjectValue made live, as a value of TheThreadsHalf h hr. -/
def theHalf : TheThreadsHalf h hr :=
  (AtFullSide.Honest.theOneObjectValue (h := h) (hr := hr) made live).toTheThreadsHalf

/-- The arguments of the three threads (the argument T of
zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines), at the parameter open₃ of theHalf. -/
abbrev thePartsOfTheThreads :=
  AtFullSide.Honest.TheLetters.parts h (theHalf live hr made h).open₃

/-- The sides (called G in this folder) at these arguments and at the rows theKOfRecord A h.head. -/
abbrev theGAtRecord :=
  theGOfReturn made h (thePartsOfTheThreads live hr made h) (theKOfRecord A h.head)

/-- The family of invariants (the argument Th of
zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines) that theHalf gives at theGAtRecord and at the
relation BaseRel. -/
abbrev theFamily :=
  (theHalf live hr made h).threadsAtRelation made (theGAtRecord live hr made h)
    (theGOfReturn_prover made h (thePartsOfTheThreads live hr made h) (theKOfRecord A h.head))
    (baseRel_is_tied scope hr h)

/-- The premises that remain once half, rows and twelve of the thirteen KindShare statements are
filled. A definition, meant as a premise. -/
structure WhatIsLeftAtRecord where
  /-- The KindShare of the kind K12. -/
  k12 : KindShare A (theGAtRecord live hr made h) A.H (BaseRel files hr)
    (theFamily scope live hr made h) .K12
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

end Values

/-- A value of WhatIsLeftAtRecord gives a value of WhatIsLeftOfT3. -/
def WhatIsLeftAtRecord.toWhatIsLeftOfT3 {scope : InScope files = true}
    {live : protocolDataWellFormed (asDescriptionFiles files) = true} {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles files = .ok pp}
    {made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A}
    {h : HeadAtReturn files A} (left : WhatIsLeftAtRecord scope live hr made h) :
    WhatIsLeftOfT3 scope hr made h where
  half := theHalf live hr made h
  rows := theKOfRecord A h.head
  shares := AtPublicFiles.AtFiles.HonestTerm.OutputHead.sharesAtTheKOfRecord_paid scope live made h
    (thePartsOfTheThreads live hr made h) (BaseRel files hr) (theFamily scope live hr made h)
    left.k12
  parts := left.parts
  a := left.a
  offlineSimulator := left.offlineSimulator
  offlineTable := left.offlineTable
  offline := left.offline
  offlineStops := left.offlineStops

/-- ZeroKnowledgeOnServedRequests at left.parts and left.a, from scope, live, hr, made, h and a
value left of WhatIsLeftAtRecord. -/
theorem zeroKnowledgeFromWhatIsLeftAtRecord (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) (left : WhatIsLeftAtRecord scope live hr made h) :
    ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files left.parts))
      left.a 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) :=
  zeroKnowledgeFromWhatIsLeft scope live hr made h left.toWhatIsLeftOfT3

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.theHalf
#print axioms VerifiableInference.Compilation.WhatIsLeftAtRecord.toWhatIsLeftOfT3
#print axioms VerifiableInference.Compilation.zeroKnowledgeFromWhatIsLeftAtRecord
