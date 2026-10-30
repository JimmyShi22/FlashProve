-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean

This file proves zkOnServedRequests_inScope: from three premises on the public files, the honest
provers that are defined in Lean satisfy ZeroKnowledgeOnServedRequests, the statement defined in
VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean. Honest verifier; interactive oracle
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
  zkOnServedRequests_inScope
      Premises: scope, live and hr. Conclusion: ZeroKnowledgeOnServedRequests files hr at the
      provers HonestProvers.ofThreeProvers (honestProvers files (thePartsAt files)), with the definition's
      three bounds offlineStops, linkStops and onlineStops at 0, 0 and 2^-174.
  AtFullSide.T3.zkOnServedRequests_fromTheRows
      Premises: scope, live, hr, made, h, and a KindShare for each of the thirteen kinds at the
      sides theGAtRecord, the relation BaseRel and the family of invariants theFamily. Conclusion:
      the same as above.
  rowsAtRecord
      Premises: scope, live, hr, made and h. Conclusion: these thirteen KindShare statements.

Limits
  * This file adds no statement on what a proof hides beyond ZeroKnowledgeOnServedRequests, as
    defined in VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean.
  * A statement of this form alone is also met by a prover that stops publicly or sends fixed
    messages. AtFullSide/E2E/BothEndsAtOneTerm.lean states it beside completeness for the same
    provers.
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
  * The steps between use theOneObjectValue (AtFullSide/Honest/TheOneObjectValue.lean). It is a
    value at what onlineProverFromPublicFiles returns at baseFilling; most of its fields are implications whose premise
    is an invariant of a thread; and its parameter open₂ is set to zeros. The conclusion of
    zkOnServedRequests_inScope names none of these.
  * theHalf is taken from theOneObjectValue, whose field owes₃ is filled by owes₃_whole_filled
    (AtFullSide/Honest/LastSocketsFilled.lean). That statement bears the library's label "NOT IN
    FRONT OF A LAW OVER COINS" (Johnson/Bind/ForProver/FiveFieldsAt.lean). Its tied premise is that
    of a tied run; baseRel_is_tied shows that every input of BaseRel is a tied request, at every
    value of the table's coins and of the seed. zkOnServedRequests_inScope has no premise beyond the
    three on the public files, so Lean has checked that tied premise wherever its proof uses the
    statement.
  * The three conditions on the offline prover come from offline_lines_into_a_socket
    (E2E/OfflineLinesIntoASocket.lean), with the limits of that file.
  * The proofs in this file only combine theorems of other files, and every limit of these files
    applies here.
  * Some closed facts beneath these proofs are checked by evaluation in Lean's kernel, and no
    independent checker has replayed them.

Built on
  * E2E/OfflineLinesIntoASocket.lean: offline_lines_into_a_socket.
  * AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeft.lean: zeroKnowledgeFromWhatIsLeft.
  * AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeftAtRecord.lean: theHalf, thePartsOfTheThreads,
    theGAtRecord, theFamily.
  * AtFullSide/E2E/ZeroKnowledgeFromTheOfflineLines.lean: k12AtRecord.
  * AtFullSide/E2E/TheSharesAtTheKOfRecord.lean: sharesAtTheKOfRecord_paid.
  * AtFullSide/K1/SimAtTermAll.lean: base_returns. AtFullSide/K1/HeadAtReturn.lean:
    headAtReturn_base.
-/
import AtFullSide.E2E.ZeroKnowledgeFromTheOfflineLines
import AtFullSide.K1.SimAtTermAll
import AtFullSide.K1.HeadAtReturn
import E2E.OfflineLinesIntoASocket

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
open AtPublicFiles.TheSides (theKOfRecord)
open ProofFile.Honest (OnlineProverWithDescription Cells onlineProverFromPublicFiles KindShare)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixInput)
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)

attribute [local instance high] oneAtGPad oneAtGValue oneAtGDefault

variable {files : PublicFiles}

section AtAReturn
variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}

/-- From a KindShare for each of the thirteen kinds, at theGAtRecord, BaseRel and theFamily, to
ZeroKnowledgeOnServedRequests at thePartsAt files. The three conditions on the offline prover are
supplied by offline_lines_into_a_socket. -/
theorem _root_.AtFullSide.T3.zkOnServedRequests_fromTheRows (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A)
    (rows : ∀ κ, ¬ Unlaid κ → KindShare A (theGAtRecord live hr made h) A.H (BaseRel files hr)
      (theFamily scope live hr made h) κ) :
    ZeroKnowledgeOnServedRequests files hr
      (HonestProvers.ofThreeProvers (honestProvers files (thePartsAt files))) 0 0
      (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) :=
  AtPublicFiles.OfflineRows.offline_lines_into_a_socket live scope hr
    (C := fun parts => ZeroKnowledgeOnServedRequests files hr
      (HonestProvers.ofThreeProvers (honestProvers files parts)) 0 0
      (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))))
    fun parts offlineSimulator offlineTable offline offlineStops =>
      zeroKnowledgeFromWhatIsLeft scope live hr made h
        { half := theHalf live hr made h
          rows := theKOfRecord A h.head
          shares := rows
          parts := parts
          a := 0
          offlineSimulator := offlineSimulator
          offlineTable := offlineTable
          offline := offline
          offlineStops := offlineStops }

/-- The thirteen KindShare statements at theGAtRecord, BaseRel and theFamily: twelve by
sharesAtTheKOfRecord_paid, and the one for the kind K12 by k12AtRecord. -/
theorem rowsAtRecord (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) :
    ∀ κ, ¬ Unlaid κ → KindShare A (theGAtRecord live hr made h) A.H (BaseRel files hr)
      (theFamily scope live hr made h) κ :=
  AtPublicFiles.AtFiles.HonestTerm.OutputHead.sharesAtTheKOfRecord_paid scope live made h
    (thePartsOfTheThreads live hr made h) (BaseRel files hr) (theFamily scope live hr made h)
    (k12AtRecord scope live hr made h)

end AtAReturn

/-- ZeroKnowledgeOnServedRequests for the honest provers at thePartsAt files, from the three
premises scope, live and hr on the public files. The proof takes A from base_returns and h from
headAtReturn_base, and takes the two Inhabited instances from the online description; the statement
names none of them. The limits are listed at the head of this file. -/
theorem zkOnServedRequests_inScope (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) :
    ZeroKnowledgeOnServedRequests files hr
      (HonestProvers.ofThreeProvers (honestProvers files (thePartsAt files))) 0 0
      (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) := by
  obtain ⟨A, made⟩ := AtFullSide.K1.base_returns files scope live
  obtain ⟨h, -⟩ := ProofFile.Honest.K1.headAtReturn_base files matrixInput OnBytes.HonestTrace.Sz.ref
    ProofFile.Honest.openHonest scope live made
  haveI : Inhabited P5J.TS := ⟨h.description.start₁ (h.description.pub
    (LPFD.Full.instanceAsPlainRecord (FlashProve.dataAtFiles FlashProve.flashProveData files).G.z₀))⟩
  haveI : Inhabited Desc.K14.St := ⟨h.description.start₂ (h.description.pub
    (LPFD.Full.instanceAsPlainRecord (FlashProve.dataAtFiles FlashProve.flashProveData files).G.z₀))⟩
  exact AtFullSide.T3.zkOnServedRequests_fromTheRows scope live hr made h
    (rowsAtRecord scope live hr made h)

end VerifiableInference.Compilation

#print axioms AtFullSide.T3.zkOnServedRequests_fromTheRows
#print axioms VerifiableInference.Compilation.rowsAtRecord
#print axioms VerifiableInference.Compilation.zkOnServedRequests_inScope
