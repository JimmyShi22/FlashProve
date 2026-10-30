-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/TheSharesAtTheKOfRecord.lean

This file collects, at one value of the kinds' rows, the KindShare statements that the theorems on
ZeroKnowledgeOnServedRequests in AtFullSide/T3/TheOneAtTheG.lean ask as their premise shares. The
value is theKOfRecord A h.head (E2E/TheKValue.lean), which is made of the thirteen entries
theThirteen and the rows laterOurs of the later chains.

Terms
  * scope (InScope files = true) says that the layout file is that of the stored full-size example,
    that the reader accepts the files, that the parameter file is that example's but for eight free
    numbers, and that 2^8 ≤ theta. live (protocolDataWellFormed (asDescriptionFiles files) = true) says that the library's
    Boolean test protocolDataWellFormed accepts the public files. hr (readFiles files = .ok pp) says that the
    reader returns the parameters pp.
  * made says that the builder onlineProverFromPublicFiles, at OnBytes.secondHashFunction and at the argument baseFilling, returns A.
    h (HeadAtReturn files A) holds the data from which the online description is made at A.
    baseMaker files unfolds to that call of onlineProverFromPublicFiles.
  * A kind (VerifiableInference.Desc.KindName) is one of sixteen labels, K1 to K15 and frame, that
    the places of the proof file's description carry. KindShare
    (Johnson/Desc/ProofFile/Honest/Law/RowDebtsByKind.lean) bundles the three conditions that the
    theorem zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines (AtFullSide/T3/TheOneAtTheG.lean)
    asks of one kind. It asks them of thirteen kinds: all but K9, K15 and frame (Unlaid).
  * The number thirteen occurs twice. TheThirteen has thirteen entries: k1, k2, k7, k11, k13, k3,
    k4, k5, k6, k8, k10, k12 and w, where w is the sending of W and is of the kind K1. The thirteen
    kinds of which a KindShare is asked are K1 to K8 and K10 to K14. The kind K14 has no entry: its
    rows are among those of laterOurs.

Main statements
  laidAtTheKOfRecord
      Premises: h, and e is one of the entries of theThirteen. Conclusion: e.slot ∈ (theKOfRecord A
      h.head).lots.
  sharesAtTheKOfRecord_butK12
      Premises: scope, live, made, h, the arguments T of the threads, a relation Rel and a family of
      invariants Th. Conclusion: a KindShare for each of the twelve kinds K1 to K8, K10, K11, K13
      and K14, at the sides theGOfReturn made h T (theKOfRecord A h.head). There is no premise on a
      kind.
  sharesAtTheKOfRecord_paid
      The same premises, and k12: the KindShare of the kind K12 at the same sides, Rel and Th.
      Conclusion: a KindShare for each of the thirteen kinds.
  zeroKnowledgeOnServedRequests_atTheKOfRecord_butK12
      The theorem zeroKnowledgeOnServedRequests_atTheG called at K := theKOfRecord A h.head and at
      shares := sharesAtTheKOfRecord_paid. All its other premises remain; they are listed under
      Limits.

How the proofs go
Each kind's theorem asks that a certain entry is the one it expects, or that its entry is among
(theKOfRecord A h.head).lots. Each such condition holds by unfolding the value. Two inclusions in
the shared chain's rows (the two sendings of K1 and the six rows of K14) hold by the definition of
laterOurs. The theorems for K1 and K14 ask for the same entry k1 under two spellings (K1.Sim.lotS
and Johnson.M1.k1Lot), which are equal by unfolding.

Limits
  * This file adds no statement on what a proof hides beyond ZeroKnowledgeOnServedRequests, as
    defined in VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean. It proves no KindShare by
    itself: it sorts statements that other files prove.
  * The KindShare of the kind K12 is a premise (k12) in this file, and it constrains Th. The twelve
    other statements hold at every family Th. The theorems for K12 (AtFullSide/K12/ShareK12.lean)
    hold only at particular families and under further premises, so k12 is not available at every
    Th. AtFullSide/E2E/ZeroKnowledgeFromTheOfflineLines.lean (k12AtRecord) proves it at the family
    theFamily.
  * T and Th are arguments, and this file gives no value of either. Where Th has no value, the two
    theorems on KindShare say nothing. AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeftAtRecord.lean names
    values (thePartsOfTheThreads, theFamily).
  * zeroKnowledgeOnServedRequests_atTheKOfRecord_butK12 is conditional on scope, live, hr, made, h,
    T, asks, one, Th, k12, _start, parts and _whole, and its conclusion is itself conditional on the
    offline sides GK and three premises on them. By itself it establishes
    ZeroKnowledgeOnServedRequests for no prover.
  * A statement of this form alone is also met by a prover that stops publicly or sends fixed
    messages. AtFullSide/E2E/BothEndsAtOneTerm.lean states it beside completeness for the provers at
    thePartsAt files.
  * A KindShare holds vacuously where the sides hold no list of its kind. That the rows are present
    is stated beside each kind's own theorem, not in this file. For K9, K15 and frame the library
    shows that they have no list; that the thirteen other kinds have one is not stated here.
  * A KindShare leaves unasked the fields of Good that concern completeness, and asks its condition
    On only at the parts that a run has called. A prover whose early block is always refused would
    therefore meet the later conditions vacuously. Completeness for the same provers excludes that,
    and it is not called in this file.
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
  * Every limit of the files called applies here.

Built on
  * E2E/TheKValue.lean: theKOfRecord. E2E/TheKOfRecord.lean: theK, mem_theK.
  * E2E/TheThirteenOfRecord.lean: theThirteen, theThirteen_apart. AtFullSide/M1/KRecord.lean:
    laterOurs.
  * AtFullSide/T3/TheOneAtTheG.lean: zeroKnowledgeOnServedRequests_atTheG.
  * K1: k1Share_at_theK (AtFullSide/K1/K1ShareAtTheK.lean).
  * K2: k2_kind_share (AtFullSide/T3/ShareK2.lean). K3: k3_kind_share (AtFullSide/T3/ShareK3.lean).
  * K4: k4_share_at_theK (AtFullSide/K4/K4sEntryInTheK.lean).
  * K5: k5_kind_share (AtFullSide/T3/ShareK5.lean).
  * K6: k6Share_atTheK (AtFullSide/E2E/OutputHeadEntryOfRecord.lean).
  * K7: reply_share_at_the_G (E2E/ReplyShareAtTheG.lean).
  * K8: k8Share_at_record (AtFullSide/K8/K8Entry.lean).
  * K10: k10Share_at_record (AtFullSide/K10/K10ShareAtRecord.lean).
  * K11: k11Share_at_theGOfReturn (AtFullSide/K11/KindPaysAtTheG.lean).
  * K13: k13Share_at_theK (AtFullSide/K13/EntriesForTheK.lean).
  * K14: k14_kind_share (AtFullSide/M1/K14ShareInstance.lean).
-/
import E2E.TheKValue
import AtFullSide.T3.TheRowsFilled
import AtFullSide.K1.K1ShareAtTheK
import AtFullSide.K10.K10ShareAtRecord
import AtFullSide.M1.K14ShareInstance

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.OutputHead
open AtPublicFiles.AtFiles
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open AtPublicFiles.TheSides (KindRows LotEntry TheThirteen LaterRows theK mem_theK theThirteen
  theThirteen_apart theKOfRecord)
open ProofFile.Honest (OnlineProverWithDescription Cells ThreadsP ready KindShare)
open ProofFile.Honest.Term (matrixInput baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Compilation (Unlaid)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

variable {files : PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}

/-- For an entry e of theThirteen, e.slot is a member of (theKOfRecord A h.head).lots. -/
theorem laidAtTheKOfRecord (h : HeadAtReturn files A) {e : LotEntry (baseFilling files) A.Z A.G}
    (isOne : e ∈ (theThirteen files A.Z A.G).entries) : e.slot ∈ (theKOfRecord A h.head).lots :=
  mem_theK isOne (theThirteen_apart files A.Z A.G) (AtFullSide.M1.laterOurs A h.head)

/-- A KindShare for each of the twelve kinds K1 to K8, K10, K11, K13 and K14, at the rows
theKOfRecord A h.head. Premises: scope, live, made, h, the arguments T of the threads, a relation
Rel and a family of invariants Th. There is no premise on a kind. -/
theorem sharesAtTheKOfRecord_butK12
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (made : baseMaker files = .ok A) (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (Rel : FullSizeMatrix → ProofFile.Honest.IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc ξ, Rel w₀ rc ξ → ∀ k Rd,
      ready A.F A.B ((theGOfReturn made h T (theKOfRecord A h.head)).prover A.H) w₀ rc ξ k = .ok Rd →
      ThreadsP A.F A.B ((theGOfReturn made h T (theKOfRecord A h.head)).prover A.H) w₀ rc ξ k Rd) :
    ∀ κ, ¬ Unlaid κ → κ ≠ .K12 →
      KindShare A (theGOfReturn made h T (theKOfRecord A h.head)) A.H Rel Th κ := by
  intro κ laysRows notK12
  cases κ with
  | K1 =>
    exact AtFullSide.K1.k1Share_at_theK scope live made h T (theThirteen files A.Z A.G)
      (theThirteen_apart files A.Z A.G) (AtFullSide.M1.laterOurs A h.head) rfl rfl
      (fun _ isASending => List.mem_append_left _ (List.mem_append_right _ isASending)) Rel Th
  | K2 =>
    exact VerifiableInference.Compilation.k2_kind_share scope live made h T (theKOfRecord A h.head)
      (laidAtTheKOfRecord h (e := (theThirteen files A.Z A.G).k2) (by simp [TheThirteen.entries]))
      A.H Rel Th
  | K3 =>
    exact VerifiableInference.Compilation.k3_kind_share made h T (theKOfRecord A h.head)
      (laidAtTheKOfRecord h (e := (theThirteen files A.Z A.G).k3) (by simp [TheThirteen.entries]))
      A.H Rel Th
  | K4 =>
    exact AtFullSide.K4.k4_share_at_theK made h T (theThirteen files A.Z A.G) rfl
      (theThirteen_apart files A.Z A.G) (AtFullSide.M1.laterOurs A h.head) A.H Rel Th
  | K5 =>
    exact VerifiableInference.Compilation.k5_kind_share made h T (theKOfRecord A h.head)
      (laidAtTheKOfRecord h (e := (theThirteen files A.Z A.G).k5) (by simp [TheThirteen.entries]))
      A.H Rel Th
  | K6 =>
    exact k6Share_atTheK scope live made h T (theThirteen files A.Z A.G) rfl
      (theThirteen_apart files A.Z A.G) (AtFullSide.M1.laterOurs A h.head) Rel Th
  | K7 =>
    exact AtPublicFiles.TheSides.reply_share_at_the_G made h T (theKOfRecord A h.head)
      (laidAtTheKOfRecord h (e := (theThirteen files A.Z A.G).k7) (by simp [TheThirteen.entries]))
      A.H Rel Th
  | K8 =>
    exact (ProofFile.Honest.K8.k8Share_at_record made h T (theThirteen files A.Z A.G) rfl
      (theThirteen_apart files A.Z A.G) (AtFullSide.M1.laterOurs A h.head) A.H Rel Th).1
  | K9 => exact absurd (Or.inl rfl) laysRows
  | K10 =>
    exact ProofFile.Honest.K10.k10Share_at_record h scope live made T (theThirteen files A.Z A.G) rfl
      (theThirteen_apart files A.Z A.G) (AtFullSide.M1.laterOurs A h.head) A.H Rel Th
  | K11 =>
    exact AtFullSide.K11.k11Share_at_theGOfReturn made h T (theKOfRecord A h.head)
      (laidAtTheKOfRecord h (e := (theThirteen files A.Z A.G).k11) (by simp [TheThirteen.entries]))
      A.H Rel Th
  | K12 => exact absurd rfl notK12
  | K13 =>
    exact AtFullSide.K13.k13Share_at_theK made h T (theThirteen files A.Z A.G)
      (theThirteen_apart files A.Z A.G) (AtFullSide.M1.laterOurs A h.head) rfl A.H Rel Th
  | K14 =>
    exact AtFullSide.M1.k14_kind_share h scope live made T (theKOfRecord A h.head)
      (laidAtTheKOfRecord h (e := (theThirteen files A.Z A.G).k1) (by simp [TheThirteen.entries]))
      (laidAtTheKOfRecord h (e := (theThirteen files A.Z A.G).w) (by simp [TheThirteen.entries]))
      (laidAtTheKOfRecord h (e := (theThirteen files A.Z A.G).k10) (by simp [TheThirteen.entries]))
      (fun _ isOfTheSix => List.mem_append_left _ isOfTheSix) A.H Rel Th
  | K15 => exact absurd (Or.inr (Or.inl rfl)) laysRows
  | frame => exact absurd (Or.inr (Or.inr rfl)) laysRows

/-- A KindShare for each kind but K9, K15 and frame, at the rows theKOfRecord A h.head. Premises:
those of sharesAtTheKOfRecord_butK12, and the KindShare of the kind K12 at the same Th. -/
theorem sharesAtTheKOfRecord_paid
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (made : baseMaker files = .ok A) (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (Rel : FullSizeMatrix → ProofFile.Honest.IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc ξ, Rel w₀ rc ξ → ∀ k Rd,
      ready A.F A.B ((theGOfReturn made h T (theKOfRecord A h.head)).prover A.H) w₀ rc ξ k = .ok Rd →
      ThreadsP A.F A.B ((theGOfReturn made h T (theKOfRecord A h.head)).prover A.H) w₀ rc ξ k Rd)
    (k12 : KindShare A (theGOfReturn made h T (theKOfRecord A h.head)) A.H Rel Th .K12) :
    ∀ κ, ¬ Unlaid κ → KindShare A (theGOfReturn made h T (theKOfRecord A h.head)) A.H Rel Th κ := by
  intro κ laysRows
  by_cases isK12 : κ = .K12
  · rw [isK12]
    exact k12
  · exact sharesAtTheKOfRecord_butK12 scope live made h T Rel Th κ laysRows isK12

end AtPublicFiles.AtFiles.HonestTerm.OutputHead

open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open AtPublicFiles.TheSides (theKOfRecord)
open ProofFile.Honest (Sides Owed relAt OnlineProverWithDescription Cells ThreadsP ready onlineProverFromPublicFiles KindShare)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open LPFD.Full (instanceAsPlainRecord XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

local instance (priority := high) sharesAtRecordPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) sharesAtRecordValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) sharesAtRecordDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles} {Wt : Type}

/-- The theorem zeroKnowledgeOnServedRequests_atTheG called at K := theKOfRecord A h.head and at
shares := sharesAtTheKOfRecord_paid. It is conditional on every one of its premises: scope, live,
hr, made, h, T, asks, one, Th, k12, _start, parts and _whole all remain, and so do, inside the
conclusion, the offline sides GK with their three premises. By itself it establishes
ZeroKnowledgeOnServedRequests for no prover. -/
theorem zeroKnowledgeOnServedRequests_atTheKOfRecord_butK12
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {more : List (String × Bool)}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (asks : ∀ t ∈ baseAsks A ++ more, t.2 = true)
    (one : ∃ w₀ rc ξ k R, ready A.F A.B A.H w₀ rc ξ k = .ok R)
    (Th : ∀ w₀ rc ξ, BaseRel files hr w₀ rc ξ → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T (theKOfRecord A h.head)).prover A.H) w₀ rc ξ k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T (theKOfRecord A h.head)).prover A.H) w₀ rc ξ k R)
    (k12 : KindShare A (theGOfReturn made h T (theKOfRecord A h.head)) A.H (BaseRel files hr) Th
      .K12)
    (_start : ∃ z₀, A.F.okStart (instanceAsPlainRecord z₀) = true)
    (parts : Parts files) (_whole : OfflineSidesAreWhole parts) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      ∀ (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
          ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
        (_ : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
        (_ : Owed (keyFileDescription d.source d.numbers d.later) parts.book
          ((cmKey files).proverAt 0 (parts.prover d)) GK.mute
          (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
        (_ : GK.owns = true),
        ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) 0 0
          (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) :=
  zeroKnowledgeOnServedRequests_atTheG scope live hr made h T (theKOfRecord A h.head) asks one Th
    (AtPublicFiles.AtFiles.HonestTerm.OutputHead.sharesAtTheKOfRecord_paid scope live made h T
      (BaseRel files hr) Th k12) _start parts _whole

end VerifiableInference.Compilation

#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.laidAtTheKOfRecord
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.sharesAtTheKOfRecord_butK12
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.sharesAtTheKOfRecord_paid
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_atTheKOfRecord_butK12
