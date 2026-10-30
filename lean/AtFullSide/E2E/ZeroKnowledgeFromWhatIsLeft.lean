-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeft.lean

This file sorts the premises of zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines
(AtFullSide/T3/TheOneAtTheG.lean) into those that it proves from theorems of other files and those
that remain. The remaining ones are collected in the structure WhatIsLeftOfT3, and the conclusion of
that theorem is derived from it. Honest verifier; interactive oracle proof; served requests.

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
  * TheThreadsHalf h hr (AtFullSide/Honest/TheOneObject.lean) is the first half of the structure
    from which completeness is proved. A tied request (TiedRequest) is an instance written from a
    served request and the out-of-domain sample of a private input. A tied run (TiedRun) is a run of
    the prover at such an instance at which the function ready returns.

Main statements
  baseRel_is_tied
      Premises: scope, hr and h. Conclusion: every input of the relation BaseRel files hr is a tied
      request, at a private input whose table's coins are those of the input.
  asks_at_the_base
      Premises: made and h. Conclusion: the one test in baseAsks A is true, by sides_are_whole. It
      proves the premise asks with no further test.
  one_of_the_half
      Premises: scope, made and a value of TheThreadsHalf h hr. Conclusion: ready returns at some
      input, by a_tied_run_exists. It proves the premise one.
  start_of_the_half
      The same premises. Conclusion: A.F.okStart accepts some instance, by the field startFit at a
      tied run. It proves the premise _start.
  WhatIsLeftOfT3
      A structure, meant as a premise. Its fields are half (a value of TheThreadsHalf h hr), rows (a
      value of KindRows), shares (a KindShare for each of the thirteen kinds at these), parts (the
      offline prover's arguments), a (a bound), offlineSimulator, and the three conditions
      offlineTable, offline and offlineStops on the offline prover.
  zeroKnowledgeFromWhatIsLeft
      Premises: scope, live, hr, made, h, and left : WhatIsLeftOfT3 scope hr made h. Conclusion:
      ZeroKnowledgeOnServedRequests files hr at the provers HonestProvers.ofThreeProvers (honestProvers
      files left.parts), with the definition's three bounds offlineStops, linkStops and onlineStops
      at left.a, 0 and 2^-174. The arguments T and Th of the theorem called are TheLetters.parts and
      TheThreadsHalf.threadsAtRelation at left.half.

Limits
  * This file adds no statement on what a proof hides beyond ZeroKnowledgeOnServedRequests, as
    defined in VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean.
  * A statement of this form alone is also met by a prover that stops publicly or sends fixed
    messages. AtFullSide/E2E/BothEndsAtOneTerm.lean states it beside completeness for the provers at
    thePartsAt files.
  * WhatIsLeftOfT3 is a premise, and this file does not show that it has a value; scope, live, hr,
    made and h are premises too. The files ZeroKnowledgeFromWhatIsLeftAtRecord.lean,
    ZeroKnowledgeFromTheOfflineLines.lean and ZeroKnowledgeFromTheRows.lean of this folder supply
    them step by step.
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
  * AtFullSide/T3/TheOneAtTheG.lean: zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines.
  * AtFullSide/Honest/TheCrossing.lean: TheThreadsHalf.threadsAtRelation.
  * AtFullSide/Honest/TheLetters.lean: TheLetters.parts.
  * AtFullSide/Honest/TheOneObject.lean: a_tied_run_exists, every_served_request_is_tied,
    pursesOf_onto.
  * Johnson/Desc/ProofFile/Honest/K1/Pay/Whole.lean: sides_are_whole.
-/
import AtFullSide.Honest.TheCrossing
import AtFullSide.T3.TheOneAtTheG

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
open AtPublicFiles.TheSides (KindRows)
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

variable {files : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}

/-- At any configuration C, recOf returns the pair of its argument s : C.Seed and the answers ansC C
i r s. By unfolding. -/
theorem sample_is_seed_and_answers {C : _} (F : OnBytes.Flat.Files C) (P : F.Provers) (i : C.I)
    (r : C.Pad × C.Rnd) (s : C.Seed) : (F.withProvers P).recOf i r s = (s, ansC C i r s) := rfl

/-- Every input of BaseRel is a tied request: an instance written from a served request of the index
and the out-of-domain sample of a private input, whose table's coins are those of the input. -/
theorem baseRel_is_tied (scope : InScope files = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles files = .ok pp) (h : HeadAtReturn files A) :
    ∀ w₀ rc x, BaseRel files hr w₀ rc x →
      ∃ n w, w.1 = w₀ ∧ tableCoins files w.2.1 = rc ∧ TiedRequest h hr n w x := by
  rintro w₀ rc x ⟨w, rc', ⟨s, x', hx, hy⟩, rfl, rfl⟩
  have e1 : (protocolAtFiles files).recOf w rc' s = (s, ansC (Cz files) w rc' s) :=
    sample_is_seed_and_answers (filesAt files) (FlashProve.dataAtFiles FlashProve.flashProveData files).P w
      rc' s
  have e2 : ansAt (AZ files) PadZ (holdZ files) = ansC (Cz files) :=
    ansAt_eq (AZ files) PadZ (holdZ files)
  have hx' : x = instanceAsPlainRecord (x', (protocolAtFiles files).recOf w rc' s) := by
    rw [e1, ← e2]
    exact hx
  refine ⟨0, (w, rc', s), rfl, rfl, ?_⟩
  rw [hx']
  exact AtFullSide.Honest.every_served_request_is_tied scope 0 w rc' s x' hy

/-- The premise asks of zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines, with the list more
empty: the one test in baseAsks A is true. -/
theorem asks_at_the_base
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) :
    ∀ t ∈ baseAsks A ++ ([] : List (String × Bool)), t.2 = true := by
  intro t ht
  unfold baseAsks at ht
  rw [List.append_nil, List.mem_singleton] at ht
  subst ht
  exact (ProofFile.Honest.K1.Pay.sides_are_whole matrixInput OnBytes.HonestTrace.Sz.ref
    ProofFile.Honest.openHonest rfl h.head made).1

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

/-- The premise one of that theorem: ready returns at some input. From a value of TheThreadsHalf h
hr, at a tied run. -/
theorem one_of_the_half (scope : InScope files = true) {pp : Inst.Model.ScalesAndPolicy}
    {hr : readFiles files = .ok pp}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    {h : HeadAtReturn files A} (O : TheThreadsHalf h hr) :
    ∃ w₀ rc ξ k R, ready A.F A.B A.H w₀ rc ξ k = .ok R := by
  obtain ⟨r⟩ : Nonempty (protocolAtFiles files).EncodingRandomness := inferInstance
  obtain ⟨e⟩ : Nonempty (protocolAtFiles files).OutOfDomainSeed := inferInstance
  obtain ⟨c, -⟩ := AtFullSide.Honest.pursesOf_onto (default : ProofFile.Honest.Coins A.B)
  obtain ⟨t⟩ := AtFullSide.Honest.a_tied_run_exists scope made O r e c
  refine ⟨t.w.1, tableCoins files t.w.2.1, t.x, pursesOf t.c, t.R, ?_⟩
  rw [(ProofFile.Honest.atPure_at_laid h.head.laid made).2]
  exact t.ready

/-- The premise _start of that theorem: A.F.okStart accepts some instance. From the field startFit
of a value of TheThreadsHalf h hr, at a tied run. -/
theorem start_of_the_half (scope : InScope files = true) {pp : Inst.Model.ScalesAndPolicy}
    {hr : readFiles files = .ok pp}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    {h : HeadAtReturn files A} (O : TheThreadsHalf h hr) :
    ∃ z₀, A.F.okStart (instanceAsPlainRecord z₀) = true := by
  obtain ⟨r⟩ : Nonempty (protocolAtFiles files).EncodingRandomness := inferInstance
  obtain ⟨e⟩ : Nonempty (protocolAtFiles files).OutOfDomainSeed := inferInstance
  obtain ⟨c, -⟩ := AtFullSide.Honest.pursesOf_onto (default : ProofFile.Honest.Coins A.B)
  obtain ⟨t⟩ := AtFullSide.Honest.a_tied_run_exists scope made O r e c
  obtain ⟨-, ⟨x', -, hx⟩, -⟩ := t.tied
  refine ⟨(x', (protocolAtFiles files).recOf t.w.1 t.w.2.1 t.w.2.2), ?_⟩
  rw [(ProofFile.Honest.atPure_at_laid h.head.laid made).2, ← hx]
  exact O.startFit t

/-- The premises of zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines that this file does not
prove. A definition, meant as a premise. -/
structure WhatIsLeftOfT3 (scope : InScope files = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles files = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) where
  /-- A value of the first half of the structure from which completeness is proved. Its parameter
  open₃ gives the argument T; the value itself gives Th and the premise one. -/
  half : TheThreadsHalf h hr
  /-- The rows of the kinds (the argument K). -/
  rows : KindRows baseFilling A.Z A.G
  /-- A KindShare for each of the thirteen kinds, at these rows, at the arguments TheLetters.parts
  of the threads, and at the family of invariants that half gives. -/
  shares : ∀ κ, ¬ Unlaid κ →
    KindShare A (theGOfReturn made h (AtFullSide.Honest.TheLetters.parts h half.open₃) rows) A.H
      (BaseRel files hr)
      (half.threadsAtRelation made
        (theGOfReturn made h (AtFullSide.Honest.TheLetters.parts h half.open₃) rows)
        (theGOfReturn_prover made h (AtFullSide.Honest.TheLetters.parts h half.open₃) rows)
        (baseRel_is_tied scope hr h)) κ
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

/-- ZeroKnowledgeOnServedRequests at left.parts and left.a, from scope, live, hr, made, h and a
value left of WhatIsLeftOfT3. -/
theorem zeroKnowledgeFromWhatIsLeft (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (h : HeadAtReturn files A) (left : WhatIsLeftOfT3 scope hr made h) :
    ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files left.parts))
      left.a 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) :=
  zeroKnowledgeOnServedRequests_atTheG_ofOfflineLines (more := []) scope live hr made h
    (AtFullSide.Honest.TheLetters.parts h left.half.open₃) left.rows (asks_at_the_base made h)
    (one_of_the_half scope made left.half)
    (left.half.threadsAtRelation made _
      (theGOfReturn_prover made h (AtFullSide.Honest.TheLetters.parts h left.half.open₃) left.rows)
      (baseRel_is_tied scope hr h))
    left.shares (start_of_the_half scope made left.half) left.parts left.offlineSimulator
    left.offlineTable left.offline left.offlineStops

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.baseRel_is_tied
#print axioms VerifiableInference.Compilation.asks_at_the_base
#print axioms VerifiableInference.Compilation.one_of_the_half
#print axioms VerifiableInference.Compilation.start_of_the_half
#print axioms VerifiableInference.Compilation.zeroKnowledgeFromWhatIsLeft
