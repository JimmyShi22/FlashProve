-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/TracePremises.lean: eight premises on the trace that H.trace returns, each as a
named proposition, and which of them gives which, each implication as a theorem. They are the
premises of the implications in Johnson/FrontRoad/SessionStopsOfTrace.lean. Seven of them say
something of the traces at requests; the eighth, TraceIsModel, is an equation on the prover's trace
field; it gives TraceOwnRel, and the others as the Limits say.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  AtTied   the common form of five of them: at every tied request of Yes (TiedYes,
      E2E/BridgeJoinAtFiles.lean), wherever H.trace answers a trace tr at the input's matrix and
      written instance, a condition on the input and tr.
  TraceSmall   every entry of tr is below 129 in absolute value.
  TraceServed   tr is theTrace Zp.p.X i x (Johnson/HonestTrace/FullPlanes.lean) at some index i and
      instance x that i serves (ServesAt, Johnson/HonestTrace/Full.lean). Nothing ties i and x to
      the input.
  TracePlain rd   the same at an index that the input's matrix holds
      (VerifiableInference.OnPublicFiles.Flat.Holds, Johnson/Flat/LedgerClaim.lean) and the instance that
      the reader rd reads off the input's written instance.
  TraceThrough trace   the matrix holds an index at which the trace function trace gives tr. It is
      meant beside TraceHinge Zp.p.X trace rd (Johnson/HonestTrace/TraceHinge.lean).
  TraceOwn   of whichever typed request x' in the relation RyesZ Z (E2E/TiedAtFiles.lean) the
      input's instance is written, with the OOD sample at whichever seed: tr is theTrace at each
      index that the matrix holds and that serves x', and at x'.val.
  TraceOwnRel, TraceOwnYes   two forms that are not under AtTied. TraceOwnRel: the like at every
      private input and every typed request in the relation RyesZ Z, at every seed. TraceOwnYes: the
      like at every private input and every typed request of Yes, at the input's own seed.
      TraceIsModel: H.trace is the written function viaIndex (modelTrace Zp.p.X). viaIndex trace:
      through the index that the matrix holds (indexOf, Johnson/Flat/LedgerClaim.lean; by choice, so
      noncomputable), nothing where it holds none. readTrace X rd: it reads the instance by rd and
      answers theTrace X i x where the index serves it, nothing elsewhere; it meets TraceHinge at rd
      (hinge_readTrace) and answers wherever rd reads an instance that the index serves
      (readTrace_served). modelTrace X: readTrace at the reader ProofFile.instOf
      (Johnson/Desc/ProofFile/InstOf.lean); it meets TraceHinge at that reader (hinge_modelTrace)
      and answers at the written instance of every typed request that the index serves
      (modelTrace_served).
  publicAt, served_of_valid, valid_of_holds, instOf_request_inj, holds_one   five facts that the
      implications use. publicAt: publicOf returns Zp.p.X (the field pubOne of AtMg,
      Johnson/P5J/AtMg.lean). served_of_valid: a typed request in the relation RyesZ Z at a matrix
      is served by an index that the matrix holds (ryesZ_iff; ledger_relation_at_protocol_prime,
      Policy/Rel/LedgerRelLaws.lean; lawful_of_read, polCond_of_read, Johnson/Meaning/Scope.lean;
      servesAt_iff_in_scope, Johnson/Goal/HonestTrace/FullInScope.lean; pp_of_reads,
      Johnson/P5J/DecFree.lean). valid_of_holds: the converse, at every matrix that holds the index.
      instOf_request_inj: the writer of a request's instance (LPFD.Full.instanceAsPlainRecord) is one to one in the
      typed request (instOf_at_frame, Johnson/Desc/ProofFile/InstOfTies.lean). holds_one: a matrix
      holds at most one index (holds_unique).
  The implications   cells_of_small: TraceSmall gives the premise hP of sessionStops_of_pinned
      (Johnson/FrontRoad/SessionStopsOfPinned.lean) at the reader cellsC X, at every X, par and list
      of members. small_of_served: TraceServed gives TraceSmall. served_of_plain: TracePlain rd
      gives TraceServed. plain_of_through: TraceHinge and TraceThrough give TracePlain.
      through_of_plain: TracePlain rd gives TraceThrough at readTrace Zp.p.X rd, which meets
      TraceHinge at rd: so TracePlain rd, and TraceHinge with TraceThrough at some trace function,
      are one premise. own_of_plain: TracePlain ProofFile.instOf gives TraceOwn. plain_of_own: TraceOwn
      gives TracePlain ProofFile.instOf. served_of_own: TraceOwn gives TraceServed. own_of_ownRel,
      own_of_ownYes: each of the two wide forms gives TraceOwn. ownYes_of_own: TraceOwn gives
      TraceOwnYes: every typed request of Yes that an index which the matrix holds serves is a tied
      request (validTiedG_atFiles, E2E/BridgeLinkAtFiles.lean). ownYes_of_ownRel_public: TraceOwnRel
      gives TraceOwnYes at every Yes (by valid_of_holds). ownRel_of_model: TraceIsModel gives
      TraceOwnRel. trace_there_of_model: under TraceIsModel the trace is there at every tied request
      of Yes. ownYes_of_ownRel: where Yes is within the relation, TraceOwnRel gives TraceOwnYes.
      ownRel_of_ownYes: TraceOwnYes at Yes := RyesZ Z gives TraceOwnRel; so the two are one premise
      there (recOf_at: the object's OOD sample at a seed is the seed with the answers ansAt).
      ownRel_of_through: TraceHinge at the reader ProofFile.instOf, with a form of TraceThrough at the
      relation, gives TraceOwnRel. throughRel_of_ownRel: TraceOwnRel gives that form back, at
      modelTrace Zp.p.X. through_of_throughRel: that form gives TraceThrough. publicAt,
      served_of_valid, valid_of_holds, small_of_served, plain_of_own, served_of_own, ownYes_of_own,
      ownYes_of_ownRel_public, throughRel_of_ownRel and trace_there_of_model are at public files in
      scope that can be read and pass protocolDataWellFormed, under LaidAt.

How it fits. A tied request is written of some typed request in the relation RyesZ Z already: the
field rel of Tied (Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean), at RyesZ Z in TiedG
(E2E/BridgeLinkAtFiles.lean). plain_of_own and served_of_own use that, with served_of_valid: so that
an index which the matrix holds serves the request is paid from the statement's own "tied". Words
(member, half, part, public and private abort test, stated share):
Johnson/FrontRoad/SessionStopsPinned.lean. Definitions and glue; not one of the release's goal
statements.

Limits.
  Of a prover whose trace field is laid as viaIndex (modelTrace Zp.p.X) by definition, TraceOwnRel
      and TraceOwn are proved (model_meets_ownRel, model_meets_own,
      Johnson/FrontRoad/TracePremisesTests.lean); the others follow there, and no theorem states
      them: TraceOwnYes, TracePlain at rd := ProofFile.instOf, TraceServed and TraceSmall by the
      implications above, under the public premises; TraceThrough at trace := modelTrace Zp.p.X by
      viaIndex_holds. Of TraceOwn: It is proved only of a prover whose trace field is laid so by
      definition, and of no prover whose rows are pinned. It can fail (const_not_own,
      Johnson/FrontRoad/ServedExists.lean). Of no other prover whose trace function answers anywhere
      is any of the seven proved at a Yes that holds of something. That acceptance, or any other
      premise of the implication on index privacy, holds at such a prover is not proved. Each of the
      seven goes one way: the trace function that never answers meets all seven: TraceOwnRel and
      TraceOwnYes by none_meets_ownRel and none_meets_ownYes (in that file), the five under AtTied
      by inspection, not proved. It does not meet TraceIsModel where an index serves a typed request
      (none_fails_model).
  Each of the eight binds and reads the hidden index: as H.trace's argument; the five under AtTied
      in TiedYes; of the seven all but TraceSmall and TraceServed in Holds; TraceIsModel in indexOf.
      TraceIsModel asks more of H than TraceOwnRel: it gives it (ownRel_of_model), and where an
      index serves a typed request the converse fails (none_meets_ownRel, none_fails_model,
      Johnson/FrontRoad/TracePremisesTests.lean).
  The converses that are proved: plain_of_own, ownYes_of_own, through_of_plain, throughRel_of_ownRel
      and, at Yes := RyesZ Z, ownRel_of_ownYes. That TraceSmall does not give TraceServed, and that
      TraceServed does not give TraceOwn, are not proved here. That TraceOwnYes does not give
      TraceOwnRel follows from two theorems of Johnson/FrontRoad/TracePremisesTests.lean
      (ownYes_at_nothing, const_fails_ownRel): under the public premises, at Yes := nothing, at a
      prover whose trace function answers the constant trace 129 at a served typed request. No one
      theorem states it; that such a request exists is servedTyped_exists
      (Johnson/FrontRoad/ServedExists.lean).
  In TracePlain and plain_of_through rd is free: at a reader that yields one instance at every input
      the instance is not tied to the input (hinge_one_request, in that file).
  The full size alone: theTrace, ServesAt, TraceHinge and ProofFile.instOf stand at the reference sizes,
      and the reader cellsC numbers the segments at twelve groups, whatever X's own number of groups
      is. theTrace is noncomputable.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.SessionStopsOfPinned
import Johnson.HonestTrace.DigitsAtTrace
import Johnson.HonestTrace.TraceHinge
import Johnson.Goal.HonestTrace.FullPlanesInScope
import Johnson.Goal.HonestTrace.FullInScope
import Johnson.Flat.LedgerClaim
import Johnson.Meaning.Scope
import Johnson.P5J.DecFree
import Johnson.Top.H.TargetAtPolicy
import Policy.Rel.LedgerRelLaws
import Johnson.Desc.ProofFile.InstOfTies
import E2E.ItemsZero
import Johnson.Flat.ThreeFull

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull)
open OnBytes.Params (Lines missedInTheChecks clog2)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (Tr cellsC cellsSmall_cellOf ServesAt theTrace meetsAll_theTrace
  servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_tracePremises : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_tracePremises {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- A matrix holds at most one index. -/
theorem holds_one {m : FullSizeMatrix} {i i' : Cm.Idx} (h : VerifiableInference.OnPublicFiles.Flat.Holds m i)
    (h' : VerifiableInference.OnPublicFiles.Flat.Holds m i') : i = i' :=
  VerifiableInference.OnPublicFiles.Flat.holds_unique le_rfl le_rfl h h'

/-- The writer of a request's instance is one to one in the typed request. -/
theorem instOf_request_inj {z z' : XF × RecFull}
    (h : LPFD.Full.instanceAsPlainRecord z = LPFD.Full.instanceAsPlainRecord z') : z.1 = z'.1 := by
  have e := congrArg ProofFile.instOf h
  rw [ProofFile.instOf_at_frame, ProofFile.instOf_at_frame] at e
  exact Subtype.ext (Option.some.inj e)

/-- A trace function on matrices, made of a trace function on indices: through the index that the
matrix holds; nothing where it holds none. -/
def viaIndex {Xi : Type} (trace : Cm.Idx → Xi → Option Tr) (m : FullSizeMatrix) (ξ : Xi) : Option Tr :=
  (VerifiableInference.OnPublicFiles.Flat.indexOf m).bind fun i => trace i ξ

/-- **Wherever viaIndex trace answers, the matrix holds an index at
which trace gives that answer.** -/
theorem viaIndex_holds {Xi : Type} (trace : Cm.Idx → Xi → Option Tr) {m : FullSizeMatrix} {ξ : Xi} {tr : Tr}
    (h : viaIndex trace m ξ = some tr) :
    ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds m i ∧ trace i ξ = some tr := by
  unfold viaIndex at h
  cases hi : VerifiableInference.OnPublicFiles.Flat.indexOf m with
  | none =>
    rw [hi] at h
    cases h
  | some i =>
    rw [hi] at h
    refine ⟨i, ?_, h⟩
    unfold VerifiableInference.OnPublicFiles.Flat.indexOf at hi
    split at hi
    · rename_i hin
      cases hi
      exact hin.choose_spec
    · cases hi

/-- At the matrix of an index, viaIndex trace is trace at that
index. -/
theorem viaIndex_matrixOf {Xi : Type} (trace : Cm.Idx → Xi → Option Tr) (i : Cm.Idx) (ξ : Xi) :
    viaIndex trace (VerifiableInference.OnPublicFiles.Flat.matrixOf i) ξ = trace i ξ := by
  have e := VerifiableInference.OnPublicFiles.Flat.indexOf_eq le_rfl le_rfl
    (VerifiableInference.OnPublicFiles.Flat.holds_matrixOf i)
  exact congrArg (fun o : Option Cm.Idx => o.bind fun i => trace i ξ) e

/-- At a matrix that holds an index, viaIndex trace is trace at that index. -/
theorem viaIndex_of_holds {Xi : Type} (trace : Cm.Idx → Xi → Option Tr) {m : FullSizeMatrix} {i : Cm.Idx}
    (hi : VerifiableInference.OnPublicFiles.Flat.Holds m i) (ξ : Xi) :
    viaIndex trace m ξ = trace i ξ := by
  have e := VerifiableInference.OnPublicFiles.Flat.indexOf_eq le_rfl le_rfl hi
  exact congrArg (fun o : Option Cm.Idx => o.bind fun i => trace i ξ) e

/-- The trace function that reads the instance by rd and answers theTrace where the index serves it;
nothing elsewhere. -/
def readTrace {Xi : Type} (X : OnBytes.Model.Verify.Public) (rd : Xi → Option (Instance ppref))
    (i : Cm.Idx) (ξ : Xi) : Option Tr :=
  open Classical in
  (rd ξ).bind fun x => if ServesAt X i x then some (theTrace X i x) else none

/-- readTrace X rd meets TraceHinge at X and the reader rd. -/
theorem hinge_readTrace {Xi : Type} (X : OnBytes.Model.Verify.Public)
    (rd : Xi → Option (Instance ppref)) : TraceHinge X (readTrace X rd) rd := by
  classical
  intro i ξ ω h
  unfold readTrace at h
  cases hx : rd ξ with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    have h' : (if ServesAt X i x then some (theTrace X i x) else none) = some ω := h
    by_cases hs : ServesAt X i x
    · rw [if_pos hs] at h'
      exact ⟨x, rfl, hs, (Option.some.inj h').symm⟩
    · rw [if_neg hs] at h'
      cases h'

/-- readTrace X rd answers wherever rd reads an instance that the index serves. -/
theorem readTrace_served {Xi : Type} (X : OnBytes.Model.Verify.Public)
    (rd : Xi → Option (Instance ppref)) (i : Cm.Idx) (ξ : Xi) (x : Instance ppref)
    (hx : rd ξ = some x) (T : ServesAt X i x) : readTrace X rd i ξ = some (theTrace X i x) := by
  classical
  unfold readTrace
  rw [hx]
  show (if ServesAt X i x then some (theTrace X i x) else none) = _
  rw [if_pos T]

/-- readTrace at the reader ProofFile.instOf. -/
def modelTrace (X : OnBytes.Model.Verify.Public) : Cm.Idx → ProofFile.Inst → Option Tr :=
  readTrace X ProofFile.instOf

/-- modelTrace X meets TraceHinge at X and the reader ProofFile.instOf. -/
theorem hinge_modelTrace (X : OnBytes.Model.Verify.Public) :
    TraceHinge X (modelTrace X) ProofFile.instOf :=
  hinge_readTrace X ProofFile.instOf

/-- modelTrace X answers at the written instance of every typed request that the index serves. -/
theorem modelTrace_served (X : OnBytes.Model.Verify.Public) (i : Cm.Idx)
    (z : XF × RecFull) (T : ServesAt X i z.1.val) :
    modelTrace X i (LPFD.Full.instanceAsPlainRecord z) = some (theTrace X i z.1.val) :=
  readTrace_served X ProofFile.instOf i _ _ (ProofFile.instOf_at_frame z) T

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)

/-- At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: publicOf returns
Zp.p.X. -/
theorem publicAt (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X :=
  (AtMg.of_olderK scope hr L (atPlanOk_of_laid Z Zp Np cF scope live hr L)).pubOne

/-- **At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: a typed request that
is in the relation RyesZ Z at a matrix is served by an index that the matrix holds.** -/
theorem served_of_valid (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (m : FullSizeMatrix) (x' : XF) (h : RyesZ Z m x') :
    ∃ i : Cm.Idx, VerifiableInference.OnPublicFiles.Flat.Holds m i ∧ ServesAt Zp.p.X i x'.val := by
  have hX := publicAt Z Zp Np cF scope hr live L
  obtain rfl := pp_of_reads Z hr
  obtain ⟨i, hi, T, hT⟩ := ((ryesZ_iff Z m x').1 h).2
  exact ⟨i, hi, (servesAt_iff_in_scope scope hr hX i x'.val).2
    ((Policy.ledger_relation_at_protocol_prime _ (OnBytes.Road.L5.lawful_of_read hr) _
      (OnBytes.Road.L5.polCond_of_read hr) i x'.val).1 T hT)⟩

/-- **The converse: at the same public files, a typed request that an index serves is in the
relation RyesZ Z at every matrix that holds that index.** -/
theorem valid_of_holds (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (m : FullSizeMatrix) (i : Cm.Idx) (x' : XF) (hi : VerifiableInference.OnPublicFiles.Flat.Holds m i)
    (T : ServesAt Zp.p.X i x'.val) : RyesZ Z m x' := by
  have hX := publicAt Z Zp Np cF scope hr live L
  obtain rfl := pp_of_reads Z hr
  have V := (servesAt_iff_in_scope scope hr hX i x'.val).1 T
  exact (ryesZ_iff Z m x').2 ⟨⟨i, hi⟩, i, hi, _, Policy.ledger_sub _ _ _ _ _
    ((Policy.ledger_relation_at_protocol_prime _ (OnBytes.Road.L5.lawful_of_read hr) _
      (OnBytes.Road.L5.polCond_of_read hr) i x'.val).2 V)⟩

section Wide
variable {X₀ Xh : Type} (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- **A premise's form, at the whole relation.** At every private input w, every typed request x' in
the relation RyesZ Z at w's matrix, every OOD seed s and every index i that the matrix holds and
that serves x': where H.trace answers at the instance written of x' and the OOD sample at s, it
answers theTrace Zp.p.X i x'.val. It does not name Yes. -/
def TraceOwnRel : Prop :=
  ∀ (w : WZ Z) (x' : XF) (s : (protocolAtFiles Z).OutOfDomainSeed) (i : Cm.Idx) (tr : Tr), RyesZ Z w.1 x' →
    VerifiableInference.OnPublicFiles.Flat.Holds w.1 i → ServesAt Zp.p.X i x'.val →
    H.trace w.1 (LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s))) = some tr →
    tr = theTrace Zp.p.X i x'.val

/-- **A premise's form, at the requests of Yes.** At every private input w, every typed request x'
of Yes at w's matrix and every index i that the matrix holds and that serves x': where H.trace
answers at the instance written of x' and the OOD sample at w's own seed, it answers theTrace Zp.p.X
i x'.val. -/
def TraceOwnYes (Yes : FullSizeMatrix → XF → Prop) : Prop :=
  ∀ (w : WZ Z) (x' : XF) (i : Cm.Idx) (tr : Tr), Yes w.1 x' →
    VerifiableInference.OnPublicFiles.Flat.Holds w.1 i → ServesAt Zp.p.X i x'.val →
    H.trace w.1 (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) = some tr →
    tr = theTrace Zp.p.X i x'.val

/-- The object's OOD sample at a seed is the seed with the OOD answers ansAt. -/
theorem recOf_at (i : FullSizeMatrix) (r : (protocolAtFiles Z).EncodingRandomness) (s : (protocolAtFiles Z).OutOfDomainSeed) :
    (protocolAtFiles Z).recOf i r s = (s, ansAt (AZ Z) PadZ (holdZ Z) i r s) := by
  show (s, (protocolAtFiles Z).honestOutOfDomainAnswer i r s) = _
  rw [ans_obj]
  rfl

/-- Where Yes is within the relation, TraceOwnRel gives TraceOwnYes. -/
theorem ownYes_of_ownRel (Yes : FullSizeMatrix → XF → Prop) (hY : ∀ m x', Yes m x' → RyesZ Z m x')
    (h : TraceOwnRel Z Zp H) : TraceOwnYes Z Zp H Yes := by
  intro w x' i tr hy hi T htr
  rw [recOf_at] at htr
  exact h w x' w.2.2 i tr (hY _ _ hy) hi T htr

/-- TraceOwnYes at Yes := RyesZ Z gives TraceOwnRel: in TraceOwnYes the private input, and so its
seed, is bound by "for all". -/
theorem ownRel_of_ownYes (h : TraceOwnYes Z Zp H (RyesZ Z)) : TraceOwnRel Z Zp H := by
  intro w x' s i tr hx hi T htr
  refine h (w.1, w.2.1, s) x' i tr hx hi T ?_
  rw [recOf_at]
  exact htr

/-- **TraceOwnRel, from TraceHinge at the reader ProofFile.instOf**: hh: trace meets TraceHinge at Zp.p.X
and ProofFile.instOf; hH: at a typed request in the relation, where H.trace answers, the matrix holds an
index at which trace gives that answer. -/
theorem ownRel_of_through (trace : Cm.Idx → ProofFile.Inst → Option Tr)
    (hh : TraceHinge Zp.p.X trace ProofFile.instOf)
    (hH : ∀ (w : WZ Z) (x' : XF) (s : (protocolAtFiles Z).OutOfDomainSeed) (tr : Tr), RyesZ Z w.1 x' →
      H.trace w.1 (LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s))) = some tr →
      ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧
        trace i (LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s))) = some tr) :
    TraceOwnRel Z Zp H := by
  intro w x' s i tr hx hi _ htr
  obtain ⟨i', hi', e⟩ := hH w x' s tr hx htr
  obtain ⟨x, hxr, -, e'⟩ := hh i' _ tr e
  rw [ProofFile.instOf_at_frame] at hxr
  obtain rfl := Option.some.inj hxr
  obtain rfl := holds_one hi hi'
  exact e'

/-- **A premise's form: the prover's trace field is the written function viaIndex (modelTrace
Zp.p.X)**: it reads the index that the matrix holds and the instance off the written instance, and
where the index serves the instance it answers theTrace Zp.p.X at them; nothing elsewhere. An
equation on one field of H. It binds every matrix and every written instance and reads both; it
assumes of no request that it is in the relation, served or small. -/
def TraceIsModel : Prop :=
  ∀ (m : FullSizeMatrix) (ξ : ProofFile.Inst), H.trace m ξ = viaIndex (modelTrace Zp.p.X) m ξ

/-- TraceIsModel gives TraceOwnRel. -/
theorem ownRel_of_model (h : TraceIsModel Z Zp H) : TraceOwnRel Z Zp H :=
  ownRel_of_through Z Zp H (modelTrace Zp.p.X) (hinge_modelTrace Zp.p.X)
    fun w x' s tr _ htr => viaIndex_holds (modelTrace Zp.p.X) ((h w.1 _).symm.trans htr)

end Wide

variable {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)

/-- The common form: at every tied request of Yes, wherever H.trace answers a trace tr at the
input's matrix and written instance, the condition φ of the private input, the request and tr. -/
def AtTied (φ : WZ Z → XF × RecFull → Tr → Prop) : Prop :=
  ∀ (n : ℕ) (w : WZ Z) (a : XF × RecFull),
    TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a) →
    ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr → φ w a tr

/-- **A premise's form**: at every tied request of Yes, every entry of the trace that H.trace
returns is below 129 in absolute value. -/
def TraceSmall : Prop :=
  AtTied Z Zp Np cF run₂ run₃ B G H Yes fun _ _ tr => ∀ k m r c, |tr k m r c| < 129

/-- **A premise's form**: at every tied request of Yes, the trace that H.trace returns is theTrace
Zp.p.X i x at some index i and instance x that i serves. Nothing ties i and x to the input. -/
def TraceServed : Prop :=
  AtTied Z Zp Np cF run₂ run₃ B G H Yes fun _ _ tr =>
    ∃ (i : Cm.Idx) (x : Instance ppref), ServesAt Zp.p.X i x ∧ tr = theTrace Zp.p.X i x

/-- **A premise's form**: the same at an index that the input's matrix holds and the instance that
rd reads off the input's written instance. rd is free. -/
def TracePlain (rd : ProofFile.Inst → Option (Instance ppref)) : Prop :=
  AtTied Z Zp Np cF run₂ run₃ B G H Yes fun w a tr =>
    ∃ (i : Cm.Idx) (x : Instance ppref), VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧
      rd (LPFD.Full.instanceAsPlainRecord a) = some x ∧ ServesAt Zp.p.X i x ∧ tr = theTrace Zp.p.X i x

/-- **A premise's form**: at every tied request of Yes, the input's matrix holds an index at which
the trace function trace gives the trace that H.trace returns. -/
def TraceThrough (trace : Cm.Idx → ProofFile.Inst → Option Tr) : Prop :=
  AtTied Z Zp Np cF run₂ run₃ B G H Yes fun w a tr =>
    ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧ trace i (LPFD.Full.instanceAsPlainRecord a) = some tr

/-- **A premise's form**: at every tied request of Yes, of whichever typed request x' in the
relation RyesZ Z the input's instance is written, with the OOD sample at whichever seed s: the trace
that H.trace returns is theTrace Zp.p.X i x'.val at each index i that the matrix holds and that
serves x'. -/
def TraceOwn : Prop :=
  AtTied Z Zp Np cF run₂ run₃ B G H Yes fun w a tr =>
    ∀ (s : (protocolAtFiles Z).OutOfDomainSeed) (x' : XF) (i : Cm.Idx),
      LPFD.Full.instanceAsPlainRecord a = LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s)) →
      RyesZ Z w.1 x' → VerifiableInference.OnPublicFiles.Flat.Holds w.1 i → ServesAt Zp.p.X i x'.val →
      tr = theTrace Zp.p.X i x'.val

/-- TraceSmall gives the premise hP of sessionStops_of_pinned at the reader cellsC X: at every X,
every par and every list of members. -/
theorem cells_of_small {S Cl : Type} (h : TraceSmall Z Zp Np cF run₂ run₃ B G H Yes)
    (X : OnBytes.Model.Verify.Public) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (bs : List (Block S Cl)) (n : ℕ) (w : WZ Z) (a : XF × RecFull)
    (ht : TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a)) (tr : Tr)
    (htr : H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr) :
    CellsSmallAt par (cellsC X) bs ⟨w.1, w.2.1, LPFD.Full.instanceAsPlainRecord a, tr⟩ :=
  fun _ _ P _ => cellsSmall_cellOf (h n w a ht tr htr) P.1 P.2

/-- At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: TraceServed gives
TraceSmall. -/
theorem small_of_served (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (h : TraceServed Z Zp Np cF run₂ run₃ B G H Yes) :
    TraceSmall Z Zp Np cF run₂ run₃ B G H Yes := by
  intro n w a ht tr htr
  obtain ⟨i, x, T, rfl⟩ := h n w a ht tr htr
  exact (meetsAll_theTrace scope hr (publicAt Z Zp Np cF scope hr live L) T).small

/-- TracePlain rd gives TraceServed. The clauses on Holds and on rd are dropped. -/
theorem served_of_plain (rd : ProofFile.Inst → Option (Instance ppref))
    (h : TracePlain Z Zp Np cF run₂ run₃ B G H Yes rd) :
    TraceServed Z Zp Np cF run₂ run₃ B G H Yes := by
  intro n w a ht tr htr
  obtain ⟨i, x, -, -, T, e⟩ := h n w a ht tr htr
  exact ⟨i, x, T, e⟩

/-- TraceHinge at Zp.p.X and TraceThrough give TracePlain. -/
theorem plain_of_through (trace : Cm.Idx → ProofFile.Inst → Option Tr)
    (rd : ProofFile.Inst → Option (Instance ppref)) (hh : TraceHinge Zp.p.X trace rd)
    (h : TraceThrough Z Zp Np cF run₂ run₃ B G H Yes trace) :
    TracePlain Z Zp Np cF run₂ run₃ B G H Yes rd := by
  intro n w a ht tr htr
  obtain ⟨i, hi, e⟩ := h n w a ht tr htr
  obtain ⟨x, hx, T, e'⟩ := hh i _ tr e
  exact ⟨i, x, hi, hx, T, e'⟩

/-- TracePlain at the reader ProofFile.instOf gives TraceOwn. -/
theorem own_of_plain (h : TracePlain Z Zp Np cF run₂ run₃ B G H Yes ProofFile.instOf) :
    TraceOwn Z Zp Np cF run₂ run₃ B G H Yes := by
  intro n w a ht tr htr s x' i e _ hi _
  obtain ⟨i₀, x, hi₀, hrd, -, etr⟩ := h n w a ht tr htr
  rw [e, ProofFile.instOf_at_frame] at hrd
  obtain rfl := Option.some.inj hrd
  obtain rfl := holds_one hi hi₀
  exact etr

/-- **At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: TraceOwn gives
TracePlain at the reader ProofFile.instOf.** That an index which the matrix holds serves the request comes
from the field rel of Tied, by served_of_valid. -/
theorem plain_of_own (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (h : TraceOwn Z Zp Np cF run₂ run₃ B G H Yes) :
    TracePlain Z Zp Np cF run₂ run₃ B G H Yes ProofFile.instOf := by
  intro n w a ht tr htr
  obtain ⟨s, x', e, hx'⟩ := ht.2.rel
  obtain ⟨i, hi, T⟩ := served_of_valid Z Zp Np cF scope hr live L w.1 x' hx'
  exact ⟨i, x'.val, hi, by rw [e, ProofFile.instOf_at_frame], T, h n w a ht tr htr s x' i e hx' hi T⟩

/-- At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: TraceOwn gives
TraceServed. -/
theorem served_of_own (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (h : TraceOwn Z Zp Np cF run₂ run₃ B G H Yes) : TraceServed Z Zp Np cF run₂ run₃ B G H Yes :=
  served_of_plain Z Zp Np cF run₂ run₃ B G H Yes ProofFile.instOf
    (plain_of_own Z Zp Np cF run₂ run₃ B G H Yes scope hr live L h)

/-- TraceOwnRel gives TraceOwn. -/
theorem own_of_ownRel (h : TraceOwnRel Z Zp H) : TraceOwn Z Zp Np cF run₂ run₃ B G H Yes := by
  intro n w a _ tr htr s x' i e hx hi T
  rw [e] at htr
  exact h w x' s i tr hx hi T htr

/-- TraceOwnYes gives TraceOwn: the typed request of which the instance is written is the one of
Yes, since the writer is one to one in the typed request. -/
theorem own_of_ownYes (h : TraceOwnYes Z Zp H Yes) : TraceOwn Z Zp Np cF run₂ run₃ B G H Yes := by
  intro n w a ht tr htr s x' i e _ hi T
  obtain ⟨⟨x₁, hy, e₁⟩, -⟩ := ht
  have ex : x' = x₁ := instOf_request_inj (e.symm.trans e₁)
  subst ex
  rw [e₁] at htr
  exact h w x' i tr hy hi T htr

/-- **At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: TraceOwn gives
TraceOwnYes.** Every typed request of Yes that an index which the matrix holds serves is in the
relation (valid_of_holds), and every such request is a tied request, at every private input
(validTiedG_atFiles, E2E/BridgeLinkAtFiles.lean; its premise by itemsZero_of_data,
E2E/ItemsZero.lean). -/
theorem ownYes_of_own (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (h : TraceOwn Z Zp Np cF run₂ run₃ B G H Yes) : TraceOwnYes Z Zp H Yes := by
  intro w x' i tr hy hi T htr
  have hx : RyesZ Z w.1 x' := valid_of_holds Z Zp Np cF scope hr live L w.1 i x' hi T
  have ht : TiedYes Z Zp Np cF run₂ run₃ B G H Yes 0 w
      (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) :=
    ⟨⟨x', hy, rfl⟩, validTiedG_atFiles Z Zp Np cF run₂ run₃ B G H
      (AtPublicFiles.AtZero.itemsZero_of_data L.data) 0 w.1 w.2.1 w.2.2 x' trivial trivial hx⟩
  exact h 0 w (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2) ht tr htr w.2.2 x' i
    (congrArg (fun ρ => LPFD.Full.instanceAsPlainRecord (x', ρ)) (recOf_at Z w.1 w.2.1 w.2.2)) hx hi T

/-- At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: TraceOwnRel gives
TraceOwnYes at every Yes. -/
theorem ownYes_of_ownRel_public (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (h : TraceOwnRel Z Zp H) : TraceOwnYes Z Zp H Yes := by
  intro w x' i tr _ hi T htr
  rw [recOf_at] at htr
  exact h w x' w.2.2 i tr (valid_of_holds Z Zp Np cF scope hr live L w.1 i x' hi T) hi T htr

/-- TracePlain rd gives TraceThrough at the trace function readTrace Zp.p.X rd, which meets
TraceHinge at rd (hinge_readTrace). So TracePlain rd, and TraceHinge with TraceThrough at some trace
function, are one premise. -/
theorem through_of_plain (rd : ProofFile.Inst → Option (Instance ppref))
    (h : TracePlain Z Zp Np cF run₂ run₃ B G H Yes rd) :
    TraceThrough Z Zp Np cF run₂ run₃ B G H Yes (readTrace Zp.p.X rd) := by
  intro n w a ht tr htr
  obtain ⟨i, x, hi, hrd, T, e⟩ := h n w a ht tr htr
  exact ⟨i, hi, (readTrace_served Zp.p.X rd i _ x hrd T).trans (congrArg some e.symm)⟩

/-- The second premise of ownRel_of_through gives TraceThrough: a tied request is written of a typed
request in the relation (the field rel of Tied). -/
theorem through_of_throughRel (trace : Cm.Idx → ProofFile.Inst → Option Tr)
    (hH : ∀ (w : WZ Z) (x' : XF) (s : (protocolAtFiles Z).OutOfDomainSeed) (tr : Tr), RyesZ Z w.1 x' →
      H.trace w.1 (LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s))) = some tr →
      ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧
        trace i (LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s))) = some tr) :
    TraceThrough Z Zp Np cF run₂ run₃ B G H Yes trace := by
  intro n w a ht tr htr
  obtain ⟨s, x', e, hx'⟩ := ht.2.rel
  rw [e] at htr ⊢
  exact hH w x' s tr hx' htr

/-- At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: TraceOwnRel gives the
second premise of ownRel_of_through back, at the trace function modelTrace Zp.p.X. -/
theorem throughRel_of_ownRel (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (h : TraceOwnRel Z Zp H) (w : WZ Z) (x' : XF) (s : (protocolAtFiles Z).OutOfDomainSeed) (tr : Tr)
    (hx : RyesZ Z w.1 x')
    (htr : H.trace w.1 (LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s))) =
      some tr) :
    ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧
      modelTrace Zp.p.X i (LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s))) =
        some tr := by
  obtain ⟨i, hi, T⟩ := served_of_valid Z Zp Np cF scope hr live L w.1 x' hx
  refine ⟨i, hi, ?_⟩
  rw [h w x' s i tr hx hi T htr]
  exact modelTrace_served Zp.p.X i _ T

/-- **At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: under TraceIsModel
the trace is there at every tied request of Yes.** -/
theorem trace_there_of_model (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (h : TraceIsModel Z Zp H) (n : ℕ) (w : WZ Z) (a : XF × RecFull)
    (ht : TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a)) :
    ∃ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr := by
  obtain ⟨s, x', e, hx'⟩ := ht.2.rel
  obtain ⟨i, hi, T⟩ := served_of_valid Z Zp Np cF scope hr live L w.1 x' hx'
  refine ⟨theTrace Zp.p.X i x'.val, ?_⟩
  rw [h, viaIndex_of_holds (modelTrace Zp.p.X) hi, e]
  exact modelTrace_served Zp.p.X i _ T

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_tracePremises
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_tracePremises
#print axioms OnBytes.FrontRoad.holds_one
#print axioms OnBytes.FrontRoad.instOf_request_inj
#print axioms OnBytes.FrontRoad.viaIndex
#print axioms OnBytes.FrontRoad.viaIndex_holds
#print axioms OnBytes.FrontRoad.viaIndex_matrixOf
#print axioms OnBytes.FrontRoad.viaIndex_of_holds
#print axioms OnBytes.FrontRoad.readTrace
#print axioms OnBytes.FrontRoad.hinge_readTrace
#print axioms OnBytes.FrontRoad.readTrace_served
#print axioms OnBytes.FrontRoad.modelTrace
#print axioms OnBytes.FrontRoad.hinge_modelTrace
#print axioms OnBytes.FrontRoad.modelTrace_served
#print axioms OnBytes.FrontRoad.publicAt
#print axioms OnBytes.FrontRoad.served_of_valid
#print axioms OnBytes.FrontRoad.valid_of_holds
#print axioms OnBytes.FrontRoad.TraceOwnRel
#print axioms OnBytes.FrontRoad.TraceOwnYes
#print axioms OnBytes.FrontRoad.recOf_at
#print axioms OnBytes.FrontRoad.ownYes_of_ownRel
#print axioms OnBytes.FrontRoad.ownRel_of_ownYes
#print axioms OnBytes.FrontRoad.ownRel_of_through
#print axioms OnBytes.FrontRoad.TraceIsModel
#print axioms OnBytes.FrontRoad.ownRel_of_model
#print axioms OnBytes.FrontRoad.AtTied
#print axioms OnBytes.FrontRoad.TraceSmall
#print axioms OnBytes.FrontRoad.TraceServed
#print axioms OnBytes.FrontRoad.TracePlain
#print axioms OnBytes.FrontRoad.TraceThrough
#print axioms OnBytes.FrontRoad.TraceOwn
#print axioms OnBytes.FrontRoad.cells_of_small
#print axioms OnBytes.FrontRoad.small_of_served
#print axioms OnBytes.FrontRoad.served_of_plain
#print axioms OnBytes.FrontRoad.plain_of_through
#print axioms OnBytes.FrontRoad.own_of_plain
#print axioms OnBytes.FrontRoad.plain_of_own
#print axioms OnBytes.FrontRoad.served_of_own
#print axioms OnBytes.FrontRoad.own_of_ownRel
#print axioms OnBytes.FrontRoad.own_of_ownYes
#print axioms OnBytes.FrontRoad.ownYes_of_own
#print axioms OnBytes.FrontRoad.ownYes_of_ownRel_public
#print axioms OnBytes.FrontRoad.through_of_plain
#print axioms OnBytes.FrontRoad.through_of_throughRel
#print axioms OnBytes.FrontRoad.throughRel_of_ownRel
#print axioms OnBytes.FrontRoad.trace_there_of_model
