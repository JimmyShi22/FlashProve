-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/ProverThroughSpec.lean: definitions and statements only. A prover of the frame
(Prover, Johnson/Desc/ProofFile/Honest/Frame.lean) at an index type W₀' and a randomness type Rc',
read through a partial map ix : W₀ → Option W₀' on the index and a map rd : Rc → Rc' on the
randomness, as a prover at W₀ and Rc: proverThrough. Its parts are made by Part.lift (that file).
The pinned part of the smallness test is its own image; so the pin's clauses on the halves
(PinHalvesAt, Johnson/FrontRoad/PinPublicSpec.lean), and the pin, go over from a prover's halves to
their images; and a condition on the trace function of the prover at W₀' (below: the elder prover)
gives CellsOwnAt (Johnson/FrontRoad/CellsOwnAtSpec.lean) of the image. Proved in
Johnson/FrontRoad/ProverThrough.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  ixOr ix dflt   the total map that the parts want: ix's value, and dflt where ix answers none.
  localThrough, commonThrough   the input of a prover's side, in the first or the second chain and
      in the shared chain, with the index read by ixOr ix dflt and the randomness by rd; instance,
      trace and key stay.
  partThrough, partThroughShared, halfThrough, halfThroughShared   a part as Part.lift makes it,
      with both of lift's maps on the input the map above, and the own state untouched; a half with
      its place kept and each part so made.
  proverThrough ix dflt rd d H'   all eleven fields. stored, trace and inRange read ix itself: where
      ix answers none they answer none, none and false. key, own₀ and ownShared₀ stay. dummy is the
      argument d. first, shared and second are the images of H''s halves. meet is given the shared
      chain's end with its input read through.
  Spec.lift_quietStop, Spec.smallStop_through, Spec.pinned_part_through   the quiet part with a
      private abort test h, lifted with the own state untouched, is the quiet part with the test h
      after the map; smallStop cells P does not see the maps; so the pinned part is its own image.
  Spec.find_through   the first half at a place among the images is the image of the first half at
      that place.
  Spec.halves_through, Spec.pin_through   PinHalvesAt par cells hs bs gives PinHalvesAt of the
      images; and RowsPinned par cells hs bs gives RowsPinned of the images.
  Spec.through_at_some, Spec.ixOr_at_some   where ix w = some i, stored, trace and inRange at w are
      H''s at i (stored at rd rc), and ixOr ix dflt w is i.
  Spec.through_at_none, Spec.tests_refuse_at_none   where ix w = none the three are none, none and
      false; so readyTests refuses at w: if no earlier test does, the range test; it reads no trace.
  Spec.readyShared_refuses_at_none, Spec.ready_refuses_at_none   so readyShared and ready, which
      both call readyTests first, refuse at w.
  TraceCellsAt X cells' trace   a condition on a trace function at the index type Cm.Idx: wherever
      it answers tr at an index i and bytes that read as an instance x which i serves, cells' tr is
      cellsC X (theTrace X i x).
  Spec.traceCells_of_answers   the stronger form, in which the function answers only at bytes that
      read as an instance that i serves, gives it.
  Spec.cellsOwn_through   at the letters of the implications on sessionStops (the index type FullSizeMatrix; ix
      := Flat.indexOf, Johnson/Flat/LedgerClaim.lean): TraceCellsAt Zp.p.X cells' of the elder
      prover's trace function gives CellsOwnAt cells' of the image, at all rows G, every Yes, every
      dflt, rd and d.
  Spec.model_traceCells, Spec.through_trace_modelAt   two controls. Under ReadsAs the trace function
      that answers e of the model's trace meets TraceCellsAt; the image, at ix := Flat.indexOf, of a
      prover with that trace field has the trace field modelAt X e, of which Spec.ownAt_speaks says,
      under the four public premises, at X := Zp.p.X and Yes := RyesZ Z, that it answers at some
      tied request.
  Spec.const_not_traceCells   a negative test: under the four public premises a trace function that
      answers everywhere one trace of which cells' yields cellsC Zp.p.X of the constant trace 129
      does not meet TraceCellsAt.
  Spec.through_trace_viaIndex, Spec.matrixOf_in_range   two small facts at ix := Flat.indexOf. At
      the model's type of traces the image's trace field is viaIndex of the elder's; at d :=
      Flat.matrixOf j the image's range test says of d what the elder's says of j.
  Spec.index_stop_moves, Spec.default_is_read   a negative test and a control, at types Rc, Xi and
      Tr' that each have a member. At the index type Bool and the map that turns the index over, the
      quiet part whose test fires just where the index is true is not its own image. At the map that
      answers none everywhere and dflt := true, that part's image fires at the index false: the
      default is read.

How it fits. By their author's account, not read here, the library's honest rows for the whole
description stand at the index type Cm.Idx and a randomness type of their own, while the
implications on the field sessionStops (PremWDebts, E2E/BridgeDebts.lean) take rows and a prover at
FullSizeMatrix and (protocolAtFiles Z).EncodingRandomness. These definitions read a prover of the first sort as one of the second. provG
(E2E/BridgeJoinAtFiles.lean) overwrites five of the eleven fields: first, shared and second by the
rows G, stored and key by the committer's. So the pins of these implications, which stand at provG's
first and second, read G's rows and not the image's own halves: Spec.halves_through and
Spec.pin_through reach them only at rows G whose parts are the images. Of an image under provG six
fields are left: trace, inRange, dummy, own₀, ownShared₀ and meet; stored's fence is gone: the
committer's columns answer at a matrix whether or not ix answers there. Words (member, half, part,
public and private abort test, stated share): Johnson/FrontRoad/SessionStopsPinned.lean. Not one of
the release's goal statements.

Limits.
  SEVEN FIELDS NEVER READ THE DEFAULT; FOUR ARE GIVEN IT. stored, trace and inRange take the index
      and read ix itself; key, dummy, own₀ and ownShared₀ take no index. first, shared, second and
      meet are given ixOr ix dflt w. Every part's input, every private abort test of the first and
      the second chain (the shared chain's has nothing to read: its type is Empty) and meet are
      given it at every w, the default included; whether a part reads it is the part's own matter:
      the pinned part does not (Spec.smallStop_through). Of a part, takes, spends, carries, the
      public abort test and the two shares are kept as they are. Inside run
      (Johnson/Desc/ProofFile/Honest/Frame.lean) no part and no meet is reached at a w where ix
      answers none: by inspection, not proved, run calls ready first, and ready refuses there
      (Spec.ready_refuses_at_none); readyShared, which reads no trace, refuses there too
      (Spec.readyShared_refuses_at_none), since readyTests does (Spec.tests_refuse_at_none). That
      the default is read elsewhere is Spec.default_is_read. The sessions' strategies
      (Johnson/Desc/ProofFile/Honest/StratC.lean) reach the steps and meet through ready and
      readyShared too (by inspection). hidB (Johnson/Desc/ProofFile/Honest/Record.lean) and silentAt
      (Johnson/Desc/ProofFile/Honest/Rule.lean) hand the input to the private abort tests with no
      call of ready: they begin with the trace function's answer, which is none where ix answers
      none (Spec.through_at_none): there the fence is the field trace. Any other statement that
      speaks of a part or of meet at a letter w, without one of these in front, meets the default
      unfenced.
  d is an argument: ready refuses unless inRange is true of it, so the caller owes ix d = some j
      with H'.inRange j = true. At ix := Flat.indexOf and d := Flat.matrixOf j the first is had
      (Spec.matrixOf_in_range); the second is the elder prover's.
  That ready returns at the image just where it returns at H' is not stated here.
  No prover is named. Whether any halves meet PinHalvesAt, is not said. TraceCellsAt is met by a
      written trace function (Spec.model_traceCells), and idly by one that never answers. No rows G
      are made of the images: a row wants letters beside its parts (Lettered,
      Johnson/Desc/ProofFile/Honest/Rule.lean).
  The images go one way: from PinHalvesAt of the images nothing is drawn on the source halves. rd is
      free and tied to nothing: at provG the stored tables are the committer's at rc itself, while
      rows made of images are given rd rc; nothing here asks that the two fit. rd need not be onto,
      and need not keep a measure: a law over the randomness that is drawn through an image would
      have to say what rd does to the measure. Nothing here is such a law.
  The index, which is part of the prover's private input, is a letter of CellsOwnAt and of
      TraceCellsAt: neither is a condition on public data.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.PinPublicSpec
import Johnson.FrontRoad.CellsOwnAtSpec

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
open OnBytes.HonestTrace (Tr cellsC matsOf cellsSmall_cellOf ServesAt theTrace meetsAll_theTrace
  servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready Placed Local Common Cells State)
open ProofFile.Honest.K8 (smallStop)
open ProofFile.Honest.K9 (quietStop)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_proverThroughSpec : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_proverThroughSpec {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

section
variable {W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')

/-- The total map that the parts want: ix's value; dflt where ix answers none. -/
def ixOr (w : W₀) : W₀' := (ix w).getD dflt

/-- The input of a prover's side in the first or the second chain, read through the two maps. -/
def localThrough (v : Local W₀ Rc Xi Tr') : Local W₀' Rc' Xi Tr' :=
  ⟨ixOr ix dflt v.w₀, rd v.rc, v.x, v.trace⟩

/-- The input of a prover's side in the shared chain, read through the two maps. -/
def commonThrough (v : Common W₀ Rc Ky) : Common W₀' Rc' Ky :=
  ⟨ixOr ix dflt v.w₀, rd v.rc, v.key⟩

/-- A part of the first or the second chain, read through the two maps: Part.lift with both of its
maps on the input localThrough, and the own state untouched. -/
def partThrough (p : ProofFile.Honest.Part (Local W₀' Rc' Xi Tr') (Local W₀' Rc' Xi Tr') X) :
    ProofFile.Honest.Part (Local W₀ Rc Xi Tr') (Local W₀ Rc Xi Tr') X :=
  p.lift (localThrough ix dflt rd) (localThrough ix dflt rd) id fun _ y => y

/-- A part of the shared chain, read through the two maps. Its private abort test has no argument to
be given: the type is Empty on both sides. -/
def partThroughShared (p : ProofFile.Honest.Part Empty (Common W₀' Rc' Ky) X₀) :
    ProofFile.Honest.Part Empty (Common W₀ Rc Ky) X₀ :=
  p.lift id (commonThrough ix dflt rd) id fun _ y => y

/-- A half with its place kept and each part read through the two maps. -/
def halfThrough (g : Placed (Local W₀' Rc' Xi Tr') (Local W₀' Rc' Xi Tr') X) :
    Placed (Local W₀ Rc Xi Tr') (Local W₀ Rc Xi Tr') X :=
  ⟨g.place, g.parts.map (partThrough ix dflt rd)⟩

/-- The same in the shared chain. -/
def halfThroughShared (g : Placed Empty (Common W₀' Rc' Ky) X₀) :
    Placed Empty (Common W₀ Rc Ky) X₀ :=
  ⟨g.place, g.parts.map (partThroughShared ix dflt rd)⟩

/-- **A prover read through a partial map on its index and a map on its randomness.** stored, trace
and inRange read ix itself: where ix answers none they answer none, none and false. The parts and
meet want a total map and read ixOr ix dflt: A SILENT DEFAULT AT THE INDEX. The three fields fence
nothing by themselves: a caller must ask one of them first. ready and readyShared ask inRange, which
is false there; hidB and silentAt ask trace, which answers none there. d: the named element of the
new range: an argument; ready refuses unless inRange is true of it. -/
def proverThrough (d : W₀) (H' : Prover W₀' Rc' Xi Ky Tr' X₀ X) : Prover W₀ Rc Xi Ky Tr' X₀ X :=
  { stored := fun w rc a b => (ix w).bind fun i => H'.stored i (rd rc) a b
    trace := fun w ξ => (ix w).bind fun i => H'.trace i ξ
    key := H'.key
    inRange := fun w => ((ix w).map H'.inRange).getD false
    dummy := d
    own₀ := H'.own₀
    ownShared₀ := H'.ownShared₀
    first := H'.first.map (halfThrough ix dflt rd)
    shared := H'.shared.map (halfThroughShared ix dflt rd)
    second := H'.second.map (halfThrough ix dflt rd)
    meet := fun x t => H'.meet x (t.narrow (commonThrough ix dflt rd) id) }

end

/-- **The quiet part with a private abort test, lifted with the own state untouched, is the quiet
part with that test after the map.** -/
def Spec.lift_quietStop : Prop :=
  ∀ {V V' W W' X : Type} (see : V → V') (wit : W → W')
    (h : V' → List Fmt.Drawn → List Fmt.Drawn → Option String) (sh : ProofFile.Honest.Odds),
    (quietStop h sh : ProofFile.Honest.Part V' W' X).lift see wit id (fun _ y => y) =
      quietStop (fun v => h (see v)) sh

/-- **The smallness test's private abort test does not see the two maps.** -/
def Spec.smallStop_through : Prop :=
  ∀ {W₀ W₀' Rc Rc' Xi Tr' : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')
    (cells : Tr' → Cells) (P : Par × List (ℕ × String × ℕ)) (v : Local W₀ Rc Xi Tr'),
    smallStop cells P (localThrough ix dflt rd v) = smallStop cells P v

/-- **So the pinned part is its own image.** -/
def Spec.pinned_part_through : Prop :=
  ∀ {W₀ W₀' Rc Rc' Xi Tr' X : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')
    (cells : Tr' → Cells) (P : Par × List (ℕ × String × ℕ)) (sh : ProofFile.Honest.Odds),
    partThrough ix dflt rd
        (quietStop (smallStop cells P) sh :
          ProofFile.Honest.Part (Local W₀' Rc' Xi Tr') (Local W₀' Rc' Xi Tr') X) =
      quietStop (smallStop cells P) sh

/-- **The first half at a place among the images is the image of the first half at that place.** -/
def Spec.find_through : Prop :=
  ∀ {W₀ W₀' Rc Rc' Xi Tr' X : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')
    (hs : List (Placed (Local W₀' Rc' Xi Tr') (Local W₀' Rc' Xi Tr') X)) (a : Place),
    ((hs.map (halfThrough ix dflt rd)).find? fun g => g.place == a) =
      (hs.find? fun g => g.place == a).map (halfThrough ix dflt rd)

/-- **The pin's clauses on the halves go over to the images.** -/
def Spec.halves_through : Prop :=
  ∀ {S Cl W₀ W₀' Rc Rc' Xi Tr' X : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')
    (par : Place → Option (Par × List (ℕ × String × ℕ))) (cells : Tr' → Cells)
    (hs : List (Placed (Local W₀' Rc' Xi Tr') (Local W₀' Rc' Xi Tr') X)) (bs : List (Block S Cl)),
    PinHalvesAt par cells hs bs → PinHalvesAt par cells (hs.map (halfThrough ix dflt rd)) bs

/-- **So does the pin.** -/
def Spec.pin_through : Prop :=
  ∀ {S Cl W₀ W₀' Rc Rc' Xi Tr' X : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')
    (par : Place → Option (Par × List (ℕ × String × ℕ))) (cells : Tr' → Cells)
    (hs : List (Placed (Local W₀' Rc' Xi Tr') (Local W₀' Rc' Xi Tr') X)) (bs : List (Block S Cl)),
    RowsPinned par cells hs bs → RowsPinned par cells (hs.map (halfThrough ix dflt rd)) bs

/-- **Where ix answers an index, the three fenced fields are the elder prover's at it.** -/
def Spec.through_at_some : Prop :=
  ∀ {W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')
    (d : W₀) (H' : Prover W₀' Rc' Xi Ky Tr' X₀ X) (w : W₀) (i : W₀'), ix w = some i →
    (∀ rc a b, (proverThrough ix dflt rd d H').stored w rc a b = H'.stored i (rd rc) a b) ∧
      (∀ ξ, (proverThrough ix dflt rd d H').trace w ξ = H'.trace i ξ) ∧
      (proverThrough ix dflt rd d H').inRange w = H'.inRange i

/-- **Where ix answers none, they are none, none and false.** -/
def Spec.through_at_none : Prop :=
  ∀ {W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')
    (d : W₀) (H' : Prover W₀' Rc' Xi Ky Tr' X₀ X) (w : W₀), ix w = none →
    (∀ rc a b, (proverThrough ix dflt rd d H').stored w rc a b = none) ∧
      (∀ ξ, (proverThrough ix dflt rd d H').trace w ξ = none) ∧
      (proverThrough ix dflt rd d H').inRange w = false

/-- **Where ix answers an index, the parts' total map answers it too.** -/
def Spec.ixOr_at_some : Prop :=
  ∀ {W₀ W₀' : Type} (ix : W₀ → Option W₀') (dflt : W₀') (w : W₀) (i : W₀'), ix w = some i →
    ixOr ix dflt w = i

/-- **So the tests that read neither a challenge nor the instance refuse there**: if no earlier test
does, the range test; they read no trace. -/
def Spec.tests_refuse_at_none : Prop :=
  ∀ {W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')
    (d : W₀) (H' : Prover W₀' Rc' Xi Ky Tr' X₀ X) (F : VerifiableInference.Desc.FileDescription Xi)
    (B : ProverCoinCounts) (w : W₀), ix w = none →
    ProofFile.Honest.readyTests F B (proverThrough ix dflt rd d H') w ≠ .ok ()

/-- **So the shared chain is not prepared there either**: readyShared, which reads no trace,
refuses. -/
def Spec.readyShared_refuses_at_none : Prop :=
  ∀ {W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')
    (d : W₀) (H' : Prover W₀' Rc' Xi Ky Tr' X₀ X) (F : VerifiableInference.Desc.FileDescription Xi)
    (B : ProverCoinCounts) (w : W₀) (rc : Rc) (ky : Ky) (c₀ : ProofFile.Honest.Purse B.shared), ix w = none →
    ∀ l, ProofFile.Honest.readyShared F B (proverThrough ix dflt rd d H') w rc ky c₀ ≠ .ok l

/-- **So ready refuses there.** -/
def Spec.ready_refuses_at_none : Prop :=
  ∀ {W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X : Type} (ix : W₀ → Option W₀') (dflt : W₀') (rd : Rc → Rc')
    (d : W₀) (H' : Prover W₀' Rc' Xi Ky Tr' X₀ X) (F : VerifiableInference.Desc.FileDescription Xi)
    (B : ProverCoinCounts) (w : W₀) (rc : Rc) (x : Xi) (c : Coins B), ix w = none →
    ∀ R, ready F B (proverThrough ix dflt rd d H') w rc x c ≠ .ok R

/-- **A condition on a trace function at the index type Cm.Idx**: wherever it answers a trace tr at
an index i and written bytes ξ that read as an instance x which i serves, the reader cells' yields
of tr the cells of the model's trace: cellsC X (theTrace X i x). Where ξ reads as no instance, or i
does not serve it, nothing is asked. The index, which is part of the prover's private input, is a
letter of the condition. -/
def TraceCellsAt {Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells' : Tr' → Cells)
    (trace : Cm.Idx → ProofFile.Inst → Option Tr') : Prop :=
  ∀ i ξ tr x, trace i ξ = some tr → ProofFile.instOf ξ = some x → ServesAt X i x →
    cells' tr = cellsC X (theTrace X i x)

/-- A stronger form gives it: wherever the function answers, ξ reads as an instance that i serves,
and the cells are the model's. -/
def Spec.traceCells_of_answers : Prop :=
  ∀ {Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells' : Tr' → Cells)
    (trace : Cm.Idx → ProofFile.Inst → Option Tr'),
    (∀ i ξ tr, trace i ξ = some tr → ∃ x, ProofFile.instOf ξ = some x ∧ ServesAt X i x ∧
      cells' tr = cellsC X (theTrace X i x)) →
    TraceCellsAt X cells' trace

/-- **At the letters of the implications on sessionStops: TraceCellsAt of the elder prover's trace
function gives CellsOwnAt of the image.** At all rows G, every Yes, every dflt, rd and d. -/
def Spec.cellsOwn_through : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Rc' Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H' : Prover Cm.Idx Rc' ProofFile.Inst TableKey Tr' X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)
    (dflt : Cm.Idx) (rd : (protocolAtFiles Z).EncodingRandomness → Rc') (d : FullSizeMatrix) (cells' : Tr' → Cells),
    TraceCellsAt Zp.p.X cells' H'.trace →
    CellsOwnAt Z Zp Np cF run₂ run₃ B G
      (proverThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd d H') Yes cells'

/-- A control; it counts as no goal. Under ReadsAs X cells' e the trace function that answers e of
the model's trace meets TraceCellsAt. -/
def Spec.model_traceCells : Prop :=
  ∀ {Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells' : Tr' → Cells) (e : Tr → Tr'),
    ReadsAs X cells' e → TraceCellsAt X cells' fun i ξ => (modelTrace X i ξ).map e

/-- A negative test; it counts as no goal. **At public files in scope that can be read and pass
protocolDataWellFormed, under LaidAt: a trace function that answers everywhere one trace t₀ of which cells' yields
cellsC Zp.p.X of the constant trace 129 does not meet TraceCellsAt.** -/
def Spec.const_not_traceCells : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {Tr' : Type} (cells' : Tr' → Cells) (t₀ : Tr')
    (_h₀ : cells' t₀ = cellsC Zp.p.X fun _ _ _ _ => 129),
    ¬ TraceCellsAt Zp.p.X cells' fun _ _ => some t₀

/-- A control; it counts as no goal. The image, at ix := Flat.indexOf, of a prover whose trace field
is that function has the trace field modelAt X e: the field of Spec.model_meets_ownAt,
Spec.ownAt_speaks and Spec.cellsOwn_speaks. -/
def Spec.through_trace_modelAt : Prop :=
  ∀ {Rc Rc' Ky Tr' X₀ X : Type} (Xp : OnBytes.Model.Verify.Public) (e : Tr → Tr')
    (H₀ : Prover Cm.Idx Rc' ProofFile.Inst Ky Tr' X₀ X) (dflt : Cm.Idx) (rd : Rc → Rc') (d : FullSizeMatrix),
    (proverThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd d
      { H₀ with trace := fun i ξ => (modelTrace Xp i ξ).map e }).trace = modelAt Xp e

/-- At the model's type of traces the image's trace field, at ix := Flat.indexOf, is viaIndex of the
elder prover's. -/
def Spec.through_trace_viaIndex : Prop :=
  ∀ {Rc Rc' Xi Ky X₀ X : Type} (H' : Prover Cm.Idx Rc' Xi Ky Tr X₀ X) (dflt : Cm.Idx)
    (rd : Rc → Rc') (d : FullSizeMatrix),
    (proverThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd d H').trace =
      viaIndex H'.trace

/-- At d := Flat.matrixOf j the image's range test says of d what the elder prover's says of j. -/
def Spec.matrixOf_in_range : Prop :=
  ∀ {Rc Rc' Xi Ky Tr' X₀ X : Type} (H' : Prover Cm.Idx Rc' Xi Ky Tr' X₀ X) (dflt : Cm.Idx)
    (rd : Rc → Rc') (j : Cm.Idx),
    (proverThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd
      (VerifiableInference.OnPublicFiles.Flat.matrixOf j) H').inRange
        (VerifiableInference.OnPublicFiles.Flat.matrixOf j) = H'.inRange j

/-- A negative test; it counts as no goal. At the index type Bool and the map that turns the index
over, the quiet part whose private abort test fires just where the index is true is not its own
image. -/
def Spec.index_stop_moves : Prop :=
  ∀ {Rc Xi Tr' X : Type} (sh : ProofFile.Honest.Odds) (rc : Rc) (x : Xi) (tr : Tr'),
    partThrough (fun b : Bool => some (!b)) false (fun r : Rc => r)
        (quietStop (fun u _ _ => if u.w₀ then some "" else none) sh :
          ProofFile.Honest.Part (Local Bool Rc Xi Tr') (Local Bool Rc Xi Tr') X) ≠
      quietStop (fun u _ _ => if u.w₀ then some "" else none) sh

/-- A control; it counts as no goal. **The default is read.** At the map that answers none
everywhere and dflt := true, the image of the quiet part whose private abort test fires just where
the index is true fires at the index false. -/
def Spec.default_is_read : Prop :=
  ∀ {Rc Xi Tr' X : Type} (sh : ProofFile.Honest.Odds) (rc : Rc) (x : Xi) (tr : Tr'),
    (partThrough (fun _ : Bool => (none : Option Bool)) true (fun r : Rc => r)
        (quietStop (fun u _ _ => if u.w₀ then some "" else none) sh :
          ProofFile.Honest.Part (Local Bool Rc Xi Tr') (Local Bool Rc Xi Tr') X)).hid
      ⟨false, rc, x, tr⟩ [] [] = some ""

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_proverThroughSpec
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_proverThroughSpec
#print axioms OnBytes.FrontRoad.ixOr
#print axioms OnBytes.FrontRoad.localThrough
#print axioms OnBytes.FrontRoad.commonThrough
#print axioms OnBytes.FrontRoad.partThrough
#print axioms OnBytes.FrontRoad.partThroughShared
#print axioms OnBytes.FrontRoad.halfThrough
#print axioms OnBytes.FrontRoad.halfThroughShared
#print axioms OnBytes.FrontRoad.proverThrough
#print axioms OnBytes.FrontRoad.Spec.lift_quietStop
#print axioms OnBytes.FrontRoad.Spec.smallStop_through
#print axioms OnBytes.FrontRoad.Spec.pinned_part_through
#print axioms OnBytes.FrontRoad.Spec.find_through
#print axioms OnBytes.FrontRoad.Spec.halves_through
#print axioms OnBytes.FrontRoad.Spec.pin_through
#print axioms OnBytes.FrontRoad.Spec.through_at_some
#print axioms OnBytes.FrontRoad.Spec.through_at_none
#print axioms OnBytes.FrontRoad.Spec.ready_refuses_at_none
#print axioms OnBytes.FrontRoad.Spec.cellsOwn_through
#print axioms OnBytes.FrontRoad.Spec.index_stop_moves
#print axioms OnBytes.FrontRoad.TraceCellsAt
#print axioms OnBytes.FrontRoad.Spec.traceCells_of_answers
#print axioms OnBytes.FrontRoad.Spec.model_traceCells
#print axioms OnBytes.FrontRoad.Spec.through_trace_modelAt
#print axioms OnBytes.FrontRoad.Spec.through_trace_viaIndex
#print axioms OnBytes.FrontRoad.Spec.matrixOf_in_range
#print axioms OnBytes.FrontRoad.Spec.ixOr_at_some
#print axioms OnBytes.FrontRoad.Spec.tests_refuse_at_none
#print axioms OnBytes.FrontRoad.Spec.default_is_read
#print axioms OnBytes.FrontRoad.Spec.readyShared_refuses_at_none
#print axioms OnBytes.FrontRoad.Spec.const_not_traceCells
