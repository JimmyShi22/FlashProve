-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/CarryThroughSpec.lean: definitions and statements only. The implication
Spec.sessionStops_of_cellsOwn (Johnson/FrontRoad/CellsOwnAtSpec.lean), at mats := matsOf Zp.p.X,
with its premises on rows and prover carried back to a prover H' at the index type Cm.Idx and a
randomness type Rc' of its own: the prover is H''s image (proverThrough,
Johnson/FrontRoad/ProverThroughSpec.lean) at ix := Flat.indexOf, and the rows G are any rows whose
first and second chain, forgotten to halves, are the images of H''s halves. Of the implication's
five premises on rows and prover, four then follow from conditions on H' at its own types; ready's
return (hR) stays a premise at the image. Proved in Johnson/FrontRoad/CarryThrough.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  imageAt dflt rd d H'   short for proverThrough Flat.indexOf dflt rd d H'.
  bareRow g, bareSides F Bk H   for a control: a row made of a half, with a candidate simulator that
      reads nothing beside each part and the four letters of the row (A, B, On, bud) laid as «true»;
      the rows so made of a prover's three chains.
  Spec.pins_of_elder   at all public files in scope that can be read, under LaidAt: where provG's
      first and second halves are the images of H''s, PinHalvesAt of H'.first at the description's
      own parameters and the list matsOf, and PinHalvesAt of H'.second at the par that names none,
      give the two pins h₁ and h₃ of the implication.
  Spec.frame_free_of_elder   where provG's first halves are the images of H''s and no half of
      H'.first stands at a place of the kind frame, no row of G.first does: hn.
  Spec.sessionStops_of_elder   the implication: under the four public premises, at rows G whose
      first and second chain, forgotten to halves, are the images: from hR at the image, and of H'
      at its own types: no half of its first chain at a place of the kind frame; PinHalvesAt twice,
      as above; TraceCellsAt Zp.p.X cells' of its trace function: the end of
      Spec.sessionStops_of_cellsOwn, at G and the image.
  Spec.bare_forgets, Spec.bare_rows_are_images   two controls. The rows bareSides F Bk H, forgotten
      to halves, are H's own halves, in all three chains. So at G := bareSides of the image the two
      premises on G of the statements above hold: such rows exist.

How it fits. By their author's account, not read here, the library's honest rows for the whole
description stand at Cm.Idx and a randomness type of their own. These statements say what would
suffice, of such a prover at its own types, for four of the five premises on rows and prover of the
implication that is named for the field sessionStops (PremWDebts, E2E/BridgeDebts.lean); beside them
stand the two equations on the rows G and hR, neither at that prover's own types. CellsOwnAt of the
image stands here together with the two pins and hn, at the same rows and reader. The pins at provG
are had from PinHalvesAt of H''s halves only with the two equations on G: Spec.pin_through alone
does not reach them. Words (member, half, part, public and private abort test, stated share):
Johnson/FrontRoad/SessionStopsPinned.lean. Not one of the release's goal statements.

Limits.
  No prover is named here. The four conditions are met together by one written control, which is not
      the honest prover: a thin prover that has the twenty-five pinned parts alone and sends nothing
      (Spec.thin_meets_four, Johnson/FrontRoad/ThinProverSpec.lean; with hR and the equations on G:
      Johnson/FrontRoad/ThinElderSpec.lean). No prover that sends a message is known at which they
      hold together.
  hR IS NOT CARRIED: it stays a premise on ready at provG of G and the image. That ready returns
      there just where it returns at H' is not stated.
  THE ROWS ARE A LETTER. PremWDebts asks its fields at one G. It asks them at one prover too, which
      on this road is the image. Whether its other fields can be had at the image, and at rows whose
      parts are the images, is not said. bareSides is a control alone: its letters are laid as
      «true» and its simulators read nothing: no other field is meant to be had at it.
  Of G the end of Spec.sessionStops_of_elder, and the two statements in front of it, read the first
      and the second chain's places and parts alone. Its premise hR reads the shared chain's places
      and parts too: ready tests them (readyTests, sharedSteps). The simulators, the four letters
      and the falls are read nowhere.
  dflt and rd are free; rd is tied to nothing. d is bound by hR: ready refuses unless the image's
      range test is true of d, so Flat.indexOf d answers an index at which H''s range test is true.
      All limits of Johnson/FrontRoad/ProverThroughSpec.lean on the default hold here. No statement
      here speaks of a part or of meet of the image at the input's index. By inspection, not proved:
      under the two conditions PinHalvesAt and the condition on the kind frame the end reads neither
      dflt nor rd: the pinned part is its own image, and no other private abort test that
      chainStopAt asks fires.
  The limits of Johnson/FrontRoad/CellsOwnAtSpec.lean hold here, but for its sentence that nothing
      carries a prover from the one index type to the other: here a prover is carried; rows are not.
      No value is given for the bound. Nothing here goes over the randomness: the measure in
      HidSmall (E2E/BridgePrivacy.lean) is over the verifier's messages alone, and rc is bound by
      «for all». The index, which is part of the prover's private input, is a letter of
      TraceCellsAt.
  At public files that do not meet the public premises the statements that have them hold idly.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.ProverThroughSpec

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
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready Placed Local Common Cells Lettered)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_carryThroughSpec : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_carryThroughSpec {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- Short for the image at ix := Flat.indexOf. -/
abbrev imageAt {Rc Rc' Xi Ky Tr' X₀ X : Type} (dflt : Cm.Idx) (rd : Rc → Rc') (d : FullSizeMatrix)
    (H' : Prover Cm.Idx Rc' Xi Ky Tr' X₀ X) : Prover FullSizeMatrix Rc Xi Ky Tr' X₀ X :=
  proverThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd d H'

/-- For a control: a row made of a half: beside each part a candidate simulator that reads nothing;
the row's four letters laid as «true». -/
def bareRow {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} (g : Placed V W Y) : Lettered Bk S Cl V W Y Pb :=
  { place := g.place
    row := g.parts.map fun p => (p, ProofFile.Honest.quietSim ⟨g.place, 0⟩ 1)
    A := fun _ _ _ _ => True
    B := fun _ _ _ _ => True
    On := fun _ _ _ _ => True
    bud := fun _ _ _ => True }

/-- For a control: the rows so made of a prover's three chains. -/
def bareSides {Xi W₀ Rc Ky Tr' X₀ X : Type} (F : VerifiableInference.Desc.FileDescription Xi) (Bk : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr' X₀ X) : Sides F Bk W₀ Rc Ky Tr' X₀ X :=
  { first := H.first.map bareRow, shared := H.shared.map bareRow, second := H.second.map bareRow }

/-- **The two pins from the elder prover's halves**: at all public files in scope that can be read,
under LaidAt, where provG's first and second halves are the images of H''s. -/
def Spec.pins_of_elder : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {Rc' Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H' : Prover Cm.Idx Rc' ProofFile.Inst TableKey Tr' X₀ Xh)
    (dflt : Cm.Idx) (rd : (protocolAtFiles Z).EncodingRandomness → Rc') (d : FullSizeMatrix)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (_hG₁ : (provG Z Zp Np cF B G (imageAt dflt rd d H')).first =
      H'.first.map (halfThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd))
    (_hG₃ : (provG Z Zp Np cF B G (imageAt dflt rd d H')).second =
      H'.second.map (halfThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd))
    (cells' : Tr' → ProofFile.Honest.Cells)
    (_p₁ : PinHalvesAt (parOwn Zp (matsOf Zp.p.X)) cells' H'.first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (_p₃ : PinHalvesAt (fun _ => none) cells' H'.second (descZ Zp Np cF).second.blocksInOrder),
    RowsPinned (parOwn Zp (matsOf Zp.p.X)) cells'
        (provG Z Zp Np cF B G (imageAt dflt rd d H')).first
        (descZ Zp Np cF).first.blocksInOrder.dropLast ∧
      RowsPinned (fun _ => none) cells' (provG Z Zp Np cF B G (imageAt dflt rd d H')).second
        (descZ Zp Np cF).second.blocksInOrder

/-- **hn from the elder prover's halves.** -/
def Spec.frame_free_of_elder : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {Rc' Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H' : Prover Cm.Idx Rc' ProofFile.Inst TableKey Tr' X₀ Xh)
    (dflt : Cm.Idx) (rd : (protocolAtFiles Z).EncodingRandomness → Rc') (d : FullSizeMatrix)
    (_hG₁ : (provG Z Zp Np cF B G (imageAt dflt rd d H')).first =
      H'.first.map (halfThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd))
    (_hn' : ∀ g ∈ H'.first, g.place.kind ≠ KindName.frame),
    ∀ L ∈ G.first, L.place.kind ≠ KindName.frame

/-- **The implication with four of its five premises on rows and prover carried back to the
prover's own types.** The prover is H''s image at ix := Flat.indexOf; the rows G are any whose first
and second chain, forgotten to halves, are the images of H''s halves. hR stays a premise at the
image. The end is that of Spec.sessionStops_of_cellsOwn. -/
def Spec.sessionStops_of_elder : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Rc' Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H' : Prover Cm.Idx Rc' ProofFile.Inst TableKey Tr' X₀ Xh)
    (dflt : Cm.Idx) (rd : (protocolAtFiles Z).EncodingRandomness → Rc') (d : FullSizeMatrix)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (_hG₁ : (provG Z Zp Np cF B G (imageAt dflt rd d H')).first =
      H'.first.map (halfThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd))
    (_hG₃ : (provG Z Zp Np cF B G (imageAt dflt rd d H')).second =
      H'.second.map (halfThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd))
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh}
    (_hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G (imageAt dflt rd d H')) w₀ rc x₀ k₀ =
      .ok R)
    (_hn' : ∀ g ∈ H'.first, g.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (cells' : Tr' → ProofFile.Honest.Cells)
    (_p₁ : PinHalvesAt (parOwn Zp (matsOf Zp.p.X)) cells' H'.first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (_p₃ : PinHalvesAt (fun _ => none) cells' H'.second (descZ Zp Np cF).second.blocksInOrder)
    (_hT : TraceCellsAt Zp.p.X cells' H'.trace)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop),
    HidSmall (famG Z Zp Np cF run₂ run₃ B G (imageAt dflt rd d H'))
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G (imageAt dflt rd d H') Yes ok Gs n w
        (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-(((linesAt Zp).sec : ℝ) + (clog2 (linesAt Zp).slots : ℝ) +
        (clog2 (max 1 (batchesAt Zp)) : ℝ) +
        (clog2 (plannedCopies (linesAt Zp) (oneTimeAt Zp) (columnsFirstAt Zp)) : ℝ)))) + 0)

/-- A control; it counts as no goal. The rows bareSides F Bk H, forgotten to halves as Sides.prover
forgets them, are H's own halves, in all three chains, whatever prover they are laid into. -/
def Spec.bare_forgets : Prop :=
  ∀ {Xi W₀ Rc Ky Tr' X₀ X : Type} (F : VerifiableInference.Desc.FileDescription Xi) (Bk : ProverCoinCounts)
    (H H₁ : Prover W₀ Rc Xi Ky Tr' X₀ X),
    ((bareSides F Bk H).prover H₁).first = H.first ∧
      ((bareSides F Bk H).prover H₁).shared = H.shared ∧
      ((bareSides F Bk H).prover H₁).second = H.second

/-- A control; it counts as no goal. At G := bareSides of the image, provG's first and second halves
are the images of H''s: rows as the statements above ask them exist. -/
def Spec.bare_rows_are_images : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {Rc' Tr' X₀ Xh : Type} (B : ProverCoinCounts) (H' : Prover Cm.Idx Rc' ProofFile.Inst TableKey Tr' X₀ Xh)
    (dflt : Cm.Idx) (rd : (protocolAtFiles Z).EncodingRandomness → Rc') (d : FullSizeMatrix),
    (provG Z Zp Np cF B (bareSides (descZ Zp Np cF) B (imageAt dflt rd d H'))
        (imageAt dflt rd d H')).first =
      H'.first.map (halfThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd) ∧
    (provG Z Zp Np cF B (bareSides (descZ Zp Np cF) B (imageAt dflt rd d H'))
        (imageAt dflt rd d H')).second =
      H'.second.map (halfThrough VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_carryThroughSpec
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_carryThroughSpec
#print axioms OnBytes.FrontRoad.imageAt
#print axioms OnBytes.FrontRoad.bareRow
#print axioms OnBytes.FrontRoad.bareSides
#print axioms OnBytes.FrontRoad.Spec.pins_of_elder
#print axioms OnBytes.FrontRoad.Spec.frame_free_of_elder
#print axioms OnBytes.FrontRoad.Spec.sessionStops_of_elder
#print axioms OnBytes.FrontRoad.Spec.bare_forgets
#print axioms OnBytes.FrontRoad.Spec.bare_rows_are_images
