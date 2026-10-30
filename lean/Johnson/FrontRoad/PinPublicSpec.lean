-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/PinPublicSpec.lean: definitions and statements only, on a premise's form and on
public data. The pin (RowsPinned, Johnson/FrontRoad/SessionStopsPinned.lean) is two conditions:
PinPublicAt, on the parameters and the chain's members alone, and PinHalvesAt, on the prover's
halves. At the first chain of the proof file's description without its last member, at the
description's own parameters and the list matsOf (parOwn Zp (matsOf Zp.p.X)), and at the second
chain, at the par that names none, PinPublicAt is a theorem: at the first chain at all public files
in scope that can be read, under LaidAt; at the second chain at all letters. So what is left of the
two pins in sessionStops_of_tiedOwn_matsOf is PinHalvesAt, which says (Spec.halves_first_iff for the
first chain; Spec.halves_none_iff and Spec.second_places_at for the second): at each of the
twenty-five written places k8PlaceAt l of the first chain a half stands, and the first half there
has the one part quietStop (smallStop (cellsC Zp.p.X) P) (windowShare P.1) at the parameters P that
parOwn names; at every other place of the first chain without its last member, and at the four
places of the second chain, if a half stands, no part of the first half there has a private abort
test that fires, and each part's stated share is 0. Proved in Johnson/FrontRoad/PinPublic.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  PinPublicAt par bs   at each member b of bs: where par names parameters P at b's place, the public
      test smallFits P passes and b has the one round round P.1; where par names none, b's place is
      not of the kind K8. These are the clauses of RowsPinned that name no half, word for word.
  PinHalvesAt par cells hs bs   at each member b of bs: where par names P, a half of hs stands at
      b's place and the first half there has the one part quietStop (smallStop cells P) (windowShare
      P.1); where par names none, the clause of SilentAt
      (Johnson/FrontRoad/SecondChainPlacesSpec.lean). These are the other clauses of RowsPinned,
      word for word.
  Spec.pin_iff   general: RowsPinned par cells hs bs holds just where PinPublicAt par bs and
      PinHalvesAt par cells hs bs hold.
  Spec.halves_none_iff   general: at the par that names none PinHalvesAt is SilentAt.
  Spec.pin_first_public   at all public files in scope that can be read, under LaidAt, at every
      mats: at each member of the kind K8 of the first chain without its last member, parOwn Zp mats
      names parameters P, and the member has the one round round P.1.
  Spec.public_first   under the same premises: PinPublicAt (parOwn Zp (matsOf Zp.p.X)) at the first
      chain without its last member.
  Spec.public_second   at all letters: PinPublicAt (fun _ => none) at the second chain. It is
      no_k8_second (Johnson/FrontRoad/SecondChainPlacesSpec.lean); the pin's equivalence at that
      chain is Spec.pin_second_iff, in that file.
  Spec.pin_first_iff   so, under the three premises, at every reader cells and all halves hs:
      RowsPinned (parOwn Zp (matsOf Zp.p.X)) cells hs at the first chain without its last member
      holds just where PinHalvesAt does.
  Spec.halves_first_iff   under the three premises: PinHalvesAt at the first chain, place by place:
      the sentence of the first paragraph as a statement.
  Spec.wrong_rounds_not_public, Spec.unfit_not_public, Spec.short_names_not_public   three negative
      tests. General: at a member at whose place par names P and whose rounds are not the one round
      round P.1, or where smallFits P fails, PinPublicAt fails; so, by Spec.pin_iff, the pin fails
      at all halves. At the description: at the lists matsOf Zp.p.X l without their last members
      PinPublicAt fails.
  Spec.halves_need_no_public   a control, general: PinHalvesAt holds at the one half with the pinned
      part, whatever smallFits and the rounds are: so it has neither of PinPublicAt's clauses.

How it fits. In sessionStops_of_pinned and all that stands on it the premises h₁ and h₃ are
RowsPinned at the first chain without its last member and at the second chain. By its text the pin
holds clauses on public data: if one of them failed at the description's own parameters, the
implications at parOwn would hold idly. Spec.public_first and Spec.public_second say that none fails
at the list matsOf; at another list smallFits can fail (the Limits). Words (member, half, part,
public and private abort test, stated share): Johnson/FrontRoad/SessionStopsPinned.lean. Not one of
the release's goal statements.

Limits.
  Nothing is said of any prover: whether any rows meet PinHalvesAt at the two chains is not said. hR
      and the premise on the cells or on the trace stay premises; no book, rows and prover are known
      at which all premises hold together. No value is given for the bound.
  smallFits is stated here at the list matsOf alone. It holds the list by its length and by nothing
      else: it passes at emptyNames too (Spec.empty_names_fit_and_read_zero,
      Johnson/FrontRoad/CellsAreTraceSpec.lean), so PinPublicAt does not tell matsOf from a list of
      wrong names. At a free mats it can fail (Spec.short_names_do_not_fit,
      Johnson/FrontRoad/CellsAreTraceSpec.lean). So Spec.public_first and Spec.pin_first_iff stand
      at matsOf; Spec.pin_first_public, which leaves smallFits out, at every mats.
  The reading follows from scope (inScope_readFiles,
      Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean); it is kept as a premise so that the
      statements fit their callers. At public files that do not meet scope, the reading and LaidAt
      the five statements that have them as premises hold idly. That these are met together is
      proved of one stored set of files, VerifierAndGoals.storedPublicFiles, in the side library (premises_met_at_full,
      AtFullSide/Top/LaidAtFull.lean).
  The shared chain is not treated: the pin does not speak of it. The first chain's last member, of
      the kind frame, is not treated: the implications take the list without it. By inspection
      PinPublicAt would hold with it too, since parOwn names none at a place of that kind.
  The full size alone.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.CellsAreTraceSpec
import Johnson.FrontRoad.SecondChainPlacesSpec

set_option autoImplicit false

namespace OnBytes.FrontRoad
open VerifierAndGoals (PublicFiles InScope readFiles)
open P5J (TS LaidAt)
open OnBytes.Maker (WholeD)
open AtPublicFiles.AtFiles (descZ)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par round)
open OnBytes.HonestTrace (matsOf)
open ProofFile.Honest (Placed Local Cells)
open ProofFile.Honest.K8 (smallStop smallFits windowShare)
open ProofFile.Honest.K9 (quietStop)

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/-- **The pin's clauses on public data**: at each member b of bs: where par names parameters P at
b's place, the public test smallFits P passes and b has the one round round P.1; where par names
none, b's place is not of the kind K8. -/
def PinPublicAt {S Cl : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (bs : List (Block S Cl)) : Prop :=
  ∀ b ∈ bs,
    match par b.place with
    | some P => smallFits P = true ∧ b.rounds = [round P.1]
    | none => b.place.kind ≠ KindName.K8

/-- **The pin's clauses on the halves**: at each member b of bs: where par names parameters P at b's
place, a half of hs stands at that place and the first half there has the one part
quietStop (smallStop cells P) (windowShare P.1); where par names none, if a half stands at b's
place, no part of the first half there has a private abort test that fires at any argument, and each
part's stated share has the value 0. -/
def PinHalvesAt {S Cl W₀ Rc Xi Tr X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr → Cells) (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)) : Prop :=
  ∀ b ∈ bs,
    match par b.place with
    | some P => ∃ g, (hs.find? fun g => g.place == b.place) = some g ∧
        g.parts = [quietStop (smallStop cells P) (windowShare P.1)]
    | none => ∀ g, (hs.find? fun g => g.place == b.place) = some g →
        ∀ p ∈ g.parts, (∀ u l o, p.hid u l o = none) ∧ p.hidShare.val = 0

/-- **The pin is the two conditions together.** -/
def Spec.pin_iff : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr → Cells) (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)),
    RowsPinned par cells hs bs ↔ PinPublicAt par bs ∧ PinHalvesAt par cells hs bs

/-- At the par that names none PinHalvesAt is SilentAt. -/
def Spec.halves_none_iff : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)) (bs : List (Block S Cl)),
    PinHalvesAt (fun _ => none) cells hs bs ↔ SilentAt hs bs

/-- **At each member of the kind K8 of the first chain without its last member parOwn names
parameters, and the member has the one round at them.** At all public files in scope that can be
read, under LaidAt, at every mats. -/
def Spec.pin_first_public : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ mats : ℕ → List (ℕ × String × ℕ),
    ∀ b ∈ (descZ Zp Np cF).first.blocksInOrder.dropLast, b.place.kind = KindName.K8 →
      ∃ P, parOwn Zp mats b.place = some P ∧ b.rounds = [round P.1]

/-- **The pin's clauses on public data hold at the first chain without its last member, at the
description's own parameters and the list matsOf.** At all public files in scope that can be read,
under LaidAt. -/
def Spec.public_first : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    PinPublicAt (parOwn Zp (matsOf Zp.p.X)) (descZ Zp Np cF).first.blocksInOrder.dropLast

/-- **They hold at the second chain, at the par that names none**: at all letters. -/
def Spec.public_second : Prop :=
  ∀ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl),
    PinPublicAt (fun _ => none) (descZ Zp Np cF).second.blocksInOrder

/-- **So the pin at the first chain, at the description's own parameters and matsOf, is a condition
on the halves alone**: at all public files in scope that can be read, under LaidAt, at every reader
of cells and all halves. -/
def Spec.pin_first_iff : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
      (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)),
      RowsPinned (parOwn Zp (matsOf Zp.p.X)) cells hs (descZ Zp Np cF).first.blocksInOrder.dropLast ↔
        PinHalvesAt (parOwn Zp (matsOf Zp.p.X)) cells hs (descZ Zp Np cF).first.blocksInOrder.dropLast

/-- **What PinHalvesAt says at the first chain, place by place**: at all public files in scope that
can be read, under LaidAt, at every reader of cells and all halves: at each of the twenty-five
written places k8PlaceAt l parOwn names parameters P, a half stands, and the first half there has
the one part quietStop (smallStop cells P) (windowShare P.1); and SilentAt holds at the members that
are not of the kind K8. -/
def Spec.halves_first_iff : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
      (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)),
      PinHalvesAt (parOwn Zp (matsOf Zp.p.X)) cells hs (descZ Zp Np cF).first.blocksInOrder.dropLast ↔
        (∀ l < 25, ∃ P g, parOwn Zp (matsOf Zp.p.X) (k8PlaceAt l) = some P ∧
            (hs.find? fun g => g.place == k8PlaceAt l) = some g ∧
            g.parts = [quietStop (smallStop cells P) (windowShare P.1)]) ∧
          SilentAt hs ((descZ Zp Np cF).first.blocksInOrder.dropLast.filter
            fun b => b.place.kind != KindName.K8)

/-- A negative test; it counts as no goal. At a member at whose place par names parameters P and
whose rounds are not the one round round P.1 PinPublicAt fails; so the pin fails at all halves
(Spec.pin_iff). -/
def Spec.wrong_rounds_not_public : Prop :=
  ∀ {S Cl : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (bs : List (Block S Cl)) (b : Block S Cl) (P : Par × List (ℕ × String × ℕ)),
    b ∈ bs → par b.place = some P → b.rounds ≠ [round P.1] → ¬ PinPublicAt par bs

/-- A negative test; it counts as no goal. At a member at whose place par names parameters P at
which smallFits fails PinPublicAt fails; so the pin fails at all halves (Spec.pin_iff). -/
def Spec.unfit_not_public : Prop :=
  ∀ {S Cl : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (bs : List (Block S Cl)) (b : Block S Cl) (P : Par × List (ℕ × String × ℕ)),
    b ∈ bs → par b.place = some P → smallFits P = false → ¬ PinPublicAt par bs

/-- A control; it counts as no goal. At one member at whose place par names parameters P, and at the
one half with the pinned part at that place, PinHalvesAt holds, whatever smallFits P and the
member's rounds are: so PinHalvesAt has neither of PinPublicAt's clauses. -/
def Spec.halves_need_no_public : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr → Cells) (b : Block S Cl) (P : Par × List (ℕ × String × ℕ)),
    par b.place = some P →
    PinHalvesAt par cells
      ([⟨b.place, [quietStop (smallStop cells P) (windowShare P.1)]⟩] :
        List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)) [b]

/-- A negative test; it counts as no goal. At all public files in scope that can be read, under
LaidAt: at the lists matsOf Zp.p.X l without their last members PinPublicAt fails at the first chain
without its last member. So the arm with parameters is not empty there, and smallFits does work. -/
def Spec.short_names_not_public : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ¬ PinPublicAt (parOwn Zp fun l => (matsOf Zp.p.X l).dropLast)
      (descZ Zp Np cF).first.blocksInOrder.dropLast

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.PinPublicAt
#print axioms OnBytes.FrontRoad.PinHalvesAt
#print axioms OnBytes.FrontRoad.Spec.pin_iff
#print axioms OnBytes.FrontRoad.Spec.halves_none_iff
#print axioms OnBytes.FrontRoad.Spec.pin_first_public
#print axioms OnBytes.FrontRoad.Spec.public_first
#print axioms OnBytes.FrontRoad.Spec.public_second
#print axioms OnBytes.FrontRoad.Spec.pin_first_iff
#print axioms OnBytes.FrontRoad.Spec.halves_first_iff
#print axioms OnBytes.FrontRoad.Spec.wrong_rounds_not_public
#print axioms OnBytes.FrontRoad.Spec.unfit_not_public
#print axioms OnBytes.FrontRoad.Spec.halves_need_no_public
#print axioms OnBytes.FrontRoad.Spec.short_names_not_public
