-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SecondChainPlacesSpec.lean: statements only, on public data and on a premise's
form. At all letters Zp, Np and cF the second chain of the description descZ Zp Np cF has four
members, at four written places, of the kinds K14, frame, K12 and frame: none is of the kind K8. So
the pin at the second chain (RowsPinned at the par that names none,
Johnson/FrontRoad/SessionStopsPinned.lean), which is a premise of the implications on the field
sessionStops, is a condition on the halves that stand at these four places alone. Proved in
Johnson/FrontRoad/SecondChainPlaces.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  secondPlacesW   the four written places.
  SilentAt hs bs   a condition on a chain's halves hs at its members bs: at each member, if a half
      stands at its place, no part of the first half there has a private abort test that fires at
      any argument, and each part's stated share has the value 0. It is the second clause of
      RowsPinned's case without parameters, word for word.
  Spec.second_places_at   the places of the second chain's members are secondPlacesW, in order. It
      is second_places (Johnson/Desc/ProofFile/Law/LaterKinds.lean) at the term descZ Zp Np cF,
      without that theorem's premise: the premise only names the seat, and descZ has the seat by
      name (secondAt Zp Np).
  Spec.no_k8_second   so no member of the second chain is of the kind K8.
  Spec.pin_none_iff   general, at every list of members and all halves: RowsPinned at the par that
      names none holds just where no member is of the kind K8 and SilentAt holds. cells is idle:
      RowsPinned at that par never reads it.
  Spec.pin_second_iff   so, at all halves hs: RowsPinned (fun _ => none) cells hs at the second
      chain's members holds just where SilentAt hs does.
  Spec.pin_none_needs_no_k8   a negative test, general: at a list of members one of which is of the
      kind K8, SilentAt can hold (at no halves) while RowsPinned (fun _ => none) fails. So the
      clause on the kinds does work, and the equivalence of Spec.pin_second_iff fails at such a
      list. That the pin fails there, at all halves, is unnamed_not_pinned
      (Johnson/FrontRoad/SessionStopsPinnedTests.lean).

How it fits. In sessionStops_of_pinned and all that stands on it the premise h₃ is RowsPinned (fun _
=> none) cells (provG …).second (descZ Zp Np cF).second.blocksInOrder. By its text it asks, beside the
halves' clause, that no member of that chain is of the kind K8: a clause on public data, which no
theorem met; if it failed, each of these implications would hold idly. Here it is stated at all
letters, with no premise. Words (member, half, part, public and private abort test, stated share):
Johnson/FrontRoad/SessionStopsPinned.lean. Not one of the release's goal statements.

Limits.
  Nothing is said of any prover. Rows without a half at the four places meet SilentAt idly, by its
      text; whether rows that send what the second chain's rounds ask meet it is not said.
  The pin at the first chain, hR and the premise on the cells or on the trace stay premises. The pin
      at the first chain has clauses on public data too (at a member of the kind K8 par names
      parameters; the member's rounds; smallFits): at parOwn no one theorem states them at each
      member of the list without its last (the pieces: Spec.k8_places_front, Spec.pars_at_parOwn,
      parOwn_at_draw, Spec.matsOf_fits). No book, rows and prover are known at which all premises
      hold together.
  The statements are on the term descZ Zp Np cF at free letters. That this term is the description
      of any public files is LaidAt's word, which is not asked here.
  The shared chain is not treated: the pin does not speak of it.
  A place is a label: nothing is said on what a member does.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.SessionStopsOfPinned

set_option autoImplicit false

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles (descZ)
open VerifiableInference.Desc (Block Place KindName)
open P5J (TS)

/-- The four written places of the second chain's members. -/
def secondPlacesW : List Place :=
  [⟨3, none, 0, KindName.K14⟩, ⟨3, none, 1, KindName.frame⟩, ⟨3, none, 2, KindName.K12⟩,
    ⟨3, none, 3, KindName.frame⟩]

/-- **A condition on a chain's halves at its members**: at each member, if a half stands at its
place, no part of the first half there has a private abort test that fires at any argument, and each
part's stated share has the value 0. -/
def SilentAt {S Cl W₀ Rc Xi Tr X : Type}
    (hs : List (ProofFile.Honest.Placed (ProofFile.Honest.Local W₀ Rc Xi Tr) (ProofFile.Honest.Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)) : Prop :=
  ∀ b ∈ bs, ∀ g, (hs.find? fun g => g.place == b.place) = some g →
    ∀ p ∈ g.parts, (∀ u l o, p.hid u l o = none) ∧ p.hidShare.val = 0

/-- **The places of the second chain's members are the four written ones, in order**: at all
letters. -/
def Spec.second_places_at : Prop :=
  ∀ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl),
    (descZ Zp Np cF).second.blocksInOrder.map (·.place) = secondPlacesW

/-- **So no member of the second chain is of the kind K8.** -/
def Spec.no_k8_second : Prop :=
  ∀ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl),
    ∀ b ∈ (descZ Zp Np cF).second.blocksInOrder, b.place.kind ≠ KindName.K8

/-- **RowsPinned at the par that names none, in two clauses**: no member is of the kind K8, and
SilentAt. At every list of members and all halves. cells is idle: RowsPinned at that par never reads
it. -/
def Spec.pin_none_iff : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (cells : Tr → ProofFile.Honest.Cells)
    (hs : List (ProofFile.Honest.Placed (ProofFile.Honest.Local W₀ Rc Xi Tr)
      (ProofFile.Honest.Local W₀ Rc Xi Tr) X)) (bs : List (Block S Cl)),
    RowsPinned (fun _ => none) cells hs bs ↔
      (∀ b ∈ bs, b.place.kind ≠ KindName.K8) ∧ SilentAt hs bs

/-- **So the pin at the second chain is a condition on the halves that stand at its four places
alone**: at all halves. cells is idle. -/
def Spec.pin_second_iff : Prop :=
  ∀ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {W₀ Rc Xi Tr X : Type} (cells : Tr → ProofFile.Honest.Cells)
    (hs : List (ProofFile.Honest.Placed (ProofFile.Honest.Local W₀ Rc Xi Tr)
      (ProofFile.Honest.Local W₀ Rc Xi Tr) X)),
    RowsPinned (fun _ => none) cells hs (descZ Zp Np cF).second.blocksInOrder ↔
      SilentAt hs (descZ Zp Np cF).second.blocksInOrder

/-- A negative test; it counts as no goal. At members one of which is of the kind K8, and at no
halves, SilentAt holds and RowsPinned at the par that names none fails. -/
def Spec.pin_none_needs_no_k8 : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (cells : Tr → ProofFile.Honest.Cells) (bs : List (Block S Cl))
    (b : Block S Cl), b ∈ bs → b.place.kind = KindName.K8 →
    SilentAt ([] : List (ProofFile.Honest.Placed (ProofFile.Honest.Local W₀ Rc Xi Tr)
        (ProofFile.Honest.Local W₀ Rc Xi Tr) X)) bs ∧
      ¬ RowsPinned (fun _ => none) cells
        ([] : List (ProofFile.Honest.Placed (ProofFile.Honest.Local W₀ Rc Xi Tr)
          (ProofFile.Honest.Local W₀ Rc Xi Tr) X)) bs

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.secondPlacesW
#print axioms OnBytes.FrontRoad.SilentAt
#print axioms OnBytes.FrontRoad.Spec.second_places_at
#print axioms OnBytes.FrontRoad.Spec.no_k8_second
#print axioms OnBytes.FrontRoad.Spec.pin_none_iff
#print axioms OnBytes.FrontRoad.Spec.pin_second_iff
#print axioms OnBytes.FrontRoad.Spec.pin_none_needs_no_k8
