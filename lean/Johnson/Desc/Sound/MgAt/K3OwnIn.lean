-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3OwnIn.lean: the kind "lookup" (K3): THE FIELD ownIn OF THE KIND's ROWS IN
THE SECOND FORM ("the state's own numbers are the list of rounds' at this link": `OwnIs`) FROM THE
FACTS ON EVERY REACHED STATE (`FoldFacts`, Johnson/Desc/First/FoldFacts.lean), AT ALL FIFTY PLACES.

Main names:
  `K3Fold Rch D`: THE TIGHT LIST, AS FAR AS THE KIND's FIELDS ARE PAID: what the paid arms
    spend of the facts along the fold, at just their borders: ownIs (at the fifty borders in front
    of the lookup arguments) · replyNat (at the border in front of the output head's calls
    alone). Not in it: the fields objects and fObj, owed, which
    spend through the mask row's conditions: at the calls liveShape, liveGroups, seatsCarried,
    msgShapes; at the digits these four and frameIs' link, next, own. The kind's law takes THIS
    as its premise (a row ends in what it spends);
    `k3Fold_of_foldFacts`: the one structure gives it: the corollary for the join at the top.
  `k3_ownIs_of_fold`: at the border in front of either lookup argument of segment l < 25, at a
    reached state without a mark: `OwnIs d.sent l`. One call of the field `FoldFacts.ownIs`, at the
    place that stands at that number of the full size's written list (`k03_at_full`).
  `head_ownIn_of_fold`: `HeadAtTableR`'s field ownIn, to the letter, at Rc := Rch at that border
    and the public part in hand; the promise in front goes unspent.

Limits: `FoldFacts` is a premise: its field ownIs is booked as the integer model's files' to show
(not seen here). Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.FoldFacts
import Johnson.P5K3R.SitsAddr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First (FoldFacts FoldData ModelPart flatPlacesOf)
open VerifiableInference.Desc.First.Look (OwnIs)
open VerifiableInference.Desc.Sound (linksFull)

/-- **The kind's fifty borders.** -/
theorem k3_ownIs_of_fold {A P : Type} {Rch : ℕ → A → Prop} {at_ : A → P × Desc.First.S}
    {d : FoldData} {reqW : P → Array UInt32} {links : List ModelPart}
    (F : FoldFacts Rch at_ d reqW links (flatPlacesOf linksFull true)) (l : ℕ) (hl : l < 25)
    (dg : Bool) (a : A) (hr : Rch (14 * l + IM.k3Ix l dg + 2) a)
    (hu : (at_ a).2.failed = none) : OwnIs d.sent l (at_ a).2 :=
  F.ownIs _ a _ l hr hu (K3Lot.k03_at_full l hl dg) rfl rfl

/-- **WHAT THE KIND's PAID FIELDS SPEND OF THE FACTS ALONG THE FOLD** (objects and fObj, owed,
will add to it). -/
structure K3Fold {P Str : Type} (Rch : ℕ → (P × Desc.First.S) × Str → Prop)
    (D : Desc.First.Look.Sent) : Prop where
  ownIs : ∀ l < 25, ∀ (dg : Bool) (u : (P × Desc.First.S) × Str),
    Rch (14 * l + IM.k3Ix l dg + 2) u → u.1.2.failed = none → OwnIs D l u.1.2
  replyNat : ∀ u : (P × Desc.First.S) × Str, Rch (14 * 24 + IM.k3Ix 24 false + 2) u →
    u.1.2.failed = none → ∀ g, u.1.2.out.reply = some g → OnBytes.Model.ofNat g.c0.toNat = g

/-- **The one structure gives the tight list.** -/
theorem k3Fold_of_foldFacts {P Str : Type} {Rch : ℕ → (P × Desc.First.S) × Str → Prop}
    {d : FoldData} {reqW : P → Array UInt32} {links : List ModelPart}
    (F : FoldFacts Rch (fun a => a.1) d reqW links (flatPlacesOf linksFull true)) :
    K3Fold Rch d.sent :=
  ⟨fun l hl dg u hr hu => k3_ownIs_of_fold F l hl dg u hr hu, fun u hr hu => F.replyNat _ u hr hu⟩

/-- **ownIn, at the head's calls.** -/
theorem head_ownIn_of_fold {P Str : Type} {Rch : ℕ → (P × Desc.First.S) × Str → Prop}
    {d : FoldData} {reqW : P → Array UInt32} {links : List ModelPart}
    (F : FoldFacts Rch (fun a => a.1) d reqW links (flatPlacesOf linksFull true)) (z : P)
    {x : Desc.First.Look.Place} (hx : x.link = 24) (On : Desc.First.S × Str → Prop) :
    ∀ a : Desc.First.S × Str, On a → Rch (14 * 24 + IM.k3Ix 24 false + 2) ((z, a.1), a.2) →
      a.1.failed = none → OwnIs d.sent x.link a.1 := by
  intro a _ hr hu
  rw [hx]
  exact k3_ownIs_of_fold F 24 (by decide) false ((z, a.1), a.2) hr hu

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_ownIs_of_fold
#print axioms VerifiableInference.OnPublicFiles.head_ownIn_of_fold
#print axioms VerifiableInference.OnPublicFiles.k3Fold_of_foldFacts
