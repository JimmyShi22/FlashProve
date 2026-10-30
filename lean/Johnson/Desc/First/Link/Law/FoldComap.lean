-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/FoldComap.lean: THE FACTS ALONG THE FOLD (`FoldFacts`,
Johnson/Desc/First/FoldFacts.lean: another file's structure, kind-free, general in the sort of
statement) CARRIED ALONG A MAP OF STATEMENTS: so that the one head's facts, stated over «the public
part and the state, with the strings», serve the link's lists, which speak at one public part z over
«the state, with the strings». Theorems.

What is said.
  `FoldFacts.comap`: **for f : Y → X: the facts at (Rch, at_) give the facts at (fun k y => Rch k (f
    y), fun y => at_ (f y))**: every one of the 26 fields begins «∀ k a, Rch k a → …» and reads a
    through at_ alone. `foldFacts_at`: **so the facts at (Rch, the first component) give the facts
    at (`RchAt Rch z`, fun a => (z, a.1))**: the form of the lists' field FF.

Limits. BOOK-KEEPING: it proves no field of `FoldFacts`. Written by program from that structure's
own list of fields. Nothing on soundness.

-/
import Johnson.Desc.First.FoldFacts
import Johnson.Desc.First.Link.Law.LinkTiedPubR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- **THE FACTS ALONG A MAP OF STATEMENTS.** -/
theorem FoldFacts.comap {X Y P : Type} {Rch : Nat → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place} (f : Y → X)
    (F : FoldFacts Rch at_ d reqW links ps) :
    FoldFacts (fun k y => Rch k (f y)) (fun y => at_ (f y)) d reqW links ps :=
  ⟨fun k a => F.bookInOrder k (f a), fun k a => F.seatsCarried k (f a), fun k a => F.bookFits k (f
    a), fun k a => F.msgShapes k (f a), fun k a => F.weightsOk k (f a), fun k a => F.pileMasks k (f
    a), fun k a => F.pileWithin k (f a), fun k a => F.oneRow k (f a), fun k a => F.tidy k (f a), fun
    k a => F.codes k (f a), fun k a => F.shape k (f a), fun k a => F.layout k (f a), fun k a =>
    F.liveShape k (f a), fun k a => F.liveLayout k (f a), fun k a => F.groups k (f a), fun k a =>
    F.liveGroups k (f a), fun k a => F.frameShape k (f a), fun k a => F.frameGroups k (f a), fun k a
    => F.ownIs k (f a), fun k a => F.groupIs k (f a), fun k a => F.frameIs k (f a), fun k a =>
    F.rowsSent k (f a), fun k a => F.reqIs k (f a), fun k a => F.replyNat k (f a), fun k a => F.room
    k (f a), fun k a => F.roomEarly k (f a)⟩

end VerifiableInference.Desc.First

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart FoldFacts FoldData)

/-- **AT ONE PUBLIC PART.** -/
theorem foldFacts_at {P : Type} {F : Frame} {Rch : ℕ → (P × S) × F.E.Str → Prop} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (H : FoldFacts Rch (fun a => a.1) d reqW links ps) (z : P) :
    FoldFacts (RchAt Rch z) (fun a : S × F.E.Str => (z, a.1)) d reqW links ps :=
  H.comap fun a : S × F.E.Str => ((z, a.1), a.2)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.First.FoldFacts.comap
#print axioms VerifiableInference.Desc.LinkJoin.foldFacts_at
