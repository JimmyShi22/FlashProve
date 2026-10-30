-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/HandsPoint.lean: A LIGHT FILE: KIND-FREE: IT IMPORTS ONE FILE ALONE: e₁ AT THE PROOF FILE, THE HALF THAT READS THE VERIFIER's STATE ALONE: WHAT ONE SUB-PROTOCOL OWES, AT ONE STATE IN FRONT.
WHY. A share that ends in Hands under a premise which runs over ALL states in front («hg : ∀ s a, X k s → … → N.groupAt l = a.L.check.group») cannot be carried to HandsR as a black box: Hands has no fence, so from the premise at fenced states alone nothing of the form Hands follows. But such a share's proof spends the premise at the step's own front
state alone. HandsPt says the six fields at ONE front state s: whoever proves HandsPt … s from «the facts at s» has Hands where the facts hold at every s, and HandsR Fk where Fk k s gives them: the turn from the first form to the second is one binder.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.

  HandsPt N links ps E ft k b s   Hands' six fields at the one state s in front.
  hands_iff_pt      Hands ↔ ∀ s, HandsPt … s.
  handsR_iff_pt     HandsR Fk ↔ ∀ s, Fk k s → HandsPt … s.
  HandsPt.under     the seated sub-protocol's from its lot's own's.

What is not claimed. HandsPt at any sub-protocol or state. No soundness.
-/
import Johnson.IMR.HandsFence

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S ModelPart Numbers shapeAt rowsHeld membersHeld bookAt)
open ProofFile (Cl)

/-- **What one sub-protocol owes, at one state in front.** -/
structure HandsPt (N : Numbers) (links : List ModelPart) (ps : List Place) (E : Nat → S → Bool)
    (ft k : Nat) (b : Block S Cl) (s : S) : Prop where
  mark : ∀ s', Yes ft b s s' → s.failed ≠ none → s'.failed ≠ none
  shape : ∀ s', Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps E k s = true → shapeAt links ps[k + 1]? s' = true
  rows : ∀ s', Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps E k s = true → rowsHeld N (openAt links ps (k + 1)) s' = true
  members : ∀ s', Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps E k s = true → membersHeld N (openAt links ps (k + 1)) s' = true
  book : ∀ s', Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps E k s = true → bookAt N ps[k + 1]? s' = true
  more : ∀ s', Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps E k s = true → E (k + 1) s' = true

variable {Fk : Nat → S → Prop} {N : Numbers} {links : List ModelPart} {ps : List Place}
  {E : Nat → S → Bool} {ft k : Nat} {b b' : Block S Cl}

theorem hands_iff_pt : Hands N links ps E ft k b ↔ ∀ s, HandsPt N links ps E ft k b s :=
  ⟨fun H s => ⟨H.mark s, H.shape s, H.rows s, H.members s, H.book s, H.more s⟩,
    fun h => ⟨fun s => (h s).mark, fun s => (h s).shape, fun s => (h s).rows,
      fun s => (h s).members, fun s => (h s).book, fun s => (h s).more⟩⟩

theorem handsR_iff_pt :
    HandsR Fk N links ps E ft k b ↔ ∀ s, Fk k s → HandsPt N links ps E ft k b s :=
  ⟨fun H s f => ⟨fun s' => H.mark s s' f, fun s' => H.shape s s' f, fun s' => H.rows s s' f,
      fun s' => H.members s s' f, fun s' => H.book s s' f, fun s' => H.more s s' f⟩,
    fun h => ⟨fun s s' f => (h s f).mark s', fun s s' f => (h s f).shape s',
      fun s s' f => (h s f).rows s', fun s s' f => (h s f).members s',
      fun s s' f => (h s f).book s', fun s s' f => (h s f).more s'⟩⟩

/-- The seated sub-protocol's from its lot's own's. -/
theorem HandsPt.under {s : S} (H : HandsPt N links ps E ft k b' s) (hU : b.UnderR b') :
    HandsPt N links ps E ft k b s :=
  ⟨fun s' hy => H.mark s' (hy.under hU), fun s' hy => H.shape s' (hy.under hU),
    fun s' hy => H.rows s' (hy.under hU), fun s' hy => H.members s' (hy.under hU),
    fun s' hy => H.book s' (hy.under hU), fun s' hy => H.more s' (hy.under hU)⟩

end IM

#print axioms IM.hands_iff_pt
#print axioms IM.handsR_iff_pt
#print axioms IM.HandsPt.under
