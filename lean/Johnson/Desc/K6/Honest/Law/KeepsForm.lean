-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/KeepsForm.lean: eight of the fourteen premises under which the table of
joints' promise rides past a block (`onAt_step_quiet`, Johnson/Desc/First/PromiseRides.lean), at the
sub-protocol "the output head's own rounds" (K6): each from `K6Keeps` (Honest/Law/Keeps.lean) and
public facts. Over the library alone. EVERY THEOREM IS CONDITIONAL.

Why here. The promise is the verifier's side's. The honest side's invariant holds it as a clause at
every border, so whoever shows that invariant behind this sub-protocol's yes must carry the promise
past it, at a state and not at a piece of the proof of soundness.

  `K6Place`   five facts on the index: the sub-protocol's place and the next one
  `keeps_quiet`     the sub-protocol's row closes and opens no class of rows and no pin (that rule's
              hq)
  `keeps_failed`, `keeps_groups`, `keeps_places`   the mark, the statement's groups and the book's
              places are as they were (hMark, hG, hB)
  `keeps_shape`     the book-keeping Bool at the next place, from that at the place (hShape)
  `keeps_book`      where the book stands (hBook)
  `keeps_inOrder`, `keeps_held`   "the statement is in order"; "the sample is held" (hIn, hHeld)

WHAT IS CALLED. Three things lie in the library's file on this sub-protocol's second tie at a piece
(Johnson/Desc/Sound/K6Second.lean), at a state or at letters, and are called: `shape_behind` (the
book-keeping from piece 4 to piece 5 of the head's segment: no count of rows may wait at piece 4,
since the head's segment has nine hearing kinds and a count may wait at pieces 11 and 12 alone),
`quiet_K6`, and the premise's form `BlindOrder` (two letters of a meaning do not read where the
chain stands). From the like file of another kind (Johnson/Desc/First/Att/K05T2.lean) the premise's
form `K5Book` is called: two facts on the table's numbers (as many trees and oracle messages are due
behind as in front), with no letter of that kind's; `K6Place` follows that file's `K5Place`.

Limits. The rule itself is not called here. OF ITS FOURTEEN PREMISES SIX ARE NOT TOUCHED: the
promise in front (ha); the three on the strings (hDec, hSh, hNc); the two on the public items (hPub,
hPP). `keeps_shape` asks the book-keeping at the place, which is to be had from the promise in front
(`onAt_shape`, Johnson/Desc/First/Att/K05T2.lean). NONE OF `K6Place`, `K5Book`, `BlindOrder` IS
SHOWN HERE AT ANY TABLE OR MEANING: that is Honest/Law/KeepsAtHead.lean's. Nothing on any property.

-/
import Johnson.Desc.K6.Honest.Law.Keeps
import Johnson.Desc.Sound.K6Second
import Johnson.Desc.First.Att.K05T2
import Johnson.Desc.First.PromiseRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Honest
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning shapeAt bookAt rowOf quietRow)
open VerifiableInference.Desc.First.Att.P (K5Book)
open VerifiableInference.Desc.Sound (BlindOrder shape_behind quiet_K6)

/-- Five facts on the index: the place of the sub-protocol and the next place. -/
structure K6Place (links : List ModelPart) (m : Nat) (p p' : Place) : Prop where
  link : p.link = some m
  piece : p.piece = 4
  sub : links[m]? = some .head
  link' : p'.link = some m
  piece' : p'.piece = 5

/-- **The sub-protocol's row is quiet.** CONDITIONAL: three of the five facts on the index. -/
theorem keeps_quiet {links : List ModelPart} {m : Nat} {p p' : Place} (Ix : K6Place links m p p') :
    quietRow (rowOf links p) = true :=
  quiet_K6 links p m Ix.link Ix.sub Ix.piece

variable {s s' : S}

/-- The mark is as it was. CONDITIONAL: what a yes leaves. -/
theorem keeps_failed (K : K6Keeps s s') : s'.failed = s.failed := by
  have h := congrArg S.failed K.here
  exact h

/-- The statement's groups are as they were. CONDITIONAL: what a yes leaves. -/
theorem keeps_groups (K : K6Keeps s s') : s'.st.groups = s.st.groups := by
  have h := congrArg (fun t : S => t.st.groups) K.here
  exact h

/-- The book's places are as they were. CONDITIONAL: what a yes leaves. -/
theorem keeps_places (K : K6Keeps s s') : s'.book.place = s.book.place := by
  have h := congrArg (fun t : S => t.book.place) K.here
  exact h

/-- **The book-keeping at the next place.** CONDITIONAL: the five facts on the index; what a yes
leaves; the book-keeping at the place. -/
theorem keeps_shape {links : List ModelPart} {m : Nat} {p p' : Place} (Ix : K6Place links m p p')
    (K : K6Keeps s s') (h : shapeAt links (some p) s = true) :
    shapeAt links (some p') s' = true := by
  obtain ⟨o, o', ho, ho', e⟩ := K.own
  have hs := K.here
  obtain ⟨_, _, o1, _, h1, _, hop, _⟩ := K
  rw [ho] at h1
  cases h1
  have hop' : o'.opened = true := by rw [e]; exact hop
  have eL : o'.L = o.L := by rw [e]
  rw [hs, ho']
  exact shape_behind links p p' m Ix.link Ix.link' Ix.sub Ix.piece Ix.piece' s o o' ho hop hop' eL h

/-- **Where the book stands.** CONDITIONAL: the two facts on the table's numbers; what a yes leaves;
the Bool at the place. -/
theorem keeps_book {N : Numbers} {p p' : Place} (Bk : K5Book N p p') (K : K6Keeps s s')
    (h : bookAt N (some p) s = true) : bookAt N (some p') s' = true := by
  have e1 : s'.book = s.book := by
    have h0 := congrArg S.book K.here
    exact h0
  have e2 : s'.st = s.st := by
    have h0 := congrArg S.st K.here
    exact h0
  unfold bookAt at h ⊢
  rw [e1, e2, Bk.trees, Bk.msgs]
  exact h

/-- **The statement is in order.** CONDITIONAL: the letter does not read where the chain stands;
what a yes leaves. -/
theorem keeps_inOrder {P W : Type} {Mg : Meaning P W} (Bl : BlindOrder Mg) (K : K6Keeps s s')
    (z : P) (h : Mg.inOrder (z, s) = true) : Mg.inOrder (z, s') = true := by
  rw [K.here, Bl.order]
  exact h

/-- **A sample is held.** CONDITIONAL, as the last. -/
theorem keeps_held {P W : Type} {Mg : Meaning P W} (Bl : BlindOrder Mg) (K : K6Keeps s s') (z : P)
    (j t : Nat) (h : Mg.held j t (z, s) = true) : Mg.held j t (z, s') = true := by
  rw [K.here, Bl.held]
  exact h

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keeps_quiet
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keeps_failed
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keeps_groups
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keeps_places
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keeps_shape
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keeps_book
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keeps_inOrder
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keeps_held
