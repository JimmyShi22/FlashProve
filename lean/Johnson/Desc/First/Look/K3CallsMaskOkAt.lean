-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
maskOkCalls_of_facts: no list of rounds, no meaning and no state are shown
at which its premises hold together.
Johnson/Desc/First/Look/K3CallsMaskOkAt.lean: the lookup on a link's CALLS AT THE TABLE OF JOINTS:
THE PREMISE hOk OF calls_objects_att | calls_objects_lay
(Johnson/Desc/First/Look/K3CallsObjects.lean: "MaskOkCalls at the part of the verifier's state
behind"), SIGN FOR SIGN, from: four facts along the fold in front (the sentences of FoldFacts'
fields liveShape, liveGroups, seatsCarried, msgShapes, at a letter Rc) · two public tests that are
open at the border behind ("frame.sentIs", freeAbove) · the promise's own conjunct bookAt there ·
the tests on the list of rounds maskTestsB. A call of maskOkCalls_of_sentIs (K3CallsMaskOk.lean).
Statements and proofs. No error term. NO SOUNDNESS IS CLAIMED.

How the facts in front reach the state behind: they read the open link's context, the statement and
the book alone, which the lookup's accepting leaves (SameBut).

OBJECT: the table of joints' promise at two borders.
USER: K3CallsObjectsAt.lean, Johnson/P5J/K03ObjAt.lean, Johnson/P5J/K03HeadObjAt.lean and others.
LETTERS: the field's own; dS, Ld, M, seatN, own.

Compiled with the whole library.


Main names:
  `onQ_book`: the unmarked arm of the promise holds bookAt.
  `maskOkCalls_of_facts`: THE END.

EACH PREMISE, AND WHO COULD PAY IT. hLive, hGroups, hSeats, hShapes: FoldFacts' fields. askSent,
askFree: tests on the table ("the item is open at that border"). pubSent, pubFree: the composed
meaning's lemmas at these two items, the second with "the planned number of slots is the place's".
hT: the seats are a function of the number in the list. hTests: a test on the list of rounds. hsome,
h6: tests on the table's list of members.

Limits. At the calls alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsMaskOk
import Johnson.Desc.First.Look.K3AttAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning Numbers bookAt pubSets moreItem)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB sentName)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (maskMsg)

section
variable {P Cells Tok : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P (Wit Cells Tok MsgT)}
  {links : List ModelPart} {ps : List Desc.Place} {pi : P} {k : ℕ}

/-- The unmarked arm of the table's promise holds "where the book stands". -/
theorem onQ_book {a : Desc.First.S × Fr.E.Str}
    (h : onQ N Mg links ps (fun s => (pi, s)) k a) (hu : a.1.failed = none) :
    bookAt N ps[k]? a.1 = true := by
  obtain ⟨-, hm | ⟨h1, -⟩⟩ := h
  · exact absurd hu hm
  · simp only [Bool.and_eq_true] at h1
    exact h1.2

variable (x : Desc.First.Look.Place) (D : Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (own : List (ℕ × ℕ))
  (m : ℕ) (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)
  (Rc : Desc.First.S × Fr.E.Str → Prop)

/-- **THE PREMISE hOk, FROM THE FACTS ALONG THE FOLD, THE PROMISE AND THE TESTS.** -/
theorem maskOkCalls_of_facts {dS : SentData} {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
    (seatN : ℕ → ℕ × ℕ) (hT : ∀ i, seatT i = seatN i.val)
    (hLive : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      a.1.live.frame.shape = D.shape)
    (hGroups : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      a.1.live.frame.groups = reqGroups a.1.live.frame.shape)
    (hSeats : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      Desc.K12.Door.atFirstSeats Ld a.1 = true)
    (hShapes : ∀ a : Desc.First.S × Fr.E.Str, Rc a → a.1.failed = none →
      Desc.K12.Door.atFirstShapes M a.1 = true)
    (askSent : moreItem (sentName m) ∈ (pubSets Mg.more links ps)[k + 1]?.getD [])
    (pubSent : ∀ s, Mg.pub (moreItem (sentName m)) (pi, s) = true → sentIsB dS x.link s = true)
    (askFree : Pub.freeAbove m ∈ (pubSets Mg.more links ps)[k + 1]?.getD [])
    (pubFree : ∀ s, Mg.pub (.freeAbove m) (pi, s) = true →
      H2K5.Door.freeAboveB x.ns s = true)
    (hTests : maskTestsB (maskMsg D x.link) (keptAt D x.link).length (dS.own x.link) N ps[k + 1]?
      Ld M own seatN = true)
    (hsome : ∀ i, ∃ y ∈ ms, Alike y ⟨⟨sigListCalls D rad x.link, seatT⟩, i⟩)
    (h6 : oneShapeB ms = true) :
    ∀ a b : Desc.First.S × Fr.E.Str, onQ N Mg links ps (fun s => (pi, s)) k a → Rc a →
      a.1.failed = none → Yes a b → SameBut a.1 b.1 →
      onQ N Mg links ps (fun s => (pi, s)) (k + 1) b →
      ∀ a', segAt? b.1 = some a' → MaskOkCalls x D rad seatT ms own a' := by
  intro a b _ hr hu _ hs hb a' hseg
  have hub : b.1.failed = none := hs.failed.trans hu
  obtain ⟨hq, -⟩ := onQ_arm hb hub
  have eLive : b.1.live = a.1.live := by
    unfold Desc.First.S.live
    rw [hs.link]
    cases a.1.link? with
    | none => exact hs.check
    | some L => rfl
  refine maskOkCalls_of_sentIs x D rad seatT ms own seatN hT ?_ ?_ (pubSent _ (hq _ askSent))
    (pubFree _ (hq _ askFree)) (Nat.le_refl _) (onQ_book hb hub) ?_ ?_ hTests hsome h6 a' hseg
  · rw [eLive]
    exact hLive a hr hu
  · rw [eLive]
    exact hGroups a hr hu
  · have h0 := hSeats a hr hu
    unfold Desc.K12.Door.atFirstSeats at h0 ⊢
    rw [hs.book]
    exact h0
  · have h0 := hShapes a hr hu
    unfold Desc.K12.Door.atFirstShapes at h0 ⊢
    rw [hs.st]
    exact h0

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.onQ_book
#print axioms VerifiableInference.OnPublicFiles.maskOkCalls_of_facts
