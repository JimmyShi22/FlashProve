-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6FrontSays.lean: WHAT THE TABLE'S PROMISE IN FRONT OF THE OUTPUT HEAD'S OWN
ROUNDS (border 341 of the full chain) SAYS OF THE VERIFIER'S STATE, AT THE COMPOSED MEANING mgAll D
Mg (Johnson/Desc/Sound/MgAll.lean): four sentences, each taken out of the promise by
name. Statements and proofs.

Why. The law of these rounds asks where the head's matrices are seated in the verifier's state
behind them. Four of the readers through which that is asked are spoken of by the promise itself at
this border: other authors' public tests, which the row of this sub-protocol asks.

What is said (a: a statement inside the promise at border 341 whose state bears no mark; hfit: the
table's own test pubFit at the composed meaning's list of extra public tests; hp: the place at 341).
  asked_more          whatever name the list of extra public tests asks at a place holds in front
      of it.
  sent_asked          the name (some 24, "frame.sentIs") is asked at this sub-protocol's place, at
      every Mg.
  **sentIs_front**    so: FillSent.sentIsB D.pubD.dS 24 a.1.2 = true: the open segment's frame's
      five fields that ReqFrame.whereIs reads are the public terms.
  **fresh_front**     the public item linkFresh 24: the open segment's list of arrays is the public
      one.
  **left_front**      what the public item left 24 says beside its Bool: k3LeftItemAt Wp 24 a.1.2.
  **book_front**      the promise's clause on the book: as many places as oracle messages, and of
      these as many as the table's numbers say.

Every letter under "there is": none.
What it does not say. That any statement is inside the promise. Who makes or keeps the four: their
authors' laws. The full chain alone. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6AtMgAll
import Johnson.Desc.Sound.MgAllAt
import Johnson.Desc.Sound.Border62At
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning Pub pubFit moreItem MoreName pubRowM
  pubStartM)
open VerifiableInference.Desc.Sound (Frame MsgT onQ pubQ linksFull head_full MgData mgAll)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (asks_K6)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (Fr : Frame)

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- The place of the output head's own rounds. -/
def placeK6 : Place := { chain := 1, link := some 24, piece := 4, kind := .K6 }

/-- **Whatever name the list of extra public tests asks at a place holds in front of it.** -/
theorem asked_more {A W : Type} (N : Numbers) (M : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × S) (hfit : pubFit M.more links ps = true) (k : ℕ) (p : Place)
    (hp : ps[k]? = some p) (a : A × Fr.E.Str) (h : onQ N M links ps get k a)
    (hm : (get a.1).2.failed = none) (x : MoreName) (hx : x ∈ (M.more.rows links p).asks) :
    M.pub (moreItem x) (get a.1) = true :=
  (Sound.onParts_of_on N M links ps get k a h hm).pub _
    (List.mem_append_left _ (Sound.asks_open (pubRowM M.more links) ps (pubStartM M.more) k p hfit
      hp _ (List.mem_append_right _ (List.mem_map_of_mem hx))))

/-- The name is asked at this sub-protocol's place, whatever Mg adds. -/
theorem sent_asked :
    First.FillSent.sentName 24 ∈ ((MGA).more.rows linksFull placeK6).asks := by
  rw [Sound.mgAll_more_merges]
  refine List.mem_filter.2 ⟨?_, by decide⟩
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  decide

/-- **The open segment's frame's five fields are the public terms.** -/
theorem sentIs_front (hfit : pubFit (MGA).more linksFull PS = true) (hp : PS[341]? = some placeK6)
    (a : (P × S) × Fr.E.Str) (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a)
    (hm : a.1.2.failed = none) : First.FillSent.sentIsB D.pubD.dS 24 a.1.2 = true := by
  have h : (MGA).pub (moreItem (First.FillSent.sentName 24)) a.1 = true :=
    asked_more Fr D.N MGA linksFull PS (fun a => a) hfit 341 placeK6 hp a ha hm
      (First.FillSent.sentName 24) (sent_asked D Mg)
  rw [Sound.mgAll_pub] at h
  exact (First.pubAll_more_sentIs D.pubD Mg.pub 24 a.1).symm.trans h

/-- **The open segment's list of arrays is the public one.** -/
theorem fresh_front (hfit : pubFit (MGA).more linksFull PS = true) (hp : PS[341]? = some placeK6)
    (a : (P × S) × Fr.E.Str) (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a)
    (hm : a.1.2.failed = none) :
    VerifiableInference.OnPublicFiles.linkFreshB (D.sent.arrayOf.getD 24 #[]) a.1.2 = true := by
  have h : (MGA).pub (.linkFresh 24) a.1 = true :=
    Sound.asked_of_on D.N MGA linksFull PS (fun a => a) hfit 341 placeK6 hp a ha hm (.linkFresh 24)
      (by rw [asks_K6 linksFull placeK6 24 rfl head_full rfl]; simp)
  exact h

/-- **What the lookup argument on the head's calls left.** -/
theorem left_front (hfit : pubFit (MGA).more linksFull PS = true) (hp : PS[341]? = some placeK6)
    (a : (P × S) × Fr.E.Str) (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a)
    (hm : a.1.2.failed = none) : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 a.1.2 := by
  have h : (MGA).pubP (.left 24) a.1 :=
    (Sound.onParts_of_on D.N MGA linksFull PS (fun a => a) 341 a ha hm).pubP (.left 24)
      (Sound.asks_open (pubRowM (MGA).more linksFull) PS (pubStartM (MGA).more) 341 placeK6 hfit hp
        (.left 24)
        (List.mem_append_left _ (by rw [asks_K6 linksFull placeK6 24 rfl head_full rfl]; simp)))
  exact h

/-- **Where the book stands.** -/
theorem book_front (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a) (hm : a.1.2.failed = none) :
    First.bookAt D.N PS[341]? a.1.2 = true :=
  (Sound.onParts_of_on D.N MGA linksFull PS (fun a => a) 341 a ha hm).book

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.sentIs_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.fresh_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.left_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.book_front
