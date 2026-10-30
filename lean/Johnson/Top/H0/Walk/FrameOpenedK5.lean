-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameOpenedK5.lean: THE TWO PUBLIC TESTS "K5.liveReq" AND "K5.readsThere" BEHIND
A YES OF THE QUIET STEP THAT OPENS AN ATTENTION LINK (openAtt, Johnson/Desc/First/Walk/Frame.lean):
EACH IS ONE Bool ON THE STATE IN FRONT AND THE PLAN's LETTERS. NO CODING THEORY. Two definitions
with code, four equations, two uses.

Why. Behind an attention link's first sub-protocol the table of joints lays these two names open:
whoever shows that sub-protocol's share owes that both tests say yes at the state behind its accept.
The tests (Att.P.liveReqB, Johnson/Desc/First/Att/K05DoorB.lean; H2K5.Door.readsThereB,
Johnson/Desc/First/Att/Door/ReadsThereB.lean) read what the quiet step has just laid.

  liveFrontB born l c    the chain's state of the calls c awaits "later or close", and its group at
                    link l was born as born
  readsFrontB W own P c book   readsAtB at the link context and the ledger that openAtt P lays over
                    c, at the numbers of the public parameters' plan of the group P.l / 2, at book
  liveReq_opened, readsThere_opened   openAtt P s = .ok t → the test at t IS that Bool at s.check
                    (and s.book): EQUATIONS: so the Bool in front is just what is owed, no more
  pubAll_liveReq_opened, pubAll_readsThere_opened   the same at the composed test pubAll D base
                    (Johnson/Desc/First/PubAll.lean), at an attention segment
  made_liveReq, made_readsThere   so, under the Bool's yes in front, the composed test says yes

Limits. HALF OF THE MAKER's DEBT: THE TWO Bools IN FRONT ARE PREMISES: that the sub-protocol's first
half (the switch) leaves them, at the plan's own letters, is not said here; they are shown at no
value. That a sub-protocol's accept ends in a yes of openAtt is its authors' law. Calls
openedAtt_here, openedAtt_book (FrameHere.lean, FrameBook.lean) and Law.openAtt_ok (FrameLaw.lean).
No soundness statement.
-/
import Johnson.Top.H0.Walk.FrameHere
import Johnson.Top.H0.Walk.FrameBook
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S Pub PubData pubAll pubAll_more_liveReq
  pubAll_more_readsThere)
open VerifiableInference.Desc.First.Att.P (liveReqB)
open H2K5.Door (readsAtB readsThereB bornOf)

/-- The chain's state of the calls awaits "later or close"; its group at link l was born as born. -/
def liveFrontB (born : Array (Nat × Nat)) (l : Nat) (c : ChainCheck) : Bool :=
  c.frame.next == .laterOrClose && (c.frame.groups.getD l {}).born == born

/-- readsAtB at what openAtt P lays over c. -/
def readsFrontB (W : Verify.Public) (own : List (Nat × Nat)) (P : AttPar) (c : ChainCheck)
    (book : TreeBook) : Bool :=
  (W.A[P.l / 2]?).any fun p =>
    readsAtB own p.iU3 p.nW { check := c, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp }
      (startFork P.X P.ns) book

theorem liveReq_opened {P : AttPar} {s t : S} (h : openAtt P s = .ok t)
    (born : Array (Nat × Nat)) : liveReqB born t = liveFrontB born P.l s.check := by
  obtain ⟨_, _, _, hl, hL, _⟩ := Law.openAtt_ok h
  unfold liveReqB liveFrontB
  rw [hL]
  simp [hl]

theorem readsThere_opened {P : AttPar} {s t : S} (h : openAtt P s = .ok t) (W : Verify.Public)
    (own : List (Nat × Nat)) : readsThereB W own t = readsFrontB W own P s.check s.book := by
  unfold readsThereB readsFrontB
  rw [openedAtt_here h, openedAtt_book h]

section
variable {Q : Type} (D : PubData) (base : Pub → Q × S → Bool)

theorem pubAll_liveReq_opened {P : AttPar} {s t : S} (h : openAtt P s = .ok t)
    (ha : D.d5.isAtt P.l = true) (z : Q) :
    pubAll D base (.more (some P.l) "K5.liveReq") (z, t) =
      liveFrontB (bornOf D.d5.shape P.l) P.l s.check := by
  rw [pubAll_more_liveReq D base P.l ha (z, t)]
  exact liveReq_opened h _

theorem pubAll_readsThere_opened {P : AttPar} {s t : S} (h : openAtt P s = .ok t)
    (ha : D.d5.isAtt P.l = true) (z : Q) :
    pubAll D base (.more (some P.l) "K5.readsThere") (z, t) =
      readsFrontB D.d5.W (D.d5.ownOf P.l) P s.check s.book := by
  rw [pubAll_more_readsThere D base P.l ha (z, t)]
  exact readsThere_opened h _ _

theorem made_liveReq {P : AttPar} {s t : S} (h : openAtt P s = .ok t)
    (ha : D.d5.isAtt P.l = true) (z : Q)
    (hf : liveFrontB (bornOf D.d5.shape P.l) P.l s.check = true) :
    pubAll D base (.more (some P.l) "K5.liveReq") (z, t) = true := by
  rw [pubAll_liveReq_opened D base h ha z, hf]

theorem made_readsThere {P : AttPar} {s t : S} (h : openAtt P s = .ok t)
    (ha : D.d5.isAtt P.l = true) (z : Q)
    (hf : readsFrontB D.d5.W (D.d5.ownOf P.l) P s.check s.book = true) :
    pubAll D base (.more (some P.l) "K5.readsThere") (z, t) = true := by
  rw [pubAll_readsThere_opened D base h ha z, hf]

end

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.liveReq_opened
#print axioms Johnson.Desc.First.Walk.Tied.readsThere_opened
#print axioms Johnson.Desc.First.Walk.Tied.pubAll_liveReq_opened
#print axioms Johnson.Desc.First.Walk.Tied.pubAll_readsThere_opened
#print axioms Johnson.Desc.First.Walk.Tied.made_liveReq
#print axioms Johnson.Desc.First.Walk.Tied.made_readsThere
