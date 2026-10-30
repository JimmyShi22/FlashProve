-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstFold.lean: THE FOLD FACTS BESIDE THE SHARED TABLE's CONSTANT
(Johnson/Desc/K14/Law/SharedConst.lean): the third named list, closed, beside
the one premise that the verifier's own value is laid and the named tests on the parameters.
A FOLD FACT is a fact on the verifier's state that holds at every state that the verifier's own
steps reach. HERE ONLY facts on THE FIRST CHAIN's LAST STATE, AS IT IS HANDED TO THE SHARED CHAIN
((O.get a.1.1).2), that the ledger's tops ask as premises or read inside the first chain's
last promise. What the shared chain's own walk keeps (Sh.X) is no fold fact: it stays in the
promise.

  BookInOrder, EveryPlaced, CodesAre, FarFrom     the four facts, each a Prop on one state
  Sh.FoldFacts A O            ONE STRUCTURE, A FIELD A FACT: ∀ p, O.R p → at a state without a mark
                              → the fact. O.R ("p is a reached last state of the first chain") is
                              an open letter of the constant, and stands in the slot's own
                              condition Sh.own. No sub-protocol of the shared chain turns p: so one
                              predicate serves at every border.
  Sh.foldList                 the fields' names, for the count
  Sh.tabP₁_at_book            at one state: the constant's reader of tables, by the book's own place
  Sh.sz_of_placed             at one state: the book has a place for every message
  Sh.paid_htab                the top's htab, at the constant's reader of tables: no premise
  Sh.hbook_of                 the top's hbook, in its own words, from the first two facts asked
                              inside the first chain's last promise
  Sh.hbook_reached            the same sentence at every reached state, from FoldFacts
  Sh.hbook_own, hcod_own, hsz_own, hfar_own     **the four sentences inside Sh.own, from FoldFacts**
WHOSE EACH IS, AND WHETHER IT LIES, stands at its field.
HOW. tabP₁_at_book, paid_htab and hbook_of are calls of tabFirst_at_book
(Johnson/Desc/Sound/HbookFirst.lean), htab_first and hbook_tabFirst
(Johnson/Desc/Sound/LettersFirst.lean).
WHAT IS NOT HERE. No law. No proof of a fold fact: each is an induction along the FIRST chain.
That the ledger's tops stand at Sh.own: they name the first chain's last promise by an equation.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open OnBytes.Means

/-- The book numbers its trees in order. -/
def BookInOrder (s : First.S) : Prop :=
  ∀ (z : ℕ) (T : Tree), s.book.trees[z]? = some T → T.number = z

/-- Every message of the statement has a place in the book, at a tree that is there. -/
def EveryPlaced (s : First.S) : Prop :=
  ∀ o, o < s.st.oracles.size → ∃ q : ℕ × ℕ, s.book.place[o]? = some q ∧ q.1 < s.book.trees.size

/-- The statement's codes. -/
def CodesAre (cs : Codes) (s : First.S) : Prop := s.st.codes = cs

/-- No place of the book is a tenant of the shared chain's three messages, nor has its number. -/
def FarFrom (arr : ℕ → ℕ → ℕ) (N : NumbersS) (s : First.S) : Prop :=
  ∀ n j t : ℕ, s.book.place[n]? = some (j, t) → ∀ m : Msg2,
    arr (N.tenant m).1 (N.tenant m).2 ≠ arr j t ∧ N.tenant m ≠ (j, t)

namespace Sh

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-- **The fold facts.** -/
structure FoldFacts : Prop where
  /-- The first chain's book numbers its trees in order. BOOKED: owed at a reached last state of the
      first chain; at one state it follows from two tests on the book and the equal counts of places
      and messages (bookFacts_of_tests, Johnson/Desc/K14/Law/BookFactsOfTests.lean);
      spent by the top's hbook (Sh.hbook_own). -/
  hb2 : ∀ p, O.R p → (O.get p).2.failed = none → BookInOrder (O.get p).2
  /-- Every message of the first chain's statement has a place in the book, at a tree that is there.
      BOOKED: owed at a reached last state; at one state: as hb2; spent by the top's hbook, and by
      hsz of evKept_of (Sh.hsz_own). -/
  hb3 : ∀ p, O.R p → (O.get p).2.failed = none → EveryPlaced (O.get p).2
  /-- The first chain's statement has the parameters' codes. BOOKED: owed at a reached last state;
      spent by hcod of evKept_of (Johnson/Desc/Sound/EvalKept.lean: it pays the
      top's ev9 | ev10). -/
  hcod : ∀ p, O.R p → (O.get p).2.failed = none → CodesAre A.Q.codes (O.get p).2
  /-- No place of the first chain's book is a tenant of the shared chain's three messages, nor has
      its number. BOOKED: owed at a reached last state; at the seat's numbering it comes down to
      five closed tests and "the book's places are the first of the written list's"
      (Sh.foldFacts_at, Johnson/Desc/K14/Law/SharedConstFar.lean); spent by hfar of evKept_of. -/
  hfar : ∀ p, O.R p → (O.get p).2.failed = none → FarFrom O.arr (nums A O) (O.get p).2

/-- The fields' names. -/
def foldList : List String := ["hb2", "hb3", "hcod", "hfar"]

/-- The top's htab: the reader of tables reads of a witness its messages and pads alone. -/
theorem paid_htab : ∀ a (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) →
    (∀ j t, w'.pad j t = w.pad j t) → tabP₁ A O a w' = tabP₁ A O a w :=
  htab_first O.arr

/-- **At one state: the reader's table, by the book's own place.** -/
theorem tabP₁_at_book (a : P₀ × First.S) (h₂ : BookInOrder a.2) (h₃ : EveryPlaced a.2)
    (w : Wit Cells Tok MsgT) (n j t : ℕ) (sh : OracleShape)
    (hp : a.2.book.place[n]? = some (j, t)) (hs : (a.2.st.oracles[n]?).map (·.shape) = some sh) :
    tabP₁ A O a w n = w.tab a.2.st.codes sh (O.arr j t) j t :=
  tabFirst_at_book O.arr a.2.st a.2.book h₂ h₃ w n j t sh hp hs

/-- At one state: the book has a place for every message of the statement. -/
theorem sz_of_placed (s : First.S) (h₃ : EveryPlaced s) :
    s.st.oracles.size ≤ s.book.place.size := by
  by_contra hc
  obtain ⟨q, hq, _⟩ := h₃ s.book.place.size (Nat.lt_of_not_le hc)
  rw [Array.getElem?_eq_none (Nat.le_refl _)] at hq
  cases hq

/-- **The top's hbook, in its own words**, from the two facts on the book, asked inside the first
chain's last promise. -/
theorem hbook_of
    (h₂ : ∀ p y, ocEnd O.get O.N₁ (mg₁ A O) O.links (ps A O) p y →
      (O.get p).2.failed = none → BookInOrder (O.get p).2)
    (h₃ : ∀ p y, ocEnd O.get O.N₁ (mg₁ A O) O.links (ps A O) p y →
      (O.get p).2.failed = none → EveryPlaced (O.get p).2) :
    ∀ p y, ocEnd O.get O.N₁ (mg₁ A O) O.links (ps A O) p y → (O.get p).2.failed = none →
      (O.get p).2.st.codes = A.Q.codes →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (O.get p).2.book.place[n]? = some (j, t) →
      ((O.get p).2.st.oracles[n]?).map (·.shape) = some sh →
      tabP₁ A O (O.get p) w n = w.tab A.Q.codes sh (O.arr j t) j t :=
  hbook_tabFirst A.Q.codes O.arr O.get O.N₁ (mg₁ A O) O.links (ps A O) h₂ h₃

/-- **The same sentence at every reached state**, from the fold facts. -/
theorem hbook_reached (F : FoldFacts A O) :
    ∀ p, O.R p → (O.get p).2.failed = none →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (O.get p).2.book.place[n]? = some (j, t) →
      ((O.get p).2.st.oracles[n]?).map (·.shape) = some sh →
      tabP₁ A O (O.get p) w n = w.tab A.Q.codes sh (O.arr j t) j t := by
  intro p hr hm w n j t sh hp hs
  rw [tabP₁_at_book A O _ (F.hb2 p hr hm) (F.hb3 p hr hm) w n j t sh hp hs, F.hcod p hr hm]

/-- **Inside the slot's own condition**, from the fold facts: the sentences that the top's hbook and
evKept_of ask. -/
theorem hbook_own (F : FoldFacts A O) :
    ∀ p y, own A O p y → (O.get p).2.failed = none → (O.get p).2.st.codes = A.Q.codes →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (O.get p).2.book.place[n]? = some (j, t) →
      ((O.get p).2.st.oracles[n]?).map (·.shape) = some sh →
      tabP₁ A O (O.get p) w n = w.tab A.Q.codes sh (O.arr j t) j t :=
  fun p _ ho hm _ => hbook_reached A O F p (own_R A O ho) hm

theorem hcod_own (F : FoldFacts A O) :
    ∀ p y, own A O p y → (O.get p).2.failed = none → (O.get p).2.st.codes = A.Q.codes :=
  fun p _ ho hm => F.hcod p (own_R A O ho) hm

theorem hsz_own (F : FoldFacts A O) : ∀ p y, own A O p y → (O.get p).2.failed = none →
    (O.get p).2.st.oracles.size ≤ (O.get p).2.book.place.size :=
  fun p _ ho hm => sz_of_placed _ (F.hb3 p (own_R A O ho) hm)

theorem hfar_own (F : FoldFacts A O) : ∀ p y, own A O p y → (O.get p).2.failed = none →
    FarFrom O.arr (nums A O) (O.get p).2 :=
  fun p _ ho hm => F.hfar p (own_R A O ho) hm

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.tabP₁_at_book
#print axioms Desc.K14.Law.Sh.sz_of_placed
#print axioms Desc.K14.Law.Sh.paid_htab
#print axioms Desc.K14.Law.Sh.hbook_of
#print axioms Desc.K14.Law.Sh.hbook_reached
#print axioms Desc.K14.Law.Sh.hbook_own
#print axioms Desc.K14.Law.Sh.hfar_own
