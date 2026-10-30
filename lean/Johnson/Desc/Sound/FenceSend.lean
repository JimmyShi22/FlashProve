-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FenceSend.lean: THE FENCE (Johnson/Desc/Sound/Fence.lean): WHAT A BLOCK OWES THE BOOK (`BookKept`) AT A SENDING, at
the fence's term (`bookedOf`); AND WHERE, TO THE NUMBER, A NEW MESSAGE IS SEATED. Two definitions and seven theorems. Rules:
general in the record (readers stOf, bookOf, rootsOf), in the piece and in what the decoder reads of the record (rec).
THE PREMISE ON rec: BookKept's clauses stand under the fence: at EVERY record, for a rec that reads anything of
a message's TREE it is FALSE (a record that places a counted message at a tree which its book does not hold yet: the
receiving appends: the tree turns from none to some). So it is asked UNDER THE FENCE IN FRONT, AT A YES OF
THE PIECE (hR). `seated_of_received`: the rider at plain data, at a NAMED
sending and layout.


  `Received ft sent lay st bk roots st' bk' roots'`: WHAT A RECEIVING WRITES, on plain data, five clauses: the planner's
    layout of the sent messages is lay · statement and book were in step (as many messages as places) · the
    statement has sent.size messages more · the book is the library's book behind such a message
    (`recvBook`, FenceRecv.lean) · the roots are lay.shapes.size more.
  `bookKept_of_recv`: if (hdec) a yes of the piece is a yes of its block's decision from the record in front to the
    record behind, (hyes) a yes of that decision writes what a receiving writes, AS FAR AS THE FENCE READS THE RECORD
    (whatever else the decision does behind the receiving: it may enter samples: it leaves the number of
    messages, the book and the roots), with lay.shapes.size = THE NUMBER OF TREES THAT THE PIECE's STRETCH LISTS, and (hR) UNDER
    THE FENCE IN FRONT, at a yes of the piece, of the messages sent in front rec says behind what it said in front:
    THEN BookKept, all four clauses.
    By FenceRecv.lean's bookSeat_old, bookSeat_new_lt and `lay_lt` (OnBytes/Tie/Pv/Keeps/LayOne.lean: every message
    has a tree among those that the planner returns).
THE RIDER ("the description's seat = lo + n off the record's book": THE
RECORD's HALF):
  `SeatedAt lo low bk o j t`: the book seats message o in the tree with the frame's number j, AT THE PART t within it (the
    part is the second member of the book's place, which `bookSeat` drops).
  `recvBook_place_old`, `recvBook_place_new`, `seatedAt_old`, `seatedAt_new`: at the library's book behind a receiving: a seated
    message keeps tree and part; the i-th new one is seated at lo + (roots + lay.tree i), part lay.part i.
  `seatedNew_of_recv`: AT A YES OF A SENDING's PIECE, UNDER THE FENCE IN FRONT: THE i-th NEW MESSAGE IS SEATED AT THE PIECE's BASE + ITS
    TREE IN THE LAYOUT, AT ITS PART IN THE LAYOUT: one clause sharper than BookKept.new. (The fence's first clause is
    "lo + the roots = the base": so the record's next tree IS the piece's base.)
  For the older messages it follows along the chain: BookKept.old for the tree; `seatedAt_old` for both.
  NOT HERE: the plan's half (which member of the description stands for which message, and that its seat by the
  plan is base + the same tree, the same tenant): left to other files; that the trees and tenants which the sending kind's
  block declares are the layout that the planner lays: left to that kind's files.
WHO PAYS THE PREMISES. hdec: piece_decides_at (Johnson/Desc/Plain/PieceYes.lean) | piece_yes (Johnson/Desc/K14/Law/Bridge.lean): both
proved, general in the record. hyes' five clauses at the ground's own receiving: FenceSendGround.lean. That a kind's
decision IS a receiving and then steps that leave these three: the kind's text. lay.shapes.size = p.trees: the
tiling's data against the kind's declared rounds. rec: where rec is filled.
Nearest kin: BookFits (Johnson/Desc/Book/BookFits.lean: a message stands in its tree's list of parts at its own part number):
ANOTHER CLAUSE ON THE SAME BOOK: it speaks of a place's second member, this of the
tree's source and a bound on its number: no twin, by reading · `OnBytes.Blk.BookKept`
(OnBytes/Iop/OpenLaws.lean: what an OPENING leaves of a book): another thing under a like name.

Every "there is", walked: in hyes: ft, sent, lay: what the decision was handed and what the planner returned.
Limits. A rule under letters: at no real kind here. It closes no row. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FenceRecv
import OnBytes.Tie.Pv.Keeps.LayOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK SgX)

/-- **What a receiving writes**, as far as the fence reads the record. -/
def Received (ft : ℕ) (sent : Array OracleNotice) (lay : TreeLay) (st : Statement) (bk : TreeBook)
    (roots : ℕ) (st' : Statement) (bk' : TreeBook) (roots' : ℕ) : Prop :=
  layTrees st.codes sent = some lay ∧ st.oracles.size = bk.place.size ∧
    st'.oracles.size = st.oracles.size + sent.size ∧
    bk' = recvBook ft bk sent lay st.oracles.size roots ∧ roots' = roots + lay.shapes.size

/-- The book seats message o in the tree with the frame's number j, at the part t within it. -/
def SeatedAt (lo : ℕ) (low : Tree → Option ℕ) (bk : TreeBook) (o j t : ℕ) : Prop :=
  bookSeat lo low bk o = some j ∧ (bk.place[o]?).map (·.2) = some t

/-- An older place stays. -/
theorem recvBook_place_old (ft : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay)
    (n0 roots o : ℕ) (ho : o < bk.place.size) :
    (recvBook ft bk sent lay n0 roots).place[o]? = bk.place[o]? := by
  show (bk.place ++ _)[o]? = _
  rw [Array.getElem?_append_left ho]

/-- The place of the i-th new message. -/
theorem recvBook_place_new (ft : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay)
    (n0 roots i : ℕ) (hi : i < sent.size) :
    (recvBook ft bk sent lay n0 roots).place[bk.place.size + i]? =
      some (bk.trees.size + lay.tree.getD i 0, lay.part.getD i 0) := by
  show (bk.place ++ _)[bk.place.size + i]? = _
  rw [Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    Array.getElem?_map, Array.getElem?_range, if_pos hi]
  rfl

/-- A seated message keeps its tree and its part. -/
theorem seatedAt_old (lo : ℕ) (low : Tree → Option ℕ) (ft : ℕ) (bk : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) (n0 roots o j t : ℕ)
    (h : SeatedAt lo low bk o j t) : SeatedAt lo low (recvBook ft bk sent lay n0 roots) o j t := by
  refine ⟨bookSeat_old lo low ft bk sent lay n0 roots o j h.1, ?_⟩
  have ho : o < bk.place.size := by
    rcases Nat.lt_or_ge o bk.place.size with h1 | h1
    · exact h1
    · have h2 := h.2
      rw [Array.getElem?_eq_none h1] at h2
      cases h2
  rw [recvBook_place_old ft bk sent lay n0 roots o ho]
  exact h.2

/-- Where the i-th new message is seated: tree and part. -/
theorem seatedAt_new (lo : ℕ) (low : Tree → Option ℕ) (ft : ℕ) (bk : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) (n0 roots i : ℕ) (hi : i < sent.size)
    (hτ : lay.tree.getD i 0 < lay.shapes.size) :
    SeatedAt lo low (recvBook ft bk sent lay n0 roots) (bk.place.size + i)
      (lo + (roots + lay.tree.getD i 0)) (lay.part.getD i 0) := by
  refine ⟨bookSeat_new lo low ft bk sent lay n0 roots i hi hτ, ?_⟩
  rw [recvBook_place_new ft bk sent lay n0 roots i hi]
  rfl

/-- **A sending keeps the book.** -/
theorem bookKept_of_recv {S Cl W ρ : Type} {C : CK} {F : Frame} (lo : ℕ) (low : Tree → Option ℕ)
    (stOf : S → Statement) (bookOf : S → TreeBook) (rootsOf : S → ℕ) (rec : S → ℕ → ρ)
    (p : Piece C F S Cl W)
    (hdec : ∀ a τ b, p.ior.red.out a τ = some b → ∃ rs gs, p.b.decide a.1 rs gs = .ok b.1)
    (hyes : ∀ s rs gs s', p.b.decide s rs gs = .ok s' → ∃ ft sent lay,
      Received ft sent lay (stOf s) (bookOf s) (rootsOf s) (stOf s') (bookOf s') (rootsOf s') ∧
        lay.shapes.size = p.trees)
    (hR : ∀ a τ b, FenceAt (bookedOf lo low stOf bookOf rootsOf) p.base a →
      p.ior.red.out a τ = some b → ∀ o, o < (stOf a.1).oracles.size → rec b.1 o = rec a.1 o) :
    BookKept (bookedOf lo low stOf bookOf rootsOf) rec p := by
  have key : ∀ a τ b, p.ior.red.out a τ = some b → ∃ ft sent lay,
      Received ft sent lay (stOf a.1) (bookOf a.1) (rootsOf a.1) (stOf b.1) (bookOf b.1)
        (rootsOf b.1) ∧ lay.shapes.size = p.trees := fun a τ b hb => by
    obtain ⟨rs, gs, hd⟩ := hdec a τ b hb
    exact hyes _ rs gs _ hd
  refine ⟨fun a τ b _ hb => ?_, fun a τ b hf hb o ho => ?_, fun a τ b _ hb => ?_,
    fun a τ b _ hb o h1 h2 => ?_⟩
  · obtain ⟨ft, sent, lay, ⟨_, _, e3, _, _⟩, _⟩ := key a τ b hb
    show (stOf a.1).oracles.size ≤ (stOf b.1).oracles.size
    omega
  · obtain ⟨ft, sent, lay, ⟨_, _, _, e4, _⟩, _⟩ := key a τ b hb
    obtain ⟨j, hj, _⟩ := hf.2 o ho
    refine ⟨hR a τ b hf hb o ho, ?_⟩
    show bookSeat lo low (bookOf b.1) o = bookSeat lo low (bookOf a.1) o
    have hj' : bookSeat lo low (bookOf a.1) o = some j := hj
    rw [e4, hj']
    exact bookSeat_old lo low ft (bookOf a.1) sent lay _ _ o j hj'
  · obtain ⟨ft, sent, lay, ⟨_, _, _, _, e5⟩, ht⟩ := key a τ b hb
    show lo + rootsOf b.1 = lo + rootsOf a.1 + p.trees
    omega
  · obtain ⟨ft, sent, lay, ⟨e1, e2, e3, e4, e5⟩, _⟩ := key a τ b hb
    have h1' : (stOf a.1).oracles.size ≤ o := h1
    have h2' : o < (stOf b.1).oracles.size := h2
    have hi : o - (stOf a.1).oracles.size < sent.size := by omega
    obtain ⟨j, hj, hlt⟩ := bookSeat_new_lt lo low ft (bookOf a.1) sent lay (stOf a.1).oracles.size
      (rootsOf a.1) (o - (stOf a.1).oracles.size) hi (OnBytes.Tie.Pv.Keeps.Fit.lay_lt e1 hi)
    have eo : (bookOf a.1).place.size + (o - (stOf a.1).oracles.size) = o := by omega
    rw [eo] at hj
    refine ⟨j, ?_, ?_⟩
    · show bookSeat lo low (bookOf b.1) o = some j
      rw [e4]
      exact hj
    · show j < lo + rootsOf b.1
      omega

/-- **The rider at plain data**: where a receiving of the messages sent, laid as lay, has written, and the record in
front counted just the trees below B: the i-th new message is seated at B + its tree in the layout, at its part. -/
theorem seated_of_received (lo : ℕ) (low : Tree → Option ℕ) (B ft : ℕ) (sent : Array OracleNotice)
    (lay : TreeLay) (st : Statement) (bk : TreeBook) (roots : ℕ) (st' : Statement) (bk' : TreeBook)
    (roots' : ℕ) (hR : Received ft sent lay st bk roots st' bk' roots') (hB : lo + roots = B) :
    ∀ i, i < sent.size → SeatedAt lo low bk' (st.oracles.size + i) (B + lay.tree.getD i 0)
      (lay.part.getD i 0) := by
  intro i hi
  obtain ⟨e1, e2, _, e4, _⟩ := hR
  have h := seatedAt_new lo low ft bk sent lay st.oracles.size roots i hi
    (OnBytes.Tie.Pv.Keeps.Fit.lay_lt e1 hi)
  rw [← e4, ← e2, ← Nat.add_assoc, hB] at h
  exact h

/-- **THE RIDER: at a yes of a sending's piece, under the fence in front, the i-th new message is seated at the
piece's base + its tree in the layout, at its part in the layout.** -/
theorem seatedNew_of_recv {S Cl W : Type} {C : CK} {F : Frame} (lo : ℕ) (low : Tree → Option ℕ)
    (stOf : S → Statement) (bookOf : S → TreeBook) (rootsOf : S → ℕ) (p : Piece C F S Cl W)
    (hdec : ∀ a τ b, p.ior.red.out a τ = some b → ∃ rs gs, p.b.decide a.1 rs gs = .ok b.1)
    (hyes : ∀ s rs gs s', p.b.decide s rs gs = .ok s' → ∃ ft sent lay,
      Received ft sent lay (stOf s) (bookOf s) (rootsOf s) (stOf s') (bookOf s') (rootsOf s')) :
    ∀ a τ b, FenceAt (bookedOf lo low stOf bookOf rootsOf) p.base a → p.ior.red.out a τ = some b →
      ∃ ft sent lay,
        Received ft sent lay (stOf a.1) (bookOf a.1) (rootsOf a.1) (stOf b.1) (bookOf b.1)
          (rootsOf b.1) ∧
        ∀ i, i < sent.size → SeatedAt lo low (bookOf b.1) ((stOf a.1).oracles.size + i)
          (p.base + lay.tree.getD i 0) (lay.part.getD i 0) := by
  intro a τ b hf hb
  obtain ⟨rs, gs, hd⟩ := hdec a τ b hb
  obtain ⟨ft, sent, lay, hR⟩ := hyes _ rs gs _ hd
  exact ⟨ft, sent, lay, hR, seated_of_received lo low p.base ft sent lay _ _ _ _ _ _ hR hf.1⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.bookKept_of_recv
#print axioms VerifiableInference.Desc.Sound.seatedAt_old
#print axioms VerifiableInference.Desc.Sound.seatedAt_new
#print axioms VerifiableInference.Desc.Sound.seated_of_received
#print axioms VerifiableInference.Desc.Sound.seatedNew_of_recv
