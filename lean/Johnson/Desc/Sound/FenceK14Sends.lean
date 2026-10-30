-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FenceK14Sends.lean: THE FENCE (Johnson/Desc/Sound/Fence.lean) AT K14's TWO SENDINGS, "send o_u" AND "send o_omega": what a
block owes the book (`BookKept`) there, and where, to the number, the new messages are seated: AT THE KIND's OWN BLOCKS
(`blocks P`, Johnson/Desc/K14/Blocks.lean). Ten theorems.
(R) IS ASKED UNDER THE FENCE IN FRONT, AT A YES OF THE PIECE (bare it is false of a rec that reads a
message's tree) · `sends_are` NAMES THE SENDING: the second and the fifth block ARE sendAt P n Q … at a place Q with the plan's codes
(for the rider that is the joint with the plan's half).

The kind's inversions (Johnson/Desc/K14/Law/AtBlocks.lean: layRows_keeps, decideSend_inv, sendAt_inv) say of a sending's yes: the
messages are received; the statement grows. THESE THREE ARE SILENT ON THE BOOK AND THE ROOTS behind the receiving. (Elsewhere the
kind's files have `SameBook d d' := d'.book = d.book ∧ d'.roots = d.roots` and `book_of_blocks` FOR THE SIX BLOCKS THAT SEND NOTHING
(Johnson/Desc/K14/Law/KeepsMsgs.lean): the two sendings are not among them: no twin; where both lie, `behindU_book` and its
like can be said with SameBook.) This file's names lie
in a namespace of their own, Desc.K14.Law.Fence, beneath the kind's. Here, by the same
walks over the same texts:
  `layRows_book`: the laying of the sample rows leaves the book, the roots and the number of messages.
  `decideSend_book`: a yes of the sending's decision: the ground's receiving, and then these three as they were.
  `behindU_book`, `behindOmega_book`: what the kind notes behind a sending turns the small record alone.
  `sendAt_received`: SO A YES OF A SENDING AT THIS CHAIN's STATE WRITES WHAT A RECEIVING WRITES (`Received`, FenceSend.lean), from the
    record in front to the record behind.
  `sends_are`: the second and the fifth of `blocks P` are sendings at this chain, at places with the plan's codes, whose notes
    behind turn the small record alone. `sends_received`: so they write what a receiving writes.
  `oraclesOf_length`: the block declares as many trees as the planner's layout has shapes.
  `bookKept_at_send`: BookKept (bookedOf lo low (·.st) (·.book) (·.roots)) rec pc, for a piece pc that holds the second or the
    fifth block: UNDER TWO PREMISES: (T) the piece's stretch lists as many trees as the layout has shapes [paid from one
    fact on the data in FenceK14Roots.lean] · (R) UNDER THE FENCE IN FRONT, at a yes of the piece: of the messages sent in
    front rec says behind what it said in front.
  `seatedNew_at_send`: THE RIDER: under the fence in front the i-th new message is seated at pc.base + its tree in the
    layout, at its part in the layout: NO PREMISE BUT THE FENCE.
By `piece_yes` (Johnson/Desc/K14/Law/Bridge.lean), FenceSend.lean's bookKept_of_recv, seatedNew_of_recv, FenceSendGround.lean's recvP_received.
WHAT IS LEFT. (T): with oraclesOf_length: "the stretch lists the trees that the block declares" (the tiling's data) and "the
record's codes are the place's" (the decision's own test). (R): where rec is filled (the decoder's files).

Every "there is", walked: ft, sent, lay: the place's first tree, the place's messages, what the planner returned.
Limits. Book-keeping: no chance, no game. It closes no row. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FenceSendGround
import Johnson.Desc.K14.Law.AtBlocks
import Johnson.Desc.K14.Law.Bridge
import Johnson.Desc.Own.TreesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Grows Block named need)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (decideSend layRows sendOwn Owing)
open VerifiableInference.Desc.Sound (Frame Piece Received BookKept FenceAt SeatedAt bookedOf
  bookKept_of_recv seatedNew_of_recv)
open _root_.Run.PQ (CK)

/-- The laying of the sample rows leaves the book, the roots and the number of messages. -/
theorem layRows_book {L : Type} (codes : Codes) (seeds : List (List E × E)) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L),
      layRows codes seeds l ys d = .ok d' →
      d'.book = d.book ∧ d'.roots = d.roots ∧ d'.st.oracles.size = d.st.oracles.size := by
  intro l
  induction l with
  | nil =>
    intro ys d d' h
    simp only [layRows] at h
    split at h
    · cases h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  | cons x l ih =>
    intro ys d d' h
    obtain ⟨o, s⟩ := x
    simp only [layRows] at h
    split at h
    · exact ih _ _ _ h
    · split at h
      · cases h
      · split at h
        · cases h
        · obtain ⟨d1, h1, h2⟩ := ebind_ok h
          have h1' := named_some h1
          obtain ⟨b2, r2, s2⟩ := ih _ _ _ h2
          unfold admitP at h1'
          split at h1'
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h1'
            obtain ⟨y, _, places, _, rfl⟩ := h1'
            refine ⟨b2, r2, s2.trans ?_⟩
            simp [admitted]
          · cases h1'

/-- A yes of the sending's decision: the receiving, and then the book, the roots and the number of messages as
they were. -/
theorem decideSend_book {L : Type} (Q : VerifiableInference.Desc.K1.Par) (owed : Option Nat)
    (d : DState L) (rs : List Fmt.RoundView) (ids : Array Nat) (d' : DState L)
    (h : decideSend Q owed d rs = .ok (ids, d')) :
    ∃ x1, recvP Q.gp.firstTree d Q.sent = some (ids, x1) ∧ d'.book = x1.book ∧
      d'.roots = x1.roots ∧ d'.st.oracles.size = x1.st.oracles.size := by
  unfold decideSend at h
  split at h
  · obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨x, hx, h⟩ := dbind_ok h
    obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨_, _, h⟩ := dbind_ok h
    obtain ⟨d2, hl, h⟩ := dbind_ok h
    cases h
    exact ⟨x.2, named_some hx, layRows_book _ _ _ _ _ _ hl⟩
  · cases h

/-- What the kind notes behind o_u's sending turns the small record alone. -/
theorem behindU_book (p : Par) (d : St) (ids : Array Nat) (d' : St)
    (h : behindU p d ids = some d') : d'.st = d.st ∧ d'.book = d.book ∧ d'.roots = d.roots := by
  unfold behindU at h
  simp only [Option.bind_eq_bind] at h
  split at h <;>
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨mask, _, o, ho, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- The like behind o_omega's. -/
theorem behindOmega_book (p : Par) (d : St) (ids : Array Nat) (d' : St)
    (h : behindOmega p d ids = some d') :
    d'.st = d.st ∧ d'.book = d.book ∧ d'.roots = d.roots := by
  unfold behindOmega at h
  simp only [Option.bind_eq_bind] at h
  split at h <;>
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨sp, _, o, ho, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- **A yes of a sending at this chain's state writes what a receiving writes.** -/
theorem sendAt_received (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') :
    ∃ lay, Received Q.gp.firstTree Q.sent lay d.st d.book d.roots d'.st d'.book d'.roots := by
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  obtain ⟨x1, hr, eb, er, es⟩ := decideSend_book Q none _ rs ids x2 hx
  obtain ⟨lay, r1, r2, r3, r4, r5⟩ := VerifiableInference.Desc.K1.recvP_received _ _ _ _ _ hr
  obtain ⟨e1, e2, e3⟩ := hb _ _ _ (named_some h)
  refine ⟨lay, r1, r2, ?_, ?_, ?_⟩
  · rw [e1]
    exact es.trans r3
  · rw [e2]
    exact eb.trans r4
  · rw [e3]
    exact er.trans r5

/-- **The second and the fifth of the kind's eight blocks ARE sendings at this chain**, at places with the plan's
codes; what they note behind turns the small record alone. -/
theorem sends_are (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ b, b = b2 ∨ b = b5 → ∃ n Q inFront groups behind, b = sendAt P n Q inFront groups behind ∧
      Q.codes = P.codes ∧
      ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  rintro b (rfl | rfl)
  · exact ⟨_, _, _, _, _, rfl, rfl, behindU_book P.par⟩
  · exact ⟨_, _, _, _, _, rfl, rfl, behindOmega_book P.par⟩

/-- So they write what a receiving writes. -/
theorem sends_received (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ b, b = b2 ∨ b = b5 → ∀ d rs gs d', b.decide d rs gs = .ok d' →
      ∃ ft sent lay, Received ft sent lay d.st d.book d.roots d'.st d'.book d'.roots := by
  intro b hb d rs gs d' h
  obtain ⟨n, Q, inFront, groups, behind, rfl, _, hbk⟩ := sends_are P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb
  exact ⟨_, _, sendAt_received P n Q inFront groups behind hbk d d' rs gs h⟩

/-- The block declares as many trees as the planner's layout has shapes. -/
theorem oraclesOf_length (codes : Codes) (sent : Array OracleNotice) (groups : List (List Nat))
    (lay : TreeLay) (h : layTrees codes sent = some lay) :
    (oraclesOf codes sent groups).length = lay.shapes.size := by
  unfold oraclesOf
  -- one text for two grounds: oraclesOf lays the trees by the program's layTrees, or by the description's own treesMade
  first
    | rw [h]
    | rw [VerifiableInference.Desc.Own.treesMade_eq, h]
  simp

variable {W ρ : Type} {F : Frame} {C : CK}

/-- **BookKept at K14's two sendings.** -/
theorem bookKept_at_send (lo : ℕ) (low : Tree → Option ℕ) (rec : St → ℕ → ρ) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pc : Piece C F St Unit W)
    (hpc : pc.b = b2 ∨ pc.b = b5)
    (hT : ∀ d d' ft sent lay, Received ft sent lay d.st d.book d.roots d'.st d'.book d'.roots →
      (∃ rs gs, pc.b.decide d rs gs = .ok d') → lay.shapes.size = pc.trees)
    (hR : ∀ a τ b,
      FenceAt (bookedOf lo low (fun d : St => d.st) (fun d => d.book) (fun d => d.roots)) pc.base a →
      pc.ior.red.out a τ = some b → ∀ o, o < a.1.st.oracles.size → rec b.1 o = rec a.1 o) :
    BookKept (bookedOf lo low (fun d : St => d.st) (fun d => d.book) (fun d => d.roots)) rec pc :=
  bookKept_of_recv lo low _ _ _ rec pc
    (fun a τ b hb => by
      obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hb
      exact ⟨_, gs, hd⟩)
    (fun d rs gs d' h => by
      obtain ⟨ft, sent, lay, hRc⟩ := sends_received P b1 b2 b3 b4 b5 b6 b7 b8 hbl pc.b hpc d rs gs d' h
      exact ⟨ft, sent, lay, hRc, hT d d' ft sent lay hRc ⟨rs, gs, h⟩⟩)
    hR

/-- **THE RIDER at K14's two sendings**: under the fence in front the i-th new message is seated at the piece's
base + its tree in the layout, at its part in the layout. -/
theorem seatedNew_at_send (lo : ℕ) (low : Tree → Option ℕ) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pc : Piece C F St Unit W)
    (hpc : pc.b = b2 ∨ pc.b = b5) :
    ∀ a τ b,
      FenceAt (bookedOf lo low (fun d : St => d.st) (fun d => d.book) (fun d => d.roots)) pc.base a →
      pc.ior.red.out a τ = some b →
      ∃ ft sent lay,
        Received ft sent lay a.1.st a.1.book a.1.roots b.1.st b.1.book b.1.roots ∧
        ∀ i, i < sent.size → SeatedAt lo low b.1.book (a.1.st.oracles.size + i)
          (pc.base + lay.tree.getD i 0) (lay.part.getD i 0) :=
  seatedNew_of_recv lo low _ _ _ pc
    (fun a τ b hb => by
      obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hb
      exact ⟨_, gs, hd⟩)
    (fun d rs gs d' h => sends_received P b1 b2 b3 b4 b5 b6 b7 b8 hbl pc.b hpc d rs gs d' h)

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.sendAt_received
#print axioms Desc.K14.Law.Fence.sends_are
#print axioms Desc.K14.Law.Fence.sends_received
#print axioms Desc.K14.Law.Fence.oraclesOf_length
#print axioms Desc.K14.Law.Fence.bookKept_at_send
#print axioms Desc.K14.Law.Fence.seatedNew_at_send
