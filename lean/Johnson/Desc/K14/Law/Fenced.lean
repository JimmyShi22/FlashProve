--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/Fenced.lean: THE PROMISE OF THE ROW OF THE EIGHT AS A TERM, BORDER BY BORDER,
AND "THE PIN GOES BACK, THE PROMISE IS KEPT" (Carries, Johnson/Desc/K14/Law/Borders.lean) PAID AT
ALL EIGHT PIECES FOR EVERY DECODER OF A FORM THAT READS THE TREES.

Why. A piece writes or clears every tree from its own base on. So "of the messages sent in front the
decoder reads behind the block what it read in front" is false at a statement whose record seats a
message in a tree at or above that base. No run reaches such a statement. The row asks "the pin goes
back" under the promise of the border in front alone: so the promise says that the record is none
such: THE FENCE (Johnson/Desc/Sound/Fence.lean: FenceAt): the record counts just the trees below the
base of the piece behind the border as sent, and seats every message that it counts in one of them.
ONE TEXT: the fence, its rules (backUnder, fenceStep) and what a sending owes the book
(Johnson/Desc/Sound/FenceK14Sends.lean: bookKept_at_send) are another file's: CALLED, not typed
anew.
  bookK           what the fence reads of this chain's record: that file's term bookedOf at the
                  record's statement, book of trees and count of roots. lo: the number, in the
                  frame's list of all trees, of the chain's first own tree. low: the number there of
                  a tree that was taken over from an earlier chain.
  recK            what a decoder may read of the record on message o: the codes; the message's
                  shape, mark "sampled" and sample rows; the book's whole place of o.
  pinF_iff        the functional pin (Johnson/Desc/K14/Law/FunPin.lean) IS the fence's file's, at
                  bookK.
  bookKept_quiet, bookKept_six   what a block owes the book, at the six blocks that send nothing:
                  from msgs_of_blocks and book_of_blocks (Johnson/Desc/K14/Law/KeepsMsgs.lean),
                  where the piece's stretch lists no tree.
  sendAt_old, old_at_sends, recK_at_sends   at the two sendings the record says of an older message
                  what it said: by the sending kind's decideSend_old.
  bookKept_two    so what a block owes the book at the two sendings: bookKept_at_send's second
                  premise is paid; its first stays: the stretch lists as many trees as the planner's
                  layout has shapes.
  shapes_at_sends that first premise, from one fact on the public data: the stretch lists as many
                  trees as the block's declared rounds have roots: by the fence's
                  hT_of_data (Johnson/Desc/Sound/FenceK14Roots.lean): CALLED.
  PrmAt           **the promise's letter as a term**: the fence at B, and PrmK (no collision at the
                  key's seeds; the key fits: Johnson/Desc/K14/Law/MemberKey.lean).
  carriesAt       **Carries from the fence's rules**: under a promise in front that gives PrmAt at
                  the piece's base: the pin goes back (backUnder); behind stands PrmAt at the base
                  plus the stretch's trees (fenceStep, keepK).
  carriesSix, carriesTwo   at a piece that holds one of the six; one of the two.
  fence_head      a record without a message and without a root has the fence at lo.
  vecPiece_trees, posPiece_trees, sendPiece_trees   how many trees these pieces' stretches list.
  decOf, readsSeat_decOf   **a decoder that reads the trees, in its general form**: of message o it
                  is any function delta of: what rec reads of the record on o; the number, in the
                  frame's list, of the tree in which the book seats o; that tree's columns. EVERY
                  SUCH DECODER meets the fence's file's condition ReadsSeat.
  decVOf, readsLow_decVOf   the like for the other vector: any function of what recV reads of the
                  record, the stored table, and the trees below lo: it meets ReadsLow.

What is not claimed. In carriesAt and its two corollaries D and DV are letters under the fence's
file's two conditions. decOf and decVOf are FORMS: delta and deltaV stay letters: which function
decodes is said nowhere here; a decoder that reads of message o anything beyond recK and o's own
tree is not of the form: so where a tree has several tenants, the widths of the tenants in front of
o's have to come from the plan (delta may hold any public value), not from the record's other
entries. THAT ANY STATEMENT MEETS PrmAt IS NOT SHOWN. On a chain that takes trees
over, low has to be filled. No chance, no game. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.MemberKey
import Johnson.Desc.K14.Law.KeepsMsgs
import Johnson.Desc.K1.Law.GoodSend5
import Johnson.Desc.Sound.FenceK14Roots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block named need)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (SameMsgs OldMsgs decideSend decideSend_old sendOwn sendPiece
  size_of_same)
open VerifiableInference.Desc.Sound (Frame Piece Booked FenceAt BookKept ReadsSeat ReadsLow
  bookedOf bookSeat backUnder fenceStep fence_start Received recvBook_place_old strsOf)
open _root_.Run.PQ (CK)

/-- **What the fence reads of this chain's record.** -/
def bookK (lo : Nat) (low : OnBytes.Tree → Option Nat) : Booked St :=
  bookedOf lo low (fun d : St => d.st) (fun d => d.book) (fun d => d.roots)

/-- The type of what recK reads. -/
abbrev RecK : Type :=
  Codes × Option (OracleShape × Bool × Array Row) × Option (Nat × Nat)

/-- **What a decoder may read of the record on message o**: the codes; the message's shape, mark and
sample rows; the book's whole place of o (the tree's number in the book; the part's number in the
tree). Nothing of a tree's value. -/
def recK (d : St) (o : Nat) : RecK :=
  (d.st.codes,
    (d.st.oracles[o]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)),
    d.book.place[o]?)

/-- "Agree on message o", as the fence's file takes it. -/
abbrev agK : Nat → Words GE → Words GE → Prop := fun o m m' => AgreeOn o m m'

variable {W : Type} {F : Frame}

/-- How many trees the stretch of a piece at one written round that draws elements lists. -/
theorem vecPiece_trees (b : Block St Unit) (base : Nat) (d : RDT) (n e : Nat) :
    (vecPiece (W := W) (F := F) b base d n e).trees = d.trees.length := by
  simp [Piece.trees, vecPiece]

/-- The like where positions are drawn. -/
theorem posPiece_trees (b : Block St Unit) (base : Nat) (d : RDT) (a t e : Nat) :
    (posPiece (W := W) (F := F) b base d a t e).trees = d.trees.length := by
  simp [Piece.trees, posPiece]

/-- The like at the two written rounds of a sending. -/
theorem sendPiece_trees (b : Block St Unit) (base : Nat) (d₁ d₂ : RDT) (c e : Nat) :
    (sendPiece (W := W) (F := F) b base d₁ d₂ c e).trees =
      d₁.trees.length + d₂.trees.length := by
  simp [Piece.trees, sendPiece]

/-- A record without a message and without a root has the fence at lo. (This kind's first border
lies behind the chain's front block: so this pays the fence there only where that block brings no
message and no root.) -/
theorem fence_head (lo : Nat) (low : OnBytes.Tree → Option Nat) (x : St × F.E.Str)
    (h0 : x.1.st.oracles.size = 0) (hr : x.1.roots = 0) : FenceAt (bookK lo low) lo x :=
  fence_start (bookK lo low) lo x h0 (by
    show lo + x.1.roots = lo
    rw [hr, Nat.add_zero])

/-! ## What a block owes the book -/

/-- **A block that leaves the messages, the book and the roots, with a stretch that lists no tree,
keeps the book.** -/
theorem bookKept_quiet {C : CK} (lo : Nat) (low : OnBytes.Tree → Option Nat)
    (pc : Piece C F St Unit W)
    (hm : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → SameMsgs d.st d'.st)
    (hb : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → SameBook d d') (ht : pc.trees = 0) :
    BookKept (bookK lo low) recK pc := by
  have yes : ∀ a τ b, pc.ior.red.out a τ = some b → SameMsgs a.1.st b.1.st ∧ SameBook a.1 b.1 := by
    intro a τ b hout
    obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hout
    exact ⟨hm _ _ gs _ hd, hb _ _ gs _ hd⟩
  refine ⟨fun a τ b _ hout => ?_, fun a τ b _ hout o _ => ⟨?_, ?_⟩, fun a τ b _ hout => ?_,
    fun a τ b _ hout o h1 h2 => ?_⟩
  · exact Nat.le_of_eq (size_of_same (yes a τ b hout).1).symm
  · obtain ⟨hs, hk⟩ := yes a τ b hout
    unfold recK
    rw [hs.1, hs.2 o, hk.1]
  · show bookSeat lo low b.1.book o = bookSeat lo low a.1.book o
    rw [(yes a τ b hout).2.1]
  · show lo + b.1.roots = lo + a.1.roots + pc.trees
    rw [(yes a τ b hout).2.2, ht, Nat.add_zero]
  · have e : b.1.st.oracles.size = a.1.st.oracles.size := size_of_same (yes a τ b hout).1
    have h2' : o < b.1.st.oracles.size := h2
    have h1' : a.1.st.oracles.size ≤ o := h1
    rw [e] at h2'
    exact absurd h2' (Nat.not_lt.2 h1')

/-- **At the six blocks that send nothing**; two codes. -/
theorem bookKept_six {C : CK} (lo : Nat) (low : OnBytes.Tree → Option Nat) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (pc : Piece C F St Unit W)
    (hpc : pc.b ∈ [b1, b3, b4, b6, b7, b8]) (ht : pc.trees = 0) :
    BookKept (bookK lo low) recK pc :=
  bookKept_quiet lo low pc (msgs_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS pc.b hpc)
    (book_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS pc.b hpc) ht

/-- A yes of a sending at this chain's state leaves the codes and every older message's shape, mark
and sample rows. -/
theorem sendAt_old (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ a ids e, behind a ids = some e → e.st = a.st)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') : OldMsgs d.st d'.st := by
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  have o := decideSend_old Q none _ x2 rs ids hx
  rw [hb _ _ _ (named_some h)]
  exact o

/-- So at the second and the fifth of the eight blocks. -/
theorem old_at_sends (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ b, b = b2 ∨ b = b5 → ∀ d rs gs d', b.decide d rs gs = .ok d' → OldMsgs d.st d'.st := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  rintro b (rfl | rfl) d rs gs d' h
  · exact sendAt_old P _ _ _ _ _ (fun a ids e k => (behindU_inv P.par a e ids k).1) d d' rs gs h
  · exact sendAt_old P _ _ _ _ _ (fun a ids e k => (behindOmega_inv P.par a e ids k).1) d d' rs gs
      h

/-- **At the two sendings the record says of an older message what it said.** -/
theorem recK_at_sends (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ b, b = b2 ∨ b = b5 → ∀ d rs gs d', b.decide d rs gs = .ok d' →
      ∀ o, o < d.st.oracles.size → recK d' o = recK d o := by
  intro b hb d rs gs d' h o ho
  obtain ⟨ft, sent, lay, _, hstep, _, hbk, _⟩ :=
    Fence.sends_received P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb d rs gs d' h
  have hold := old_at_sends P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb d rs gs d' h
  unfold recK
  rw [hold.1, hold.2 o ho, hbk,
    recvBook_place_old ft d.book sent lay d.st.oracles.size d.roots o (Nat.lt_of_lt_of_eq ho hstep)]

/-- **At the two sendings.** hT: the piece's stretch lists as many trees as the planner's layout has
shapes. The called rule asks "of the older messages rec says behind what it said in front" under the
fence; it is paid here without the fence, at every record: recK reads no tree's value. -/
theorem bookKept_two {C : CK} (lo : Nat) (low : OnBytes.Tree → Option Nat) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pc : Piece C F St Unit W)
    (hpc : pc.b = b2 ∨ pc.b = b5)
    (hT : ∀ d d' ft sent lay, Received ft sent lay d.st d.book d.roots d'.st d'.book d'.roots →
      (∃ rs gs, pc.b.decide d rs gs = .ok d') → lay.shapes.size = pc.trees) :
    BookKept (bookK lo low) recK pc :=
  Fence.bookKept_at_send lo low recK P b1 b2 b3 b4 b5 b6 b7 b8 hbl pc hpc hT
    (fun a τ b _ hout o ho => by
      obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hout
      exact recK_at_sends P b1 b2 b3 b4 b5 b6 b7 b8 hbl pc.b hpc _ _ gs _ hd o ho)

/-- **The first premise of bookKept_at_send, from one fact on the data**: T, the number of trees
that the piece's stretch lists, is the sum of the roots of the block's declared rounds. -/
theorem shapes_at_sends (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b = b2 ∨ b = b5) (T : Nat) (hD : T = (b.rounds.map (·.entry.roots)).sum) :
    ∀ (d d' : St) ft sent lay,
      Received ft sent lay d.st d.book d.roots d'.st d'.book d'.roots →
      (∃ rs gs, b.decide d rs gs = .ok d') → lay.shapes.size = T := by
  obtain ⟨n, Q, inFront, groups, behind, rfl, _, hbk⟩ :=
    Fence.sends_are P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb
  exact Fence.hT_of_data P n Q inFront groups behind hbk T hD

/-! ## A decoder that reads the trees -/

/-- **A decoder of the chain's own messages, in its general form**: of message o: any function of
what rec reads of the record on o, of the number of the tree in which the book seats o, and of that
tree's columns. -/
def decOf {ρ : Type} (lo : Nat) (low : OnBytes.Tree → Option Nat) (rec : St → Nat → ρ)
    (δ : Nat → ρ → Option (Nat × (Nat → List UInt64)) → Words GE) (x : St × F.E.Str) : Words GE :=
  fun o =>
    δ o (rec x.1 o) ((bookSeat lo low x.1.book o).map fun j => (j, (strsOf F x.2).col j)) o

/-- **Every such decoder meets the fence's condition on a decoder.** -/
theorem readsSeat_decOf {ρ : Type} (lo : Nat) (low : OnBytes.Tree → Option Nat)
    (rec : St → Nat → ρ) (δ : Nat → ρ → Option (Nat × (Nat → List UInt64)) → Words GE) :
    ReadsSeat (bookK lo low) rec agK (decOf (F := F) lo low rec δ) := by
  intro x x' o j hx hx' hr hc i
  have hx1 : bookSeat lo low x.1.book o = some j := hx
  have hx2 : bookSeat lo low x'.1.book o = some j := hx'
  have hcol : (strsOf F x'.2).col j = (strsOf F x.2).col j := funext hc
  show δ o (rec x.1 o) ((bookSeat lo low x.1.book o).map fun j => (j, (strsOf F x.2).col j)) o
      .main i =
    δ o (rec x'.1 o) ((bookSeat lo low x'.1.book o).map fun j => (j, (strsOf F x'.2).col j)) o
      .main i
  rw [hx1, hx2, hr]
  simp only [Option.map_some, hcol]

/-- **A decoder of the other vector, in its general form**: any function of what recV reads of the
record, of the stored table, and of the trees below lo. -/
def decVOf {ρ' : Type} (lo : Nat) (recV : St → ρ')
    (δV : ρ' → (Nat → Option (Nat × List UInt64)) → (Nat → Nat → List UInt64) → Nat → GE)
    (x : St × F.E.Str) : Nat → GE :=
  δV (recV x.1) (strsOf F x.2).cell fun j z => if j < lo then (strsOf F x.2).col j z else []

/-- **Every such decoder meets the fence's condition on a decoder of what an earlier chain
sent.** -/
theorem readsLow_decVOf {ρ' : Type} (lo : Nat) (recV : St → ρ')
    (δV : ρ' → (Nat → Option (Nat × List UInt64)) → (Nat → Nat → List UInt64) → Nat → GE) :
    ReadsLow lo recV (decVOf (F := F) lo recV δV) := by
  intro x x' hr hcell hcol
  have e1 : (strsOf F x'.2).cell = (strsOf F x.2).cell := funext hcell
  have e2 : (fun j z => if j < lo then (strsOf F x'.2).col j z else []) =
      fun j z => if j < lo then (strsOf F x.2).col j z else [] := by
    funext j z
    by_cases h : j < lo
    · rw [if_pos h, if_pos h, hcol j z h]
    · rw [if_neg h, if_neg h]
  unfold decVOf
  rw [hr, e1, e2]

/-! ## The promise, and Carries -/

variable (rg : W → Words GE) (wv : W → Nat → GE) (D : St × F.E.Str → Words GE)
  (DV : St × F.E.Str → Nat → GE)

/-- The functional pin is the fence's file's, at this chain's record. -/
theorem pinF_iff (lo : Nat) (low : OnBytes.Tree → Option Nat) (x : St × F.E.Str) (w : W) :
    PinF rg wv D DV x w ↔
      VerifiableInference.Desc.Sound.PinF (bookK lo low) agK rg wv D DV x w := Iff.rfl

/-- **The promise's letter at the border in front of a piece with the base B**: the fence at B; no
collision at the key's seeds, and the key fits. -/
def PrmAt (lo : Nat) (low : OnBytes.Tree → Option Nat) (P : P14) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (B : Nat) (x : St × F.E.Str) : Prop :=
  FenceAt (bookK lo low) B x ∧ PrmK P err eM rank x

/-- **Carries, from the fence's rules.** -/
theorem carriesAt {C : CK} {ρ' : Type} (lo : Nat) (low : OnBytes.Tree → Option Nat) (P : P14)
    (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (recV : St → ρ') (pc : Piece C F St Unit W) (B B' : Nat) (hB : pc.base = B)
    (hB' : B' = B + pc.trees) (hK : BookKept (bookK lo low) recK pc)
    (hD : ReadsSeat (bookK lo low) recK agK D) (hV : ReadsLow lo recV DV) (hlo : lo ≤ B)
    (hr : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → recV d' = recV d)
    (hk : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → d'.loc.key = d.loc.key)
    (on : St × F.E.Str → Prop) (hon : ∀ a, on a → PrmAt lo low P err eM rank B a) :
    Carries pc (PinF rg wv D DV) on (PrmAt lo low P err eM rank B') := by
  subst hB
  subst hB'
  refine ⟨fun a τ b w ha hout hp => ?_, fun a τ b ha hout => ⟨?_, ?_⟩⟩
  · exact backUnder St Unit W _ _ _ _ C F (bookK lo low) recK agK rg wv D DV lo recV pc
      (fun o m m' m'' h h' => agree_of_two h' h) hK hD hV hlo
      (fun a τ b hb => by
        obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hb
        exact hr _ _ gs _ hd)
      a τ b w (hon a ha).1 hout hp
  · exact fenceStep St Unit W _ C F (bookK lo low) recK pc hK a τ b hout (hon a ha).1
  · exact keepK P err eM rank pc hk a τ b hout (hon a ha).2

/-- One of the six is one of the eight. -/
theorem eight_of_six {b b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}
    (h : b ∈ [b1, b3, b4, b6, b7, b8]) : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h | h | h | h <;> simp [h]

/-- One of the two is one of the eight. -/
theorem eight_of_two {b b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}
    (h : b = b2 ∨ b = b5) : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h <;> simp [h]

/-- **Carries at a piece that holds one of the six blocks that send nothing**: the fence stays at
B. -/
theorem carriesSix {C : CK} {ρ' : Type} (lo : Nat) (low : OnBytes.Tree → Option Nat) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (recV : St → ρ') (hD : ReadsSeat (bookK lo low) recK agK D) (hV : ReadsLow lo recV DV)
    (hrV : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], ∀ d rs gs d', b.decide d rs gs = .ok d' →
      recV d' = recV d)
    (pc : Piece C F St Unit W) (hpc : pc.b ∈ [b1, b3, b4, b6, b7, b8]) (ht : pc.trees = 0)
    (B : Nat) (hB : pc.base = B) (hlo : lo ≤ B)
    (on : St × F.E.Str → Prop) (hon : ∀ a, on a → PrmAt lo low P err eM rank B a) :
    Carries pc (PinF rg wv D DV) on (PrmAt lo low P err eM rank B) :=
  carriesAt rg wv D DV lo low P err eM rank recV pc B B hB (by rw [ht, Nat.add_zero])
    (bookKept_six lo low P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS pc hpc ht) hD hV hlo
    (hrV pc.b (eight_of_six hpc))
    (key_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS pc.b (eight_of_six hpc)) on hon

/-- **Carries at a piece that holds one of the two sendings**: the fence goes on by the stretch's
trees. -/
theorem carriesTwo {C : CK} {ρ' : Type} (lo : Nat) (low : OnBytes.Tree → Option Nat) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (recV : St → ρ') (hD : ReadsSeat (bookK lo low) recK agK D) (hV : ReadsLow lo recV DV)
    (hrV : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], ∀ d rs gs d', b.decide d rs gs = .ok d' →
      recV d' = recV d)
    (pc : Piece C F St Unit W) (hpc : pc.b = b2 ∨ pc.b = b5) (t : Nat) (ht : pc.trees = t)
    (hT : ∀ d d' ft sent lay, Received ft sent lay d.st d.book d.roots d'.st d'.book d'.roots →
      (∃ rs gs, pc.b.decide d rs gs = .ok d') → lay.shapes.size = t)
    (B : Nat) (hB : pc.base = B) (hlo : lo ≤ B)
    (on : St × F.E.Str → Prop) (hon : ∀ a, on a → PrmAt lo low P err eM rank B a) :
    Carries pc (PinF rg wv D DV) on (PrmAt lo low P err eM rank (B + t)) :=
  carriesAt rg wv D DV lo low P err eM rank recV pc B (B + t) hB (by rw [ht])
    (bookKept_two lo low P b1 b2 b3 b4 b5 b6 b7 b8 hbl pc hpc
      (fun d d' ft sent lay h h' => (hT d d' ft sent lay h h').trans ht.symm)) hD hV hlo
    (hrV pc.b (eight_of_two hpc))
    (key_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS pc.b (eight_of_two hpc)) on hon

end Desc.K14.Law
