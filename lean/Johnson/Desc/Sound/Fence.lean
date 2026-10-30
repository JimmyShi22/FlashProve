-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/Fence.lean: The fence: what ties a chain's record to the trees that its pieces have sent, so
that "a decoder that reads the trees reads behind a block, of every message sent in front of it, what it
read in front" can be said of every statement in front, also of one that no run reaches. Definitions,
statements written as `def … : Prop`, and their proofs. General in the record and in the decoder. The
term takes a reader for trees that are taken over from an earlier chain;
`pinF_of_under`'s condition is
named as what it must be: the border's; what `oneFence_idle` is worth is said; what rec must
carry is said.

Why. A piece's reduction leaves the stored table and every column of a tree below its base; it lays its
stretch's own trees from its base on and clears every later tree (Johnson/Desc/Sound/StringsStay.lean: colStays;
SharedJointCountLedger.lean: out_clears_unsent). So a premise "∀ a τ b, out a τ = some b → the decoder reads of
message o at b what it read at a" is false at a statement whose record seats a message that it counts as
sent in a tree at or above the piece's base. No run reaches such a statement; a bare "for all" does.
That is cured of K14's law's rule, in form, by a pin under a fence Fn (a file
MemberKey.lean, not in this library: StaysG, PinG, back_guard), with Fn a letter: "Fn as a term: owed by nobody". This file is
that debt.
The fence is said by the border. StaysG has one Fn in front of and behind a piece, and its row one
pin at all pieces. A fence that gives "old" at a piece which says yes at such statements (FenceTeeth.lean [not in this library]:
bareOld_false; a piece that refuses them has "old" there for nothing) must put every sent message's tree
below that piece's base, and the pieces' bases differ: one Fn that does so at all of them puts them below
the least base (`oneFence_idle`): where the chain's own messages sit from that base on, it holds only of
records without a message. `oneFence_idle` is a gloss: it presupposes that Fn bounds the seats. The stronger
argument (on paper, on a sending's text): for every Fn
that holds at one front record of a sending which a run reaches: the fence is kept, so it holds behind; fed
to the same piece a second time, the piece says yes and writes the message's tree over. Both end at:
"the guard belongs to the border". So:

  `Booked S`: what the fence reads of a record: cnt (how many messages it counts as sent), seat (the number
    of the tree in which it seats message o, if it seats it), sent (the number of the first tree that it
    does not count as sent).
  `FenceAt K B x`: the record counts the trees below B as sent, no more and no fewer; and every message that
    it counts as sent is seated in a tree below B. B: the base of the piece behind the border.
  `BookKept K rec p`: what a block owes the book at a yes of its piece, all four of the record alone (facts on the
    kind's text and on how many trees its stretch lists), and all four asked under the fence in front alone (bare,
    "the seat stays" would be false of a receiving at a record that places a counted message at a tree
    which its book does not hold yet: the receiving appends trees: the seat turns from none to some: the
    same disease once more): no message is lost · of a message sent in front
    the record says behind what it said in front (rec: what a decoder reads of the record on message o;
    and its seat) · it counts as many more trees as the piece's stretch sends · a new message is seated
    below the new count.
  `ReadsSeat K rec Ag D`: the condition on the decoder: it reads message o through what rec reads of the record
    on o, and the columns of o's tree: nothing else. Ag o m m': "m and m' agree on message o". At the term below the
    seat is the tree alone: so rec s o must carry the statement's entry for o and the book's whole place of o (its
    part within the tree too): else a decoder that reads o's rows at its part of a column does not meet it.
  `FenceStep`: at a yes the fence at the piece's base gives the fence at its base + its trees: by `Tiled` the
    next piece's base.
  `FenceOld`: under the fence at the piece's base: of every message sent in front the decoder reads behind
    what it read in front. By colStays, out_behind: called.
  `ReadsLow`, `FenceOwn`: the like for a decoder of something that was sent on an earlier chain (trees below lo).
  `PinF`, `BackUnder`: the functional pin ("of every message sent so far the witness has the decoder's word; and
    the other vector"): one letter at all borders: it goes back at a yes under the fence in front: for a kind
    whose law asks "the pin goes back" under the promise in front, with the fence a clause of that promise.
  `PinUnder`, `BackAt`: for a kind whose law asks it bare: the pin under the fence at B: at every statement in front
    the pin at base + trees behind gives the pin at base in front: one letter a border. `pinF_of_under`: beside a border's
    condition that gives the fence at that border's B it is the functional pin. (One promise for all borders
    that gave the fence at two bases would hold of nothing: said here without a theorem.) `fence_start`: a record without a message that counts the trees below B has the fence.
  `bookedOf`, `fenceB`, `fenceB_iff`: the term, at a record with a statement, a book of trees and a count of roots
    (readers stOf, bookOf, rootsOf): cnt := the statement's number of messages · seat o := lo + n where the
    book places o in a tree whose source is "own n"; low t where that tree t is taken over from an earlier chain
    (source "given") · sent := lo + the roots received. lo: the number, in the frame's list of all trees, of
    the chain's first own tree. low: a letter: the number in that list of a tree that was taken over: on a chain
    that takes none over (by reading: the shared chain) fun _ => none will do; on a chain that goes on from another
    it must be filled, or the fence fails at every record that counts such a message. (Not the tree's own
    `number` as it stands: by the library's note on that field a chain that continues no other counts from
    0, so two trees that one chain reads can have one number.) As a test with code. Proposed by reading
    OnBytes/Iop/Ground.lean (TreeBook, Tree, receiveOracles) and Johnson/Desc/K1/Law/Writes3.lean (recvD): that it is
    the seat which the meant decoder reads is left to the decoder's files to confirm.

The silly members (Johnson/Desc/Sound/FenceTeeth.lean [not in this library]). A block that refuses all meets every statement here for
nothing, as it meets every law of a yes. A fence that never holds makes PinUnder hold of everything: so
whoever uses PinUnder owes "the promise gives the fence" at every border: fence_start and FenceStep are its
two halves. That the fence cannot be dropped, that it can fail, and that BookKept can fail: there.
Nearest kin: MemberKey.lean's StaysG | PinG | back_guard (one Fn; the fence a letter) ·
PinF | Stays | back_fun (no fence; these PinF and back_fun are not in this library: the PinF above is this file's own) · the table of joints' way to the same end: a pin is an item
that opens behind its sending, read through the acting part, in which a tree from the border's top on is
not seen (Johnson/Desc/Sound/BordersSharedQ.lean: muQ, actQ): there the tenants are the plan's numbers, not the
record's. By name ("fence", "seat"), the files then at hand hold no fence as a term. (The
`PinAt` (MsgSig.lean) and `seatOf` (World.lean) of Johnson/Desc/Sound are other things: a tenant's pin; a member's seat by the plan.)
Every "there is", walked: in FenceAt: the tree's number: the book's own.
Limits. Frames: no chance, no game. BookKept at a real kind, ReadsSeat at a real decoder: premises.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SendLaw
import Johnson.Desc.Sound.StringsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker
open _root_.Run.PQ (CK SgX)

/-- What a fence reads of a record. -/
structure Booked (S : Type) where
  /-- how many messages the record counts as sent -/
  cnt : S → ℕ
  /-- the number of the tree in which it seats message o -/
  seat : S → ℕ → Option ℕ
  /-- the number of the first tree that it does not count as sent -/
  sent : S → ℕ

section
variable {S Cl W ρ M V : Type} {C : CK} {F : Frame}

/-- **THE FENCE AT THE BORDER IN FRONT OF A PIECE WITH THE BASE B.** -/
def FenceAt (K : Booked S) (B : ℕ) (x : S × F.E.Str) : Prop :=
  K.sent x.1 = B ∧ ∀ o, o < K.cnt x.1 → ∃ j, K.seat x.1 o = some j ∧ j < B

/-- **What a block owes the book at a yes of its piece**: of the record alone; EACH CLAUSE UNDER THE FENCE IN
FRONT. -/
structure BookKept (K : Booked S) (rec : S → ℕ → ρ) (p : Piece C F S Cl W) : Prop where
  size : ∀ a τ b, FenceAt K p.base a → p.ior.red.out a τ = some b → K.cnt a.1 ≤ K.cnt b.1
  old : ∀ a τ b, FenceAt K p.base a → p.ior.red.out a τ = some b → ∀ o, o < K.cnt a.1 →
    rec b.1 o = rec a.1 o ∧ K.seat b.1 o = K.seat a.1 o
  more : ∀ a τ b, FenceAt K p.base a → p.ior.red.out a τ = some b →
    K.sent b.1 = K.sent a.1 + p.trees
  new : ∀ a τ b, FenceAt K p.base a → p.ior.red.out a τ = some b → ∀ o, K.cnt a.1 ≤ o →
    o < K.cnt b.1 → ∃ j, K.seat b.1 o = some j ∧ j < K.sent b.1

/-- **The condition on the decoder**: it reads message o through what rec reads of the record on o and
the columns of o's tree. -/
def ReadsSeat (K : Booked S) (rec : S → ℕ → ρ) (Ag : ℕ → M → M → Prop) (D : S × F.E.Str → M) : Prop :=
  ∀ (x x' : S × F.E.Str) (o j : ℕ), K.seat x.1 o = some j → K.seat x'.1 o = some j →
    rec x'.1 o = rec x.1 o → (∀ z, (strsOf F x'.2).col j z = (strsOf F x.2).col j z) →
    Ag o (D x') (D x)

/-- A decoder of something that was sent on an earlier chain: it reads what recV reads of the record, the
stored table, and the trees below lo. -/
def ReadsLow {ρ' : Type} (lo : ℕ) (recV : S → ρ') (DV : S × F.E.Str → V) : Prop :=
  ∀ x x' : S × F.E.Str, recV x'.1 = recV x.1 → (∀ z, (strsOf F x'.2).cell z = (strsOf F x.2).cell z) →
    (∀ j z, j < lo → (strsOf F x'.2).col j z = (strsOf F x.2).col j z) → DV x' = DV x

/-- The functional pin: of every message sent so far the witness has the decoder's word; and the other
vector is the decoder's. -/
def PinF (K : Booked S) (Ag : ℕ → M → M → Prop) (rg : W → M) (wv : W → V) (D : S × F.E.Str → M)
    (DV : S × F.E.Str → V) (x : S × F.E.Str) (w : W) : Prop :=
  (∀ o, o < K.cnt x.1 → Ag o (D x) (rg w)) ∧ wv w = DV x

/-- **The functional pin under the fence at B.** -/
def PinUnder (K : Booked S) (Ag : ℕ → M → M → Prop) (rg : W → M) (wv : W → V) (D : S × F.E.Str → M)
    (DV : S × F.E.Str → V) (B : ℕ) (x : S × F.E.Str) (w : W) : Prop :=
  FenceAt K B x → PinF K Ag rg wv D DV x w

end

/-- **At a yes the fence goes on to the next border.** -/
def FenceStep : Prop :=
  ∀ (S Cl W ρ : Type) (C : CK) (F : Frame) (K : Booked S) (rec : S → ℕ → ρ) (p : Piece C F S Cl W),
    BookKept K rec p →
    ∀ a τ b, p.ior.red.out a τ = some b → FenceAt K p.base a → FenceAt K (p.base + p.trees) b

/-- **Under the fence the decoder reads behind, of the messages sent in front, what it read in front.** -/
def FenceOld : Prop :=
  ∀ (S Cl W ρ M : Type) (C : CK) (F : Frame) (K : Booked S) (rec : S → ℕ → ρ)
    (Ag : ℕ → M → M → Prop) (D : S × F.E.Str → M) (p : Piece C F S Cl W),
    BookKept K rec p → ReadsSeat K rec Ag D →
    ∀ a τ b, p.ior.red.out a τ = some b → FenceAt K p.base a →
      ∀ o, o < K.cnt a.1 → Ag o (D b) (D a)

/-- The like for what was sent on an earlier chain: no fence is spent: the piece's base is from lo on. -/
def FenceOwn : Prop :=
  ∀ (S Cl W ρ' V : Type) (C : CK) (F : Frame) (lo : ℕ) (recV : S → ρ') (DV : S × F.E.Str → V)
    (p : Piece C F S Cl W),
    ReadsLow lo recV DV → lo ≤ p.base →
    (∀ a τ b, p.ior.red.out a τ = some b → recV b.1 = recV a.1) →
    ∀ a τ b, p.ior.red.out a τ = some b → DV b = DV a

/-- **The functional pin goes back at a yes, under the fence in front.** hAg: two that agree with a third
on o agree on o. -/
def BackUnder : Prop :=
  ∀ (S Cl W ρ ρ' M V : Type) (C : CK) (F : Frame) (K : Booked S) (rec : S → ℕ → ρ)
    (Ag : ℕ → M → M → Prop) (rg : W → M) (wv : W → V) (D : S × F.E.Str → M) (DV : S × F.E.Str → V)
    (lo : ℕ) (recV : S → ρ') (p : Piece C F S Cl W),
    (∀ o m m' m'', Ag o m m'' → Ag o m m' → Ag o m' m'') →
    BookKept K rec p → ReadsSeat K rec Ag D → ReadsLow lo recV DV → lo ≤ p.base →
    (∀ a τ b, p.ior.red.out a τ = some b → recV b.1 = recV a.1) →
    ∀ a τ b w, FenceAt K p.base a → p.ior.red.out a τ = some b →
      PinF K Ag rg wv D DV b w → PinF K Ag rg wv D DV a w

/-- **The pin under the fence goes back at a yes, AT EVERY STATEMENT IN FRONT**: from the border behind the
piece to the border in front of it. hAg: two that agree with a third on o agree on o. -/
def BackAt : Prop :=
  ∀ (S Cl W ρ ρ' M V : Type) (C : CK) (F : Frame) (K : Booked S) (rec : S → ℕ → ρ)
    (Ag : ℕ → M → M → Prop) (rg : W → M) (wv : W → V) (D : S × F.E.Str → M) (DV : S × F.E.Str → V)
    (lo : ℕ) (recV : S → ρ') (p : Piece C F S Cl W),
    (∀ o m m' m'', Ag o m m'' → Ag o m m' → Ag o m' m'') →
    BookKept K rec p → ReadsSeat K rec Ag D → ReadsLow lo recV DV → lo ≤ p.base →
    (∀ a τ b, p.ior.red.out a τ = some b → recV b.1 = recV a.1) →
    ∀ a τ b w, p.ior.red.out a τ = some b →
      PinUnder K Ag rg wv D DV (p.base + p.trees) b w → PinUnder K Ag rg wv D DV p.base a w

theorem fenceStep : FenceStep := by
  intro S Cl W ρ C F K rec p h a τ b hb hf
  refine ⟨by rw [h.more a τ b hf hb, hf.1], fun o ho => ?_⟩
  by_cases hlt : o < K.cnt a.1
  · obtain ⟨j, hj, hjB⟩ := hf.2 o hlt
    exact ⟨j, ((h.old a τ b hf hb o hlt).2).trans hj, Nat.lt_of_lt_of_le hjB (Nat.le_add_right _ _)⟩
  · obtain ⟨j, hj, hjB⟩ := h.new a τ b hf hb o (Nat.le_of_not_lt hlt) ho
    refine ⟨j, hj, ?_⟩
    rw [h.more a τ b hf hb, hf.1] at hjB
    exact hjB

theorem fenceOld : FenceOld := by
  intro S Cl W ρ M C F K rec Ag D p h hD a τ b hb hf o ho
  obtain ⟨j, hj, hjB⟩ := hf.2 o ho
  obtain ⟨hr, hs⟩ := h.old a τ b hf hb o ho
  refine hD a b o j hj (hs.trans hj) hr fun z => ?_
  rw [out_behind p a b τ hb]
  exact colStays C F p.base p.ds a.2 τ j z hjB

theorem fenceOwn : FenceOwn := by
  intro S Cl W ρ' V C F lo recV DV p hD hlo hr a τ b hb
  refine hD a b (hr a τ b hb) (fun z => ?_) fun j z hj => ?_
  · rw [out_behind p a b τ hb]
    exact cellStays C F p.base p.ds a.2 τ z
  · rw [out_behind p a b τ hb]
    exact colStays C F p.base p.ds a.2 τ j z (Nat.lt_of_lt_of_le hj hlo)

theorem backUnder : BackUnder := by
  intro S Cl W ρ ρ' M V C F K rec Ag rg wv D DV lo recV p hAg h hD hV hlo hr a τ b w hf hb hp
  obtain ⟨h1, h2⟩ := hp
  refine ⟨fun o ho => ?_, h2.trans (fenceOwn S Cl W ρ' V C F lo recV DV p hV hlo hr a τ b hb)⟩
  exact hAg o (D b) (D a) (rg w) (h1 o (Nat.lt_of_lt_of_le ho (h.size a τ b hf hb)))
    (fenceOld S Cl W ρ M C F K rec Ag D p h hD a τ b hb hf o ho)

theorem backAt : BackAt := by
  intro S Cl W ρ ρ' M V C F K rec Ag rg wv D DV lo recV p hAg h hD hV hlo hr a τ b w hb hp hf
  exact backUnder S Cl W ρ ρ' M V C F K rec Ag rg wv D DV lo recV p hAg h hD hV hlo hr a τ b w hf hb
    (hp (fenceStep S Cl W ρ C F K rec p h a τ b hb hf))

section
variable {S W M V : Type} {F : Frame}

/-- Beside THE BORDER's condition `on`, which gives the fence at that border's B, the pin under the fence is
the functional pin. -/
theorem pinF_of_under (K : Booked S) (Ag : ℕ → M → M → Prop) (rg : W → M) (wv : W → V)
    (D : S × F.E.Str → M) (DV : S × F.E.Str → V) (B : ℕ) (on : S × F.E.Str → Prop)
    (hp : ∀ x, on x → FenceAt K B x) (x : S × F.E.Str) (w : W) (hx : on x)
    (h : PinUnder K Ag rg wv D DV B x w) : PinF K Ag rg wv D DV x w := h (hp x hx)

/-- A record without a message that counts just the trees below B has the fence at B. -/
theorem fence_start (K : Booked S) (B : ℕ) (x : S × F.E.Str) (h0 : K.cnt x.1 = 0)
    (hB : K.sent x.1 = B) : FenceAt K B x :=
  ⟨hB, fun o ho => absurd (h0 ▸ ho) (Nat.not_lt_zero o)⟩

/-- **ONE FENCE FOR ALL PIECES IS IDLE**: if Fn puts every message that the record counts as sent below B, and
the record seats its messages from B on, then Fn holds only of records without a message. -/
theorem oneFence_idle (K : Booked S) (B : ℕ) (Fn : S × F.E.Str → Prop)
    (hFn : ∀ x, Fn x → ∀ o, o < K.cnt x.1 → ∃ j, K.seat x.1 o = some j ∧ j < B)
    (x : S × F.E.Str) (hlo : ∀ o j, K.seat x.1 o = some j → B ≤ j) (hx : Fn x) : K.cnt x.1 = 0 := by
  by_contra hne
  obtain ⟨j, hj, hjB⟩ := hFn x hx 0 (Nat.pos_of_ne_zero hne)
  exact absurd hjB (Nat.not_lt.2 (hlo 0 j hj))

end

/-! ## The term -/

/-- The number, in the frame's list of all trees, of the tree in which the book places message o: lo + n
where that tree's source is "own n"; what low says where it was taken over from an earlier chain. -/
def bookSeat (lo : ℕ) (low : OnBytes.Tree → Option ℕ) (bk : OnBytes.TreeBook) (o : ℕ) : Option ℕ :=
  (bk.place[o]?).bind fun pl => (bk.trees[pl.1]?).bind fun t =>
    match t.src with
    | .own n => some (lo + n)
    | .given _ _ => low t

/-- **What the fence reads, at a record with a statement, a book of trees and a count of roots.** -/
def bookedOf {S : Type} (lo : ℕ) (low : OnBytes.Tree → Option ℕ) (stOf : S → OnBytes.Statement)
    (bookOf : S → OnBytes.TreeBook) (rootsOf : S → ℕ) : Booked S :=
  ⟨fun s => (stOf s).oracles.size, fun s o => bookSeat lo low (bookOf s) o, fun s => lo + rootsOf s⟩

/-- **THE FENCE AS A TEST WITH CODE.** -/
def fenceB (lo : ℕ) (low : OnBytes.Tree → Option ℕ) (B : ℕ) (st : OnBytes.Statement)
    (bk : OnBytes.TreeBook) (roots : ℕ) : Bool :=
  decide (lo + roots = B) && (List.range st.oracles.size).all fun o =>
    match bookSeat lo low bk o with
    | some j => decide (j < B)
    | none => false

theorem fenceB_iff {S : Type} {F : Frame} (lo : ℕ) (low : OnBytes.Tree → Option ℕ) (B : ℕ)
    (stOf : S → OnBytes.Statement) (bookOf : S → OnBytes.TreeBook) (rootsOf : S → ℕ)
    (x : S × F.E.Str) :
    fenceB lo low B (stOf x.1) (bookOf x.1) (rootsOf x.1) = true ↔
      FenceAt (bookedOf lo low stOf bookOf rootsOf) B x := by
  unfold fenceB FenceAt bookedOf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine and_congr_right fun _ => forall_congr' fun o => imp_congr_right fun _ => ?_
  cases bookSeat lo low (bookOf x.1) o with
  | none => simp
  | some j => simp

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.fenceStep
#print axioms VerifiableInference.Desc.Sound.fenceOld
#print axioms VerifiableInference.Desc.Sound.fenceOwn
#print axioms VerifiableInference.Desc.Sound.backUnder
#print axioms VerifiableInference.Desc.Sound.backAt
#print axioms VerifiableInference.Desc.Sound.oneFence_idle
#print axioms VerifiableInference.Desc.Sound.fenceB_iff
