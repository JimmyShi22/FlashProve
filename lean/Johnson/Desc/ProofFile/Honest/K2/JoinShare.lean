-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/JoinShare.lean: the kind "the code switch" (K2): THE KIND's SHARE
OF THE JOINED LIST, AS A TERM: the record `Others` (Honest/Thread/Join.lean, of other authors)
filled with the lots of a list of places: each place's lots of messages and of pads
(Honest/K2/ScriptLots.lean), its table by the member's number (`switchTableAt`,
Honest/K2/Seated.lean), and the members' numbers. With the laws that say that each place's lots lie
in the record, a form for "one share lies in a larger record" (the real list holds several senders'
shares as one: `Others.add`, Honest/Thread/JoinFit.lean, of other authors), and the kind's ties at a
fit list (`JoinFit`, there) that holds the share. Three definitions with code, one of them a public
test; one form of a premise; statements with their proofs.

  `switchShare`     the record, over letters: for each place its member's number (no), the number of
                    challenges in front of it (fx), its messages' numbers (num), its tree and
                    tenants; the closing, the sender and the data; rest: what is laid at every
                    other member's number
  `switchShareAt`   the record at a plan's own letters
  `switchSeatsB`    A PUBLIC TEST: each message of each place has a seat in a list of seats, and all
                    of one place sit in one tree
  `seats_of_test`   where it passes, `switchShareAt` reads neither of its two defaults: the tree and
                    tenant of each lot of pads are a seat's of the list
  `share_msgs_mem`, `share_pads_mem`   each place's lots lie in the record
  `share_tl_at`     at a place's member's number the record holds that place's table, where no
                    member's number stands twice
  `share_tl_rest`   at every other number: rest
  `ShareIn`         THE FORM OF A PREMISE: a share's lots, numbers and tables stand in a record
  `shareIn_self`, `shareIn_add_left`, `shareIn_add_right`   a share lies in itself; in a sum, on the
                    left; on the right where no number of it stands on the left
  `share_msgs_fit`, `share_off_fit`, `share_pads_fit`, `share_rows_fit`, `share_trees_fit`   THE
                    ENDS: at a fit list that holds the share, at each place of the share

`switchShareAt` is written after the record that the authors of the joined list wrote for their own
trials at a small description (k2Others, Honest/Thread/JoinSmallK2.lean). That file is not imported,
and no equation between the two is stated here.

By: `join_msgs_other`, `join_pads_other`, `join_trees_other` (Honest/Thread/JoinFit.lean, of other
authors) · `join_rows_k2` (Honest/K2/Law/JoinTie.lean) · `msgLot_mem`, `padLot_mem`
(Honest/K2/Law/LotsLaid.lean) · `ownMsgs_off` (Honest/K2/Law/TabRowsOff.lean); the rest by laws on
lists.

Limits. A RECORD IS WRITTEN; NO SCRIPT IS LAID HERE. A kept copy gets a lot of pads and no lot of
messages. Where the plan has no seat for a message, `switchShareAt` lays the pad's lot at tree 0 or
tenant 0: `switchSeatsB` is the test that bars it; that it passes is shown here at no plan. rest
stays a letter in every law. `switchShare` TAKES THE SENDER Sd AS A LETTER, FOR ITS TABLES ALONE:
the texts of its lots have `coreSender freshTable` written into them (`handed`, `switchRowsLaid`).
`switchShareAt` lays that same sender: there tables and texts have one sender. That the list is fit
(`JoinFit`) and holds the share (`ShareIn`), and that no member's number of the share stands twice,
stay premises. AT A KEPT COPY THE ENDS SAY NOTHING ON THE MESSAGE. Nothing is asked of the book. The
texts read a run's coins; no proof here opens a text. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit
import Johnson.Desc.ProofFile.Honest.K2.Law.JoinTie
import Johnson.Desc.ProofFile.Honest.K2.SwitchNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (MsgLot PadLot TreeLot OwnMsgs OwnPads OwnTrees Others joinQ JoinFit
  join_msgs_other join_pads_other join_trees_other)

variable {W₀ Rc Xi Tr : Type}

/-- **THE KIND's SHARE OF THE JOINED LIST**, over a list of places. THE SENDER Sd IS A LETTER HERE,
FOR THE TABLES ALONE: the texts of the lots have `coreSender freshTable` written into them: at
another Sd the share's tables are not the tables of its messages, and nothing ties the two;
`switchShareAt` lays `coreSender freshTable`. Where two places have one member's number, the first
in the list gives the table. -/
def switchShare (Bk : ProverCoinCounts) (ch : Nat) (Sd : Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (no fx : SwitchPlace → Nat)
    (num : SwitchPlace → Nat → Nat) (tree : SwitchPlace → Nat) (tenant : SwitchPlace → Nat → Nat)
    (places : List SwitchPlace) (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    Others Bk (Local W₀ Rc Xi Tr) where
  ml := places.flatMap fun p => switchMsgLots ch D readers closing p (num p) (fx p)
  pl := places.flatMap fun p => switchPadLots ch p (tree p) (tenant p)
  tl := fun b => match places.find? fun p => no p == b with
    | some p => ⟨fun j k w h => (p.place, switchTableAt Bk ch Sd D readers closing p k w h j),
        fun _ => 0⟩
    | none => rest b
  tn := places.map no

/-- **THE SHARE AT A PLAN's OWN LETTERS**: the first chain; the sender `coreSender freshTable`, of
which the lots' texts are made; the lot's own closing; each place's number by its place in the flat
list bs; the numbers and seats that the plan's list of seats gives. TWO DEFAULTS STAND IN IT: where
the plan has no seat for a message, the pad's lot is laid at tree 0 or at tenant 0 (`getD 0`,
twice): `switchSeatsB` is the test that bars both (`seats_of_test`). -/
def switchShareAt (Bk : ProverCoinCounts) (bs : List (Block S ProofFile.Cl)) (front : Nat) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) : Others Bk (Local W₀ Rc Xi Tr) :=
  switchShare Bk 0 (coreSender freshTable) D readers
    (lotClosingAt G.first.layout (segmentsOf Z G))
    (fun p => borderNo bs p.place) (fun p => front + roundsTo bs (borderNo bs p.place))
    (switchNum Z) (fun p => ((switchSeatIn (P5J.At.pseatsAll Z) p.link 0).map (·.j)).getD 0)
    (fun p n => ((switchSeatIn (P5J.At.pseatsAll Z) p.link n).map (·.t)).getD 0)
    (switchPlaces Z G) rest

/-- **A PUBLIC TEST**: each message of each place has a seat in the list ps, and it stands in the
tree of the place's message 0. -/
def switchSeatsB (ps : List P5T.PSeat) (places : List SwitchPlace) : Bool :=
  places.all fun p => (List.range (switchSent p.sizes p.others).size).all fun n =>
    (switchSeatIn ps p.link n).any fun q => q.j == ((switchSeatIn ps p.link 0).map (·.j)).getD 0

namespace Law

/-- **Where the test passes no default is read**: the tree and tenant at which `switchShareAt` lays
message n's lot of pads are those of the seat that `switchSeatIn` finds. -/
theorem seats_of_test {ps : List P5T.PSeat} {places : List SwitchPlace}
    (h : switchSeatsB ps places = true) {p : SwitchPlace} (hp : p ∈ places) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) :
    ∃ q ∈ ps, switchSeatIn ps p.link n = some q ∧
      ((switchSeatIn ps p.link 0).map (·.j)).getD 0 = q.j ∧
      ((switchSeatIn ps p.link n).map (·.t)).getD 0 = q.t := by
  have t := List.all_eq_true.1 (List.all_eq_true.1 h p hp) n (List.mem_range.2 hn)
  cases hs : switchSeatIn ps p.link n with
  | none =>
    rw [hs] at t
    cases t
  | some q =>
    rw [hs, Option.any_some, beq_iff_eq] at t
    exact ⟨q, List.mem_of_find?_eq_some hs, rfl, t.symm, rfl⟩

variable {Bk : ProverCoinCounts} (ch : Nat) (Sd : Sender) (D : RowDataOf Xi)
  (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (no fx : SwitchPlace → Nat)
  (num : SwitchPlace → Nat → Nat) (tree : SwitchPlace → Nat) (tenant : SwitchPlace → Nat → Nat)
  (places : List SwitchPlace) (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr))

/-- Each place's lots of messages lie in the record. -/
theorem share_msgs_mem {p : SwitchPlace} (hp : p ∈ places) :
    ∀ L ∈ switchMsgLots ch D readers closing p (num p) (fx p),
      L ∈ (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest).ml :=
  fun _ hL => List.mem_flatMap.2 ⟨p, hp, hL⟩

/-- Each place's lots of pads lie in the record. -/
theorem share_pads_mem {p : SwitchPlace} (hp : p ∈ places) :
    ∀ L ∈ switchPadLots ch p (tree p) (tenant p),
      L ∈ (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest).pl :=
  fun _ hL => List.mem_flatMap.2 ⟨p, hp, hL⟩

/-- **At a place's member's number: that place's table**, where no number stands twice. -/
theorem share_tl_at (hnd : (places.map no).Nodup) {p : SwitchPlace} (hp : p ∈ places) :
    (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest).tl (no p) =
      ⟨fun j k w h => (p.place, switchTableAt Bk ch Sd D readers closing p k w h j),
        fun _ => 0⟩ := by
  show (match places.find? fun q => no q == no p with
    | some q => (⟨fun j k w h => (q.place, switchTableAt Bk ch Sd D readers closing q k w h j),
        fun _ => 0⟩ : TreeLot Bk (Local W₀ Rc Xi Tr))
    | none => rest (no p)) = _
  cases hf : places.find? fun q => no q == no p with
  | none =>
    have := List.find?_eq_none.1 hf p hp
    simp at this
  | some q =>
    have hq := List.mem_of_find?_eq_some hf
    have t := List.find?_some hf
    have he : no q = no p := beq_iff_eq.1 t
    obtain rfl : q = p := List.inj_on_of_nodup_map hnd hq hp he
    rfl

/-- At a number that is no place's: rest. -/
theorem share_tl_rest {b : Nat} (hb : b ∉ places.map no) :
    (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest).tl b = rest b := by
  show (match places.find? fun q => no q == b with
    | some q => (⟨fun j k w h => (q.place, switchTableAt Bk ch Sd D readers closing q k w h j),
        fun _ => 0⟩ : TreeLot Bk (Local W₀ Rc Xi Tr))
    | none => rest b) = _
  cases hf : places.find? fun q => no q == b with
  | none => rfl
  | some q =>
    have t := List.find?_some hf
    exact absurd (List.mem_map.2 ⟨q, List.mem_of_find?_eq_some hf, beq_iff_eq.1 t⟩) hb

/-- **THE FORM OF A PREMISE: a share stands in a record**: its lots, its members' numbers, and at
these numbers its tables. -/
structure ShareIn {Wl : Type} (A O : Others Bk Wl) : Prop where
  ml : ∀ L ∈ A.ml, L ∈ O.ml
  pl : ∀ L ∈ A.pl, L ∈ O.pl
  tn : ∀ b ∈ A.tn, b ∈ O.tn
  tl : ∀ b ∈ A.tn, O.tl b = A.tl b

/-- A share stands in itself. -/
theorem shareIn_self {Wl : Type} (A : Others Bk Wl) : ShareIn A A :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ _ => rfl⟩

/-- A share stands in a sum, on the left. -/
theorem shareIn_add_left {Wl : Type} (A B : Others Bk Wl) : ShareIn A (A.add B) :=
  ⟨fun _ h => List.mem_append.2 (Or.inl h), fun _ h => List.mem_append.2 (Or.inl h),
    fun _ h => List.mem_append.2 (Or.inl h),
    fun _ h => if_pos (List.contains_iff_mem.2 h)⟩

/-- A share stands in a sum, on the right, where no number of it stands on the left. -/
theorem shareIn_add_right {Wl : Type} (A B : Others Bk Wl) (hd : ∀ b ∈ B.tn, b ∉ A.tn) :
    ShareIn B (A.add B) :=
  ⟨fun _ h => List.mem_append.2 (Or.inr h), fun _ h => List.mem_append.2 (Or.inr h),
    fun _ h => List.mem_append.2 (Or.inr h),
    fun b h => if_neg fun hc => hd b h (List.contains_iff_mem.1 hc)⟩

variable {Xj X Cl Cells Tok : Type} {bs : List (Block S Cl)} {front : Nat} {arr : Nat → Nat → Nat}
  {seats : List (Nat × Nat)} {wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj} {own₀ : X}
  {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) X)} {O : Others Bk (Local W₀ Rc Xi Tr)}

/-- **A MESSAGE OF WHICH THE SWITCH IS THE FIRST SENDER, AT A FIT LIST THAT HOLDS THE SHARE.**
closing is a letter: whether `switchMsgTxt` answers is a theorem on public data at the lot's own
closing `lotClosingAt` under `closingOk` alone (`msgTxt_isSome`, `msgTxt_public`,
Honest/K2/Law/LotsAnswer.lean). At a book whose count at the part's address does not cover the
part's due, or that does not lend it a stretch that it carries, this law holds for nothing, and it
is never quoted as if it spoke there: that the frame hands the part its coins (`handed`) is neither
asked nor paid here: whoever quotes this law at a book names that at that book beside it. It says
nothing at an empty list of places. -/
theorem share_msgs_fit (F : JoinFit bs front arr seats wit own₀ jobs O)
    (hin : ShareIn (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest) O)
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat) {p : SwitchPlace} (hp : p ∈ places) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) (h1 : firstSender p n = true) :
    OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs O) Vd N (num p n) (fx p)
      (switchMsgTxt ch D readers closing p n) :=
  join_msgs_other F
    (hin.ml _ (share_msgs_mem ch Sd D readers closing no fx num tree tenant places rest hp _
      (msgLot_mem ch D readers closing p (num p) (fx p) hn h1))) cells tok Vd N

/-- The same at the text off the pad; what is said there of the closing and of the book holds here
too. It says nothing at an empty list of places. -/
theorem share_off_fit (F : JoinFit bs front arr seats wit own₀ jobs O)
    (hin : ShareIn (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest) O)
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat) {p : SwitchPlace} (hp : p ∈ places) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) (h1 : firstSender p n = true) :
    OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs O) Vd N (num p n) (fx p)
      (switchMsgOff ch D readers closing p n) :=
  ownMsgs_off _ Vd N ch D readers closing p (fx p) n (num p n)
    (share_msgs_fit ch Sd D readers closing no fx num tree tenant places rest F hin cells tok Vd N
      hp hn h1)

/-- **EVERY MESSAGE's PAD, AT A FIT LIST THAT HOLDS THE SHARE.** At a book whose count at the part's
address does not cover the part's due this law holds for nothing, and it is never quoted as if it
spoke there: that the book covers it is neither asked nor paid here: whoever quotes this law at a
book names that at that book beside it. It says nothing at an empty list of places. -/
theorem share_pads_fit (F : JoinFit bs front arr seats wit own₀ jobs O)
    (hin : ShareIn (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest) O)
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (Vd : Local W₀ Rc Xi Tr → Prop) {p : SwitchPlace} (hp : p ∈ places) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) :
    OwnPads (joinQ bs front cells tok arr wit own₀ jobs O) Vd (tree p) (tenant p n)
      (fun k _ => switchPadTxt ch p n k) :=
  join_pads_other F
    (hin.pl _ (share_pads_mem ch Sd D readers closing no fx num tree tenant places rest hp _
      (padLot_mem ch p (tree p) (tenant p) hn))) cells tok Vd

/-- **THE JOINED SCRIPT's WITNESS HOLDS THE ROWS THAT THE SWITCH LAYS**, at a message of which the
switch is the first sender, where no message of the sending is a word (hw), the part is handed its
coins (hH) and its rows are laid (hV). closing is a letter: whether the rows are laid is a theorem
on public data at `lotClosingAt` under `closingOk` alone (`rows_isSome`,
Honest/K2/Law/LotsAnswer.lean). At a book that does not hand the part its coins, or where the rows
are not laid, this law holds for nothing, and it is never quoted as if it spoke there. It says
nothing at an empty list of places. -/
theorem share_rows_fit (F : JoinFit bs front arr seats wit own₀ jobs O)
    (hin : ShareIn (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest) O)
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok) {p : SwitchPlace}
    (hp : p ∈ places) (hw : NoWord (switchSent p.sizes p.others)) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) (h1 : firstSender p n = true) (k : Coins Bk)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hH : handed ch p k = some c)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w (hd.take (fx p)) = .ok V) :
    ((joinQ bs front cells tok arr wit own₀ jobs O).wit k w hd).tab p.sizes.codes
        ((switchSent p.sizes p.others).getD n default).shape (num p n) (tree p) (tenant p n) =
      K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) :=
  join_rows_k2 F.msgs F.pads cells tok ch D readers closing p (num p) (fx p) (tree p) (tenant p)
    (fun L hL => hin.ml L
      (share_msgs_mem ch Sd D readers closing no fx num tree tenant places rest hp L hL))
    (fun L hL => hin.pl L
      (share_pads_mem ch Sd D readers closing no fx num tree tenant places rest hp L hL))
    hw hn h1 k hH w hd hV

/-- **THE TREES, AT A FIT LIST THAT HOLDS THE SHARE**, at a thread whose four fields are the joined
Script's, where no member's number of the share stands twice. closing is a letter here too; what is
shown on public data stands at `lotClosingAt` under `closingOk` alone
(Honest/K2/Law/LotsAnswer.lean). THREE ROADS LEAD TO THE TABLE WITHOUT A WORD (`noTable`): the frame
hands the part nothing; the first move refuses, so no rows are laid; the sending has no table number
j. Nothing is asked of the book here, and on each of the three the end is not empty: it speaks of
that table. It says nothing at an empty list of places. -/
theorem share_trees_fit {V X' Pb : Type} (F : JoinFit bs front arr seats wit own₀ jobs O)
    (hin : ShareIn (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest) O)
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (T : Thread Bk S Cl V (Local W₀ Rc Xi Tr) X' Pb) (hbs : T.bs = bs) (hfr : T.front = front)
    (htab : T.table = (joinQ bs front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ bs front cells tok arr wit own₀ jobs O).fixed)
    (hnd : (places.map no).Nodup) {p : SwitchPlace} (hp : p ∈ places) {blk : Block S Cl}
    (hblk : bs[no p]? = some blk) :
    OwnTrees T (no p) (blk.oracles.flatMap id).length
      (fun j k w h => (p.place, switchTableAt Bk ch Sd D readers closing p k w h j))
      (fun _ => 0) := by
  have hm : no p ∈
      (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest).tn :=
    List.mem_map.2 ⟨p, hp, rfl⟩
  have e := join_trees_other F cells tok T hbs hfr htab hfix (hin.tn _ hm) hblk
  rw [hin.tl _ hm,
    share_tl_at ch Sd D readers closing no fx num tree tenant places rest hnd hp] at e
  exact e

end Law

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.switchShare
#print axioms ProofFile.Honest.K2.switchShareAt
#print axioms ProofFile.Honest.K2.switchSeatsB
#print axioms ProofFile.Honest.K2.Law.seats_of_test
#print axioms ProofFile.Honest.K2.Law.share_msgs_mem
#print axioms ProofFile.Honest.K2.Law.share_pads_mem
#print axioms ProofFile.Honest.K2.Law.share_tl_at
#print axioms ProofFile.Honest.K2.Law.share_tl_rest
#print axioms ProofFile.Honest.K2.Law.ShareIn
#print axioms ProofFile.Honest.K2.Law.shareIn_self
#print axioms ProofFile.Honest.K2.Law.shareIn_add_left
#print axioms ProofFile.Honest.K2.Law.shareIn_add_right
#print axioms ProofFile.Honest.K2.Law.share_msgs_fit
#print axioms ProofFile.Honest.K2.Law.share_off_fit
#print axioms ProofFile.Honest.K2.Law.share_pads_fit
#print axioms ProofFile.Honest.K2.Law.share_rows_fit
#print axioms ProofFile.Honest.K2.Law.share_trees_fit
