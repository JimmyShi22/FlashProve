-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean: one form for what a kind of sub-protocol asks
of the `Script` (Honest/Thread/First.lean), and a way to build a `Script` from the kinds' own terms.
The `Script` says what the honest prover's messages, pads and commitment trees are meant to be, as
functions of a run's coins, the input and the challenges heard. This file writes none for a
description of the protocol. The rule of this file: a hypothesis on the `Script` is an equation at
the asker's own numbers. For trees these are the numbers of the trees that the asker's sub-protocol
declares. For messages and pads they are single entries (mask row or main rows, row, place) whose
value the asker's own definition fixes, whoever sends the message. Several kinds may own entries of
one message, and two may own the same entry. Then they must agree. The file proves that hypotheses
of this form can be met together: those on trees (`OwnTrees`) outright, those on messages and pads
where the lots agree. It writes no table's, no message's and no pad's content, so by itself it
proves none of the hypotheses of the rule for a whole file.

  1  `OwnTrees`, `OwnMsgs`, `OwnPads`, `OwnTreesAt`   the forms of a hypothesis. `OwnTrees` is an
     equation at every list of challenges. `OwnTreesAt` asks only what the invariant reads: the
     table at `Thread.tableAt`, wherever the invariant holds together with `Said` after the sender.
     `ownTreesAt_of_own`: the first gives the second
  2  `TreeLot`, `MsgLot`, `PadLot`, `senderOf`, `Script.ofLots`   the construction: one lot for each
     sub-protocol, a list of lots of entries of messages, and one of entries of pads
  3  `treesTo_mono`, `roundsTo_succ`, `tree_split`   small lemmas on the two running sums
  4  `senderOf_own`   a tree's number has one sender. A sub-protocol that declares no tree is passed
     over: no number is in its span
  5  `ofLots_ownTrees`   the construction meets `OwnTrees` at every sub-protocol, whatever the lots
     hold, at a `Thread` whose `bs`, `front`, `table` and `fixed` are the construction's
  6  `ofLots_hfix`   the construction meets the hypothesis `hfix` of `fits_head`
     (Honest/Thread/FitsHead.lean), if no table reads more of its sub-protocol's challenges than
     there are
  7  `ofLots_ownMsgs`, `ofLots_ownPads`   the construction meets `OwnMsgs` or `OwnPads` at a lot of
     the list, if the other lots of the same message or pad agree with it wherever both answer. Lots
     that never answer at one entry agree. `LotsAgree`, `PadLotsAgree`: that hypothesis, by name.
     `MsgsAgree`, `PadsAgree`: all lots agree. `ofLots_ownMsgs_all`, `ofLots_ownPads_all`: then the
     construction meets the form at every lot
  8  `ofLots_msgsFit`   the construction passes the test `Script.msgsFit`
     (Honest/Thread/ScriptFit.lean), if each lot's `fx` is at most `front` plus the rounds before
     the border `born` of its message

Why `OwnTreesAt`. Where the table of a tree in the `Script` is `tableBy`
(Honest/Small/PlayedTo.lean, of other authors, not in the sealed library: the table that the
library's own run of the prover's parts sends), it is one default value at every list of challenges
that is too short for that run to reach the tree. A table with a coin in it is not. So `OwnTrees` is
false there (argued), and only `OwnTreesAt` can hold.

Where nobody owns. At an entry at which no lot answers, `Script.ofLots` puts zero. At a source
`taken` it puts the default place with a table of no words, and 0 for `fixed`. At a tree's number
beyond the list's last it puts what the lot after the list says. No lemma here speaks at these. A
zero there does not say that the honest message holds a zero. So at a list that holds, of one
message, only a lot for some of its entries, the construction puts zero at all the others, at a mask
row too: nothing ties these zeros to what an honest prover sends. No later lemma that speaks of
entries as coins may be stated at such a list. A lot's definition can be one that answers only where
the book of coins has enough coins for the prover's part. With such a lot, and a book that is short
there, the pad that is built is 0, and an answer that should be padded is the bare sum. So every
later lemma that speaks of what is built at such entries as coins, or that needs every entry of a
message to be owned, has to take as a named public hypothesis that the book covers the part's coins.

Where two own one entry. Where two lots answer at one entry and do not agree, the first in the list
wins, and nothing marks it. So one kind's coin can be replaced by what another's definition answers.
The
owner's lemma then lacks its hypothesis, and nothing else notices. Every later lemma that speaks of
an entry as a coin has to take `MsgsAgree` or `PadsAgree` as a named hypothesis, beside the one on
the book. At a mask row the sender's lot is meant to be the one in the list, and the lots of the
kinds that spend its coins are meant to be lemmas on it.

What a lot may read. By type every lot is given all the run's coins and the whole input. No
definition here narrows that. That a definition reads only its owner's share of the coins rests on
each author's definition. Before any lemma on coins, each lot has to be proved to satisfy: two runs'
coins that are alike on the owner's share give the same value. Each lot also has to be proved to
satisfy, before it is used: whether its definition answers at an entry depends on public data alone.
Otherwise a zero is put in a coin's place at some inputs or coins and not at others.

The parameters `Vd` and `N`. At a `Vd` that holds of no input, `OwnMsgs` and `OwnPads` ask nothing,
and every `Script` meets them. Whoever states a lemma from them has to say at which `Vd` and `N`.

Limits.
  * No lot is written here, for any kind.
  * That the honest prover sends what a lot's table says is not treated.
  * That every entry of a message is owned by some lot is not treated.
  * `OwnTreesAt` asks nothing where the invariant holds, together with `Said`, at no run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ScriptFit
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Thread.ThrRow
import Johnson.Desc.Sound.MsgSig
import OnBytes.TypedOracleCompiler.Slice.Batch3Wire
import Johnson.Flat.Dec.FitAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Slice (GE)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb Cells Tok : Type}

/-! ## 1 The forms -/

/-- **Own trees.** Sub-protocol number `b` is taken to declare `r` trees (nothing compares `r` with
the description; at 0 nothing is asked). `tbl j`: the sender's place and the table of its tree
number `j`. `off j`: how many of the sub-protocol's own challenges that table reads. Asked, of the
`Thread`'s `table` and `fixed`, at the sub-protocol's first `r` numbers: the table is `tbl j` at all
coins, inputs and lists of challenges; `fixed` is `front` + the rounds before the sub-protocol +
`off j`. It is a definition: the form of a hypothesis. -/
structure OwnTrees (T : Thread Bk S Cl V W X Pb) (b r : Nat)
    (tbl : Nat → Coins Bk → W → List Fmt.Drawn → Place × Table) (off : Nat → Nat) : Prop where
  table : ∀ j, j < r → ∀ k w h, T.table (.own (treesTo T.bs b + j)) k w h = tbl j k w h
  fixed : ∀ j, j < r → T.fixed (.own (treesTo T.bs b + j)) = T.front + roundsTo T.bs b + off j

/-- **Own entries of a message.** `n`: the message's number in the witness. `fx`: after how many
challenges the value changes no more. `txt`: the entries that the asker owns, and `none` everywhere
else. `Vd` and `N` restrict the inputs and the challenges that are spoken of, which makes the
hypothesis weaker. It is a definition: the form of a hypothesis. -/
def OwnMsgs (Q : Script Bk W Cells Tok MsgT) (Vd : W → Prop) (N n fx : Nat)
    (txt : Coins Bk → W → List Fmt.Drawn → Bool → Nat → Nat → Option GE) : Prop :=
  ∀ k w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place y,
    txt k w (hd.take fx) mask row place = some y →
    Q.msg n k w (hd.take (Q.fixedMsg n)) mask row place = y

/-- **Own entries of a pad.** `j`, `t`: the tree and the tenant. `txt`: the entries that the asker
owns, and `none` everywhere else. It is a definition: the form of a hypothesis. -/
def OwnPads (Q : Script Bk W Cells Tok MsgT) (Vd : W → Prop) (j t : Nat)
    (txt : Coins Bk → W → Bool → Nat → Nat → Option GE) : Prop :=
  ∀ k w, Vd w → ∀ mask row place y, txt k w mask row place = some y →
    Q.pad j t k w mask row place = y

/-- **Own trees, at a state of the run.** After sub-protocol number `b`, wherever the invariant
holds together with `Said`: the invariant's table of the sub-protocol's tree number `j`, as the
invariant reads it (`Thread.tableAt`), comes from the place and shows the columns of the asker's own
table at the same challenges. It is a definition: the form of a hypothesis or of a lemma. -/
def OwnTreesAt (T : Thread Bk S Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop) (b r : Nat)
    (tbl : Nat → Coins Bk → W → List Fmt.Drawn → Place × Table) : Prop :=
  ∀ j, j < r → ∀ b' k s m E, b < b' → ThrS T Said b' k s m E →
    (T.tableAt (.own (treesTo T.bs b + j)) k m).1 =
        (tbl j k m.st.input (m.st.heard.take (T.fixed (.own (treesTo T.bs b + j))))).1 ∧
      (T.tableAt (.own (treesTo T.bs b + j)) k m).2.same
        (tbl j k m.st.input (m.st.heard.take (T.fixed (.own (treesTo T.bs b + j))))).2 = true

/-- `OwnTrees` gives `OwnTreesAt`. -/
theorem ownTreesAt_of_own {T : Thread Bk S Cl V W X Pb} {b r : Nat}
    {tbl : Nat → Coins Bk → W → List Fmt.Drawn → Place × Table} {off : Nat → Nat}
    (h : OwnTrees T b r tbl off) (Said : Nat → Coins Bk → Mid W X → Prop) :
    OwnTreesAt T Said b r tbl := by
  intro j hj b' k s m E _ _
  unfold Thread.tableAt
  rw [h.table j hj]
  exact ⟨rfl, Table.same_refl _⟩

/-! ## 2 The construction -/

/-- What one sub-protocol's authors supply for its trees. -/
structure TreeLot (Bk : ProverCoinCounts) (W : Type) where
  tbl : Nat → Coins Bk → W → List Fmt.Drawn → Place × Table
  off : Nat → Nat

/-- What authors supply for entries of one message that they own. -/
structure MsgLot (Bk : ProverCoinCounts) (W : Type) where
  n : Nat
  fx : Nat
  txt : Coins Bk → W → List Fmt.Drawn → Bool → Nat → Nat → Option GE

/-- What authors supply for entries of one pad that they own. -/
structure PadLot (Bk : ProverCoinCounts) (W : Type) where
  j : Nat
  t : Nat
  txt : Coins Bk → W → Bool → Nat → Nat → Option GE

/-- The sub-protocol that declares tree number `t`: the first one after which more than `t` trees
are declared; the list's length if there is none. -/
def senderOf (bs : List (Block S Cl)) (t : Nat) : Nat :=
  ((List.range bs.length).find? fun b => decide (t < treesTo bs (b + 1))).getD bs.length

/-- **A `Script` from lots.** `cells`, `tok`: as given. A tree: its sender's lot (`senderOf`), at
the tree's number within the sender. `fixedMsg n`: the greatest `fx` of the lots of message n, 0 if
there is none. The catch-all arms: see the head, "Where nobody owns". Where no lot answers it puts
zero. With a lot that answers only where the book of coins covers the prover's part, and a book that
is short there, the pad that is built is 0, and an answer that should be padded is the bare sum.
Where two lots answer at one entry and do not agree, the first in the list wins, and nothing marks
it. -/
def Script.ofLots (bs : List (Block S Cl)) (front : Nat) (cells : W → Cells) (tok : W → Tok)
    (pl : List (PadLot Bk W)) (tl : Nat → TreeLot Bk W) (ml : List (MsgLot Bk W)) :
    Script Bk W Cells Tok MsgT where
  cells := cells
  tok := tok
  pad := fun j t k w mask row place =>
    ((pl.filter fun L => L.j == j && L.t == t).findSome? fun L => L.txt k w mask row place).getD 0
  msg := fun n k w h mask row place =>
    ((ml.filter (·.n == n)).findSome? fun L => L.txt k w (h.take L.fx) mask row place).getD 0
  fixedMsg := fun n => ((ml.filter (·.n == n)).map (·.fx)).foldl max 0
  table := fun σ k w h => match σ with
    | .own t => (tl (senderOf bs t)).tbl (t - treesTo bs (senderOf bs t)) k w h
    | .taken _ _ => (default, ⟨0, 0, fun _ i => i.elim0⟩)
  fixed := fun σ => match σ with
    | .own t =>
      front + roundsTo bs (senderOf bs t) +
        (tl (senderOf bs t)).off (t - treesTo bs (senderOf bs t))
    | .taken _ _ => 0

/-! ## 3 Small lemmas -/

/-- More sub-protocols declare no fewer trees. -/
theorem treesTo_mono (bs : List (Block S Cl)) {a b : Nat} (h : a ≤ b) :
    treesTo bs a ≤ treesTo bs b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold treesTo
  rw [List.take_add, List.flatMap_append, List.length_append]
  exact Nat.le_add_right _ _

/-- The rounds before the next border. -/
theorem roundsTo_succ {bs : List (Block S Cl)} {b : Nat} {blk : Block S Cl}
    (h : bs[b]? = some blk) : roundsTo bs (b + 1) = roundsTo bs b + blk.rounds.length := by
  unfold roundsTo
  rw [declsTo_succ h, List.length_append]

/-- A tree's number below a border is in the span of one sub-protocol before that border. -/
theorem tree_split (bs : List (Block S Cl)) {t : Nat} : ∀ n, n ≤ bs.length → t < treesTo bs n →
    ∃ b j blk, b < n ∧ bs[b]? = some blk ∧ j < (blk.oracles.flatMap id).length ∧
      t = treesTo bs b + j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, hn, h => by
    by_cases h' : t < treesTo bs n
    · obtain ⟨b, j, blk, hb, r⟩ := tree_split bs n (by omega) h'
      exact ⟨b, j, blk, by omega, r⟩
    · have hblk : bs[n]? = some bs[n] := List.getElem?_eq_getElem (by omega)
      rw [treesTo_succ hblk] at h
      exact ⟨n, t - treesTo bs n, bs[n], by omega, hblk, by omega, by omega⟩

/-! ## 4 The trees -/

/-- **A tree's number has one sender.** -/
theorem senderOf_own {bs : List (Block S Cl)} {b j : Nat} {blk : Block S Cl}
    (hblk : bs[b]? = some blk) (hj : j < (blk.oracles.flatMap id).length) :
    senderOf bs (treesTo bs b + j) = b := by
  have hb : b < bs.length := (List.getElem?_eq_some_iff.1 hblk).1
  unfold senderOf
  rw [List.find?_range_eq_some.2
    ⟨decide_eq_true (by rw [treesTo_succ hblk]; omega), List.mem_range.2 hb, fun i hi => by
      rw [decide_eq_false (by
        have := treesTo_mono bs (show i + 1 ≤ b by omega)
        omega)]
      rfl⟩]
  rfl

variable (bs : List (Block S Cl)) (front : Nat) (cells : W → Cells) (tok : W → Tok)
  (pl : List (PadLot Bk W)) (tl : Nat → TreeLot Bk W) (ml : List (MsgLot Bk W))

/-- **The construction meets `OwnTrees` at every sub-protocol**, whatever the lots hold: at a
`Thread` whose `bs`, `front`, `table` and `fixed` are the construction's. -/
theorem ofLots_ownTrees (T : Thread Bk S Cl V W X Pb) (hbs : T.bs = bs) (hfr : T.front = front)
    (htab : T.table = (Script.ofLots bs front cells tok pl tl ml).table)
    (hfix : T.fixed = (Script.ofLots bs front cells tok pl tl ml).fixed) {b : Nat}
    {blk : Block S Cl} (hblk : bs[b]? = some blk) :
    OwnTrees T b (blk.oracles.flatMap id).length (tl b).tbl (tl b).off where
  table := fun j hj k w h => by
    rw [htab, hbs]
    show (tl (senderOf bs (treesTo bs b + j))).tbl
      (treesTo bs b + j - treesTo bs (senderOf bs (treesTo bs b + j))) k w h = _
    rw [senderOf_own hblk hj, Nat.add_sub_cancel_left]
  fixed := fun j hj => by
    rw [hfix, hbs, hfr]
    show front + roundsTo bs (senderOf bs (treesTo bs b + j)) +
      (tl (senderOf bs (treesTo bs b + j))).off
        (treesTo bs b + j - treesTo bs (senderOf bs (treesTo bs b + j))) = _
    rw [senderOf_own hblk hj, Nat.add_sub_cancel_left]

/-- **The construction meets the hypothesis `hfix` of `fits_head`**: a tree that is declared before
a border is fixed by the challenges before that border, if no `off j` exceeds its sub-protocol's
number of rounds. -/
theorem ofLots_hfix
    (hoff : ∀ b blk, bs[b]? = some blk → ∀ j, j < (blk.oracles.flatMap id).length →
      (tl b).off j ≤ blk.rounds.length) :
    ∀ b', b' ≤ bs.length → ∀ t, t < treesTo bs b' →
      (Script.ofLots bs front cells tok pl tl ml).fixed (.own t) ≤ front + roundsTo bs b' := by
  intro b' hb' t ht
  obtain ⟨b, j, blk, hb, hblk, hj, rfl⟩ := tree_split bs b' hb' ht
  show front + roundsTo bs (senderOf bs (treesTo bs b + j)) +
    (tl (senderOf bs (treesTo bs b + j))).off
      (treesTo bs b + j - treesTo bs (senderOf bs (treesTo bs b + j))) ≤ _
  rw [senderOf_own hblk hj, Nat.add_sub_cancel_left]
  have h1 := hoff b blk hblk j hj
  have h2 := roundsTo_succ hblk
  have h3 := roundsTo_mono bs (b + 1) b' (by omega)
  omega

/-! ## 5 The messages -/

/-- **The other lots of the same message agree with this one wherever both answer.** The name and
the wording are those of the authors of another part of this project. It is a definition: the form
of a hypothesis. -/
def LotsAgree (ml : List (MsgLot Bk W)) (L : MsgLot Bk W) : Prop :=
  ∀ L' ∈ ml, L'.n = L.n → ∀ k w (hd : List Fmt.Drawn) mask row place y y',
    L.txt k w (hd.take L.fx) mask row place = some y →
    L'.txt k w (hd.take L'.fx) mask row place = some y' → y' = y

/-- The same for pads. It is a definition: the form of a hypothesis. -/
def PadLotsAgree (pl : List (PadLot Bk W)) (L : PadLot Bk W) : Prop :=
  ∀ L' ∈ pl, L'.j = L.j → L'.t = L.t → ∀ k w mask row place y y',
    L.txt k w mask row place = some y → L'.txt k w mask row place = some y' → y' = y

/-- **The construction meets `OwnMsgs` at a lot of the list**, if the other lots of the same message
agree with it wherever both answer. -/
theorem ofLots_ownMsgs {L : MsgLot Bk W} (hL : L ∈ ml)
    (hagree : LotsAgree ml L)
    (Vd : W → Prop) (N : Nat) :
    OwnMsgs (Script.ofLots bs front cells tok pl tl ml) Vd N L.n L.fx L.txt := by
  intro k w hd _ _ mask row place y hy
  have hle : ∀ L' ∈ ml.filter (·.n == L.n),
      (hd.take (((ml.filter (·.n == L.n)).map (·.fx)).foldl max 0)).take L'.fx =
        hd.take L'.fx := by
    intro L' hL'
    rw [List.take_take, Nat.min_eq_left
      (TypedOracleCompiler.Slice.le_foldl_max _ 0 _ (Or.inl (List.mem_map.2 ⟨L', hL', rfl⟩)))]
  have hLf : L ∈ ml.filter (·.n == L.n) := List.mem_filter.2 ⟨hL, beq_self_eq_true _⟩
  show ((ml.filter (·.n == L.n)).findSome? fun L' =>
    L'.txt k w ((hd.take (((ml.filter (·.n == L.n)).map (·.fx)).foldl max 0)).take L'.fx) mask row
      place).getD 0 = y
  cases hf : (ml.filter (·.n == L.n)).findSome? fun L' =>
    L'.txt k w ((hd.take (((ml.filter (·.n == L.n)).map (·.fx)).foldl max 0)).take L'.fx) mask row
      place with
  | none =>
    have h0 := List.findSome?_eq_none_iff.1 hf L hLf
    rw [hle L hLf, hy] at h0
    cases h0
  | some y' =>
    obtain ⟨L', hL', hy'⟩ := List.exists_of_findSome?_eq_some hf
    rw [hle L' hL'] at hy'
    obtain ⟨hm, hn⟩ := List.mem_filter.1 hL'
    exact hagree L' hm (eq_of_beq hn) k w hd mask row place y y' hy hy'

/-- **The construction meets `OwnPads` at a lot of the list**, if the other lots of the same pad
agree with it wherever both answer. -/
theorem ofLots_ownPads {L : PadLot Bk W} (hL : L ∈ pl)
    (hagree : PadLotsAgree pl L)
    (Vd : W → Prop) :
    OwnPads (Script.ofLots bs front cells tok pl tl ml) Vd L.j L.t L.txt := by
  intro k w _ mask row place y hy
  have hLf : L ∈ pl.filter fun L' => L'.j == L.j && L'.t == L.t :=
    List.mem_filter.2 ⟨hL, by rw [beq_self_eq_true, beq_self_eq_true]; rfl⟩
  show ((pl.filter fun L' => L'.j == L.j && L'.t == L.t).findSome? fun L' =>
    L'.txt k w mask row place).getD 0 = y
  cases hf : (pl.filter fun L' => L'.j == L.j && L'.t == L.t).findSome? fun L' =>
    L'.txt k w mask row place with
  | none =>
    have h0 := List.findSome?_eq_none_iff.1 hf L hLf
    rw [hy] at h0
    cases h0
  | some y' =>
    obtain ⟨L', hL', hy'⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨hm, hn⟩ := List.mem_filter.1 hL'
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hn
    exact hagree L' hm (eq_of_beq h1) (eq_of_beq h2) k w mask row place y y' hy hy'

/-- **All lots of one message agree wherever two of them answer.** It is a definition: the form of a
hypothesis. -/
def MsgsAgree (ml : List (MsgLot Bk W)) : Prop :=
  ∀ L ∈ ml, LotsAgree ml L

/-- The same for pads. It is a definition: the form of a hypothesis. -/
def PadsAgree (pl : List (PadLot Bk W)) : Prop :=
  ∀ L ∈ pl, PadLotsAgree pl L

/-- Where the lots of messages agree, the construction meets `OwnMsgs` at every one of them. -/
theorem ofLots_ownMsgs_all (h : MsgsAgree ml) (Vd : W → Prop) (N : Nat) :
    ∀ L ∈ ml, OwnMsgs (Script.ofLots bs front cells tok pl tl ml) Vd N L.n L.fx L.txt :=
  fun L hL => ofLots_ownMsgs bs front cells tok pl tl ml hL (h L hL) Vd N

/-- Where the lots of pads agree, the construction meets `OwnPads` at every one of them. -/
theorem ofLots_ownPads_all (h : PadsAgree pl) (Vd : W → Prop) :
    ∀ L ∈ pl, OwnPads (Script.ofLots bs front cells tok pl tl ml) Vd L.j L.t L.txt :=
  fun L hL => ofLots_ownPads bs front cells tok pl tl ml hL (h L hL) Vd

/-- **The construction passes the test on the messages.** `born n`: the border from which message
`n` is spoken of. `hfx`: each lot's `fx` is at most `front` plus the rounds before that border. -/
theorem ofLots_msgsFit (born : Nat → Nat) (nMsg : Nat)
    (hfx : ∀ L ∈ ml, L.fx ≤ front + roundsTo bs (born L.n)) :
    (Script.ofLots bs front cells tok pl tl ml).msgsFit front bs born nMsg = true := by
  unfold Script.msgsFit
  refine List.all_eq_true.2 fun n _ => decide_eq_true ?_
  show ((ml.filter (·.n == n)).map (·.fx)).foldl max 0 ≤ _
  refine Johnson.G.foldl_max_le id _ _ 0 (Nat.zero_le _) fun a ha => ?_
  show a ≤ _
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 ha
  obtain ⟨hm, hn⟩ := List.mem_filter.1 hL
  have h1 := hfx L hm
  rw [eq_of_beq hn] at h1
  exact h1

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.ownTreesAt_of_own
#print axioms ProofFile.Honest.FirstThread.treesTo_mono
#print axioms ProofFile.Honest.FirstThread.roundsTo_succ
#print axioms ProofFile.Honest.FirstThread.tree_split
#print axioms ProofFile.Honest.FirstThread.senderOf_own
#print axioms ProofFile.Honest.FirstThread.ofLots_ownTrees
#print axioms ProofFile.Honest.FirstThread.ofLots_hfix
#print axioms ProofFile.Honest.FirstThread.ofLots_ownMsgs
#print axioms ProofFile.Honest.FirstThread.ofLots_ownPads
#print axioms ProofFile.Honest.FirstThread.ofLots_ownMsgs_all
#print axioms ProofFile.Honest.FirstThread.ofLots_ownPads_all
#print axioms ProofFile.Honest.FirstThread.ofLots_msgsFit
