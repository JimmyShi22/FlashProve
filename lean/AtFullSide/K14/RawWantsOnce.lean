-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawWantsOnce.lean: AT THE WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean),
THE LIBRARY's WRITTEN LIST OF THE FIRST CHAIN's SENDINGS AND THE MERGES THAT mergesByName
(Honest/BookWhole.lean) GUESSES: WHATEVER linksWants RETURNS THERE: OF THE STRETCHES THAT
spendingBook ASKS wantsFree ABOUT, ANY TWO AT DIFFERENT NUMBERS OF THE LIST GIVE ENTRIES THAT HAVE
NO COIN IN COMMON (Ahead.shares, Honest/Frame.lean). THE STRETCHES' ENTRIES ARE NOT ALL THAT SPENDS
IN A BOOK: the entries on fold masks and the shared split's one coin stand behind them and are
outside this list: of a stretch against one of these nothing is said. Two definitions, one with
code; statements with their proofs.

  rawMsgsOk, rawMsgs_written   **every stretch's message is the index-mask message or the mask row
                  of the link of its spender, AS WRITTEN** (rawIdxW, rawRowsW,
                  AtFullSide/K14/RawFactsWritten.lean): name, owner, base and free entries: ONE
                  EVALUATION IN LEAN's KERNEL. rawMsgs_bent, rawMsgs_bent_rows: each of its two
                  clauses can fail
  rawWants_msg, rawWants_msg_mem   that, out of the Bool. The first one's clause on the spender's
                  link is called by nothing yet
  rawMsgsW, rawMsgsW_keys, rawMsgsW_rooms   the 26 written messages: owner and base tell them apart;
                  two with one owner and two bases have their free entries one behind the other.
                  Both by a plain decide over the written values. (There is one such pair, the
                  index-mask message and link 0's mask row: by a reading of the 26; no theorem.)
  rawWants_same_msg   **owner and base settle a stretch's message**: so whoever holds two stretches'
                  owners and bases (AtFullSide/K14/RawWantsAtSpenders.lean has them at two parts)
                  has the premise of rawWants_apart (AtFullSide/K14/RawWantsApart.lean)
  rawWants_once_owner   **two stretches of one owner have no coin in common**, as runs among the
                  owner's coins of the extension field: one base: rawWants_apart; two bases:
                  rawWants_within and rawMsgsW_rooms
  rawWants_once   **the statement of the first sentence**: other owners: no coin in common by the
                  word's first clause; of the base field a stretch's entry takes none
  rawWants_once_parts   **the same by two spenders**: two stretches of the list whose spenders are
                  two give entries that have no coin in common: for a caller that holds two parts

OPTIONS ARE RAISED in front of the three evaluations: maxRecDepth to 1000000 (no lower number was
tried), and maxHeartbeats is lifted. This side library's files Lean compiles with a larger stack
(lakefile.toml). No other option is raised.
Kin. meets_shift (Honest/BookLinear/Seventh.lean) and meets_false_of_front, meets_false_of_back
(Honest/BookFreeOf.lean) are called. The frame's Honest/BookApart.lean has the general law in the
same word, for ALL spending entries of a book that fails none of its own tests;
Honest/BookLinear/Seventh.lean (spent_apart, clause7S) a test of another make for that whole list.
This file has the stretches alone, at one written description, with no premise on a book: from the
maker's own test (rawWants_written) and one evaluation of its own.
What is assumed. Nothing.
What is not claimed. "ONCE" FOR ALL THAT SPENDS (the first paragraph). A fact on the list of
stretches and on Want.entry of its members, not on a book: that spendingBook, bookRaw or bookWhole
returns, and that a book's entries begin with these, is not said here. THAT ANY DESCRIPTION BUT WP
HAS SUCH STRETCHES; the sendings are found by labels that rest on one print; the merges are a guess
(the limits of AtFullSide/K14/RawWantsWritten.lean, all). Numbers and addresses: nothing on
soundness, completeness or hiding.
-/
import AtFullSide.K14.RawWantsApart
import Johnson.Desc.ProofFile.Honest.BookLinear.Seventh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **The test**: at what linksWants returns: every stretch's message is i, or the mask row that the
list rows has at the link of the stretch's spender. Rejects where linksWants rejects. -/
def rawMsgsOk (i : MsgAt) (rows : List (Nat × MsgAt)) : Bool :=
  match linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW (mergesByName WP.first.blocksInOrder).ends
      (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 with
  | .ok a => (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).all
        fun w => w.msg == i || (match w.spender.place.link with
          | some l => rows.contains (l, w.msg)
          | none => false)
  | .error _ => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **It accepts at the index-mask message as written**: one evaluation in Lean's kernel. -/
theorem rawMsgs_written : rawMsgsOk rawIdxW rawRowsW = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The evaluation can fail: with one free entry fewer in the message that it compares with, it
rejects. -/
theorem rawMsgs_bent : rawMsgsOk { rawIdxW with free := 254 } rawRowsW = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- So can its clause on the rows: without the last written row it rejects. -/
theorem rawMsgs_bent_rows : rawMsgsOk rawIdxW rawRowsW.dropLast = false := by decide +kernel

/-- The 26 written messages: the index-mask message and the 25 links' mask rows. -/
def rawMsgsW : List MsgAt := rawIdxW :: rawRowsW.map (·.2)

/-- Owner and base tell the 26 apart. -/
theorem rawMsgsW_keys : (rawMsgsW.map fun m => (m.owner, m.base)).Nodup := by decide

/-- Two of the 26 with one owner and two bases: the free entries of the one end where the other's
begin or before, in the bases' second numbers (coins of the extension field). -/
theorem rawMsgsW_rooms : ∀ m ∈ rawMsgsW, ∀ m' ∈ rawMsgsW, m.owner = m'.owner → m.base ≠ m'.base →
    m.base.e + m.free ≤ m'.base.e ∨ m'.base.e + m'.free ≤ m.base.e := by decide

/-- **EVERY STRETCH's MESSAGE IS THE INDEX-MASK MESSAGE OR THE MASK ROW OF ITS SPENDER's LINK**, as
written: name, owner, base and free entries. -/
theorem rawWants_msg : ∀ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a →
    ∀ w ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1),
    w.msg = rawIdxW ∨ ∃ l, w.spender.place.link = some l ∧ (l, w.msg) ∈ rawRowsW := by
  intro a ha w hw
  have h := rawMsgs_written
  unfold rawMsgsOk at h
  rw [ha] at h
  have h1 := List.all_eq_true.1 h w hw
  rcases Bool.or_eq_true_iff.1 h1 with h2 | h2
  · exact .inl (beq_iff_eq.1 h2)
  · cases hl : w.spender.place.link with
    | none =>
      rw [hl] at h2
      cases h2
    | some l =>
      rw [hl] at h2
      exact .inr ⟨l, rfl, List.contains_iff_mem.1 h2⟩

/-- So it is one of the 26. -/
theorem rawWants_msg_mem : ∀ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a →
    ∀ w ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1),
    w.msg ∈ rawMsgsW := by
  intro a ha w hw
  rcases rawWants_msg a ha w hw with h | ⟨l, -, h⟩
  · rw [h]
    exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, h, rfl⟩)

/-- **OWNER AND BASE SETTLE A STRETCH's MESSAGE.** -/
theorem rawWants_same_msg : ∀ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a →
    ∀ x ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1),
    ∀ y ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1),
    x.msg.owner = y.msg.owner → x.msg.base = y.msg.base → x.msg = y.msg := by
  intro a ha x hx y hy ho hb
  exact List.inj_on_of_nodup_map rawMsgsW_keys (rawWants_msg_mem a ha x hx)
    (rawWants_msg_mem a ha y hy) (Prod.ext ho hb)

/-- **TWO STRETCHES OF ONE OWNER, AT TWO NUMBERS OF THE LIST, HAVE NO COIN IN COMMON**: as runs
among the owner's coins of the extension field. -/
theorem rawWants_once_owner : ∀ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a →
    ∀ x ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).zipIdx,
    ∀ y ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).zipIdx,
    x.2 ≠ y.2 → x.1.msg.owner = y.1.msg.owner →
      meets (x.1.msg.base.e + x.1.number) x.1.count (y.1.msg.base.e + y.1.number) y.1.count =
        false := by
  intro a ha x hx y hy hn ho
  have mx := List.fst_mem_of_mem_zipIdx hx
  have my := List.fst_mem_of_mem_zipIdx hy
  by_cases hb : x.1.msg.base = y.1.msg.base
  · have hm := rawWants_same_msg a ha x.1 mx y.1 my ho hb
    rw [hb, meets_shift]
    exact rawWants_apart a ha x hx y hy hn hm
  · have wx := rawWants_within a ha x.1 mx
    have wy := rawWants_within a ha y.1 my
    rcases rawMsgsW_rooms _ (rawWants_msg_mem a ha x.1 mx) _ (rawWants_msg_mem a ha y.1 my) ho hb
      with h | h
    · exact meets_false_of_front (.inr (.inr (by omega)))
    · exact meets_false_of_back (.inr (.inr (by omega)))

/-- **TWO STRETCHES AT TWO NUMBERS OF THE LIST: THEIR ENTRIES HAVE NO COIN IN COMMON**, in the
book's own word (Ahead.shares, Honest/Frame.lean). -/
theorem rawWants_once : ∀ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a →
    ∀ x ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).zipIdx,
    ∀ y ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).zipIdx,
    x.2 ≠ y.2 → x.1.entry.shares y.1.entry = false := by
  intro a ha x hx y hy hn
  unfold Ahead.shares
  by_cases ho : x.1.msg.owner = y.1.msg.owner
  · have h := rawWants_once_owner a ha x hx y hy hn ho
    have h0 : meets x.1.entry.start.f x.1.entry.count.f y.1.entry.start.f y.1.entry.count.f =
        false := meets_false_of_front (.inl rfl)
    have h1 : meets x.1.entry.start.e x.1.entry.count.e y.1.entry.start.e y.1.entry.count.e =
        false := h
    rw [h0, h1]
    simp
  · have h2 : (x.1.entry.owner == y.1.entry.owner) = false := beq_eq_false_iff_ne.2 ho
    rw [h2]
    rfl

/-- **TWO STRETCHES WITH TWO SPENDERS: THEIR ENTRIES HAVE NO COIN IN COMMON.** -/
theorem rawWants_once_parts : ∀ a, linksWants WP.first.blocksInOrder proofSendsFull.1 rawLater rawIdxW
    (mergesByName WP.first.blocksInOrder).ends (WP.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
      .ok a →
    ∀ x ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1),
    ∀ y ∈ (a.1 ++ (loneWants rawIdxW (mergesByName WP.first.blocksInOrder).lone
      ((WP.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1),
    x.spender ≠ y.spender → x.entry.shares y.entry = false := by
  intro a ha x hx y hy hs
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hy
  refine rawWants_once a ha (x, i) (List.mem_zipIdx_iff_getElem?.2 hi) (y, j)
    (List.mem_zipIdx_iff_getElem?.2 hj) fun e => hs ?_
  have e' : i = j := e
  subst e'
  rw [Option.some.inj (hi.symm.trans hj)]

end AtFullSide.K14

#print axioms AtFullSide.K14.rawMsgs_written
#print axioms AtFullSide.K14.rawMsgs_bent
#print axioms AtFullSide.K14.rawMsgs_bent_rows
#print axioms AtFullSide.K14.rawMsgsW_keys
#print axioms AtFullSide.K14.rawMsgsW_rooms
#print axioms AtFullSide.K14.rawWants_msg
#print axioms AtFullSide.K14.rawWants_msg_mem
#print axioms AtFullSide.K14.rawWants_same_msg
#print axioms AtFullSide.K14.rawWants_once_owner
#print axioms AtFullSide.K14.rawWants_once
#print axioms AtFullSide.K14.rawWants_once_parts
