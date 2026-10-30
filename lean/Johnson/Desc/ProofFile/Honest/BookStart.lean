-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookStart.lean: the maker of the book of coins (`ProverCoinCounts`,
Honest/Frame.lean), twelfth file: WHERE A PART's STRETCH OF ITS SEGMENT's MASK ROW STARTS AMONG THE
SENDER's OWN COINS, AS ONE FUNCTION OF THE PLAN, with the statements that hold it against the
entries that Honest/BookEntries.lean makes. Definitions with code, tests at that file's synthetic
lists, and statements with proofs, all by unfolding and by induction over that file's own
definitions.

  `scalarsInFront`   how many of the segment's own scalars the parts in front of a part send
  `segmentParts`     a segment's parts, in order: what `segmentWants` runs over
  `startOf`          the number, among the sender's coins of the extension field, of the first entry
                    that the part at an address spends of the mask row: where the row's entries
                    begin (`MsgAt.base`: `maskStart`, Honest/BookRows.lean) plus `scalarsInFront`
  `Want.entry_start`, `entry_count`, `entry_owner`, `entry_spender`   the book's entry of a stretch,
                    field by field
  `partWants_all`, `partWants_spender`, `partWants_first`   one part's stretches name that part;
                    each but the end values' lies in the mask row and begins at the part's first
                    scalar's number
  `partsWants_mem`, `partsWants_first`     the like for parts in a row, whose addresses are distinct
  `segment_start`    AT A SEGMENT WHOSE PARTS' ADDRESSES ARE DISTINCT: a stretch that `segmentWants`
                    makes and that is not the end
                    values': its entry's owner is the mask row's sender, and its entry starts at
                    `startOf`

Limits. The end values' stretches are left out: at a merge they lie in the index-mask message, else
behind the part's other scalars. That the verifier's count of slots is the count of scalars sent,
that the sender lays its coin of that number at the row's place of that number, and that a reader
reads that place: three other statements, none here. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

variable {S Cl : Type}

/-- **How many of the segment's own scalars the parts in front of the part at a send.** `none` where
no part of the list stands at a. -/
def scalarsInFront : List PartAt → Addr → Option Nat
  | [], _ => none
  | p :: ps, a => if p.addr = a then some 0 else (scalarsInFront ps a).map (· + p.ownScalars)

/-- A segment's parts, in order. -/
def segmentParts (bs : List (Block S Cl)) (l : Nat) : List PartAt :=
  (bs.filter fun b => b.place.link == some l).flatMap planParts

/-- **Where the part's stretch of the mask row starts among the sender's coins of the extension
field.** row: the segment's mask row. -/
def startOf (bs : List (Block S Cl)) (l : Nat) (row : MsgAt) (a : Addr) : Option Nat :=
  (scalarsInFront (segmentParts bs l) a).map (row.base.e + ·)

theorem Want.entry_start (w : Want) : w.entry.start.e = w.msg.base.e + w.number := rfl
theorem Want.entry_count (w : Want) : w.entry.count.e = w.count := rfl
theorem Want.entry_owner (w : Want) : w.entry.owner = w.msg.owner := rfl
theorem Want.entry_spender (w : Want) : w.entry.spender = w.spender := rfl

/-- One part's stretches name that part; each but the end values' lies in the mask row and begins at
the number j. -/
theorem partWants_all {row idx : MsgAt} {merge : Bool} {p : PartAt} {j t : Nat} {w : Want}
    (h : w ∈ (partWants row idx merge p j t).1) :
    w.spender = p.addr ∧ (w.use ≠ "ends" → w.msg = row ∧ w.number = j) := by
  unfold partWants at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · rcases List.mem_singleton.mp h with rfl
      exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
    · split at h
      · rcases List.mem_singleton.mp h with rfl
        exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
      · split at h
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
          · rcases List.mem_singleton.mp h with rfl
            exact ⟨rfl, fun c => absurd rfl c⟩
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
          · rcases List.mem_singleton.mp h with rfl
            exact ⟨rfl, fun c => absurd rfl c⟩

theorem partWants_spender {row idx : MsgAt} {merge : Bool} {p : PartAt} {j t : Nat} {w : Want}
    (h : w ∈ (partWants row idx merge p j t).1) : w.spender = p.addr := (partWants_all h).1

theorem partWants_first {row idx : MsgAt} {merge : Bool} {p : PartAt} {j t : Nat} {w : Want}
    (h : w ∈ (partWants row idx merge p j t).1) (hu : w.use ≠ "ends") :
    w.msg = row ∧ w.number = j := (partWants_all h).2 hu

/-- A stretch of parts in a row names one of them. -/
theorem partsWants_mem {row idx : MsgAt} {merges : List Addr} {w : Want} :
    ∀ (ps : List PartAt) (j t : Nat), w ∈ (partsWants row idx merges ps j t).1 →
      w.spender ∈ ps.map (·.addr)
  | [], _, _, h => by cases h
  | p :: ps, j, t, h => by
    unfold partsWants at h
    dsimp only at h
    rcases List.mem_append.mp h with h | h
    · rw [partWants_spender h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (partsWants_mem ps _ _ h)

/-- **Parts in a row, at distinct addresses**: a stretch that is not the end values' lies in the
mask row and begins at j plus the scalars of the parts in front of its part. -/
theorem partsWants_first {row idx : MsgAt} {merges : List Addr} {w : Want} :
    ∀ (ps : List PartAt) (j t : Nat), (ps.map (·.addr)).Nodup →
      w ∈ (partsWants row idx merges ps j t).1 → w.use ≠ "ends" →
      w.msg = row ∧ ∃ n, scalarsInFront ps w.spender = some n ∧ w.number = j + n
  | [], _, _, _, h, _ => by cases h
  | p :: ps, j, t, hn, h, hu => by
    unfold partsWants at h
    dsimp only at h
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_append.mp h with h | h
    · refine ⟨(partWants_first h hu).1, 0, ?_, (partWants_first h hu).2⟩
      unfold scalarsInFront
      rw [if_pos (partWants_spender h).symm]
    · obtain ⟨hm, n, h1, h2⟩ := partsWants_first ps _ _ hn'.2 h hu
      have hne : p.addr ≠ w.spender := by
        intro e
        apply hn'.1
        show p.addr ∈ ps.map (·.addr)
        rw [e]
        exact partsWants_mem ps _ _ h
      refine ⟨hm, n + p.ownScalars, ?_, by omega⟩
      unfold scalarsInFront
      rw [if_neg hne, h1]
      rfl

/-- **At a segment whose parts' addresses are distinct** (`hn`): the entry of a stretch that is not
the end values': its owner is the mask row's sender; it starts at `startOf`; it has the stretch's
count. -/
theorem segment_start {bs : List (Block S Cl)} {l : Nat} {row idx : MsgAt} {merges : List Addr}
    {t : Nat} {w : Want} (hn : ((segmentParts bs l).map (·.addr)).Nodup)
    (h : w ∈ (segmentWants bs l row idx merges t).1) (hu : w.use ≠ "ends") :
    w.entry.owner = row.owner ∧ startOf bs l row w.spender = some w.entry.start.e ∧
      w.entry.count.e = w.count := by
  obtain ⟨hm, n, h1, h2⟩ := partsWants_first (segmentParts bs l) 0 t hn h hu
  refine ⟨by rw [Want.entry_owner, hm], ?_, rfl⟩
  unfold startOf
  rw [h1, Want.entry_start, hm, h2]
  simp

/-! ### Tests at the synthetic lists of Honest/BookEntries.lean -/

-- every stretch of the toy segment that is not the end values' starts where `startOf` says
#guard toyWants.1.all fun w =>
  w.use == "ends" || startOf toySeg 0 toyRow w.spender == some w.entry.start.e
-- no part stands at an address of another place
#guard (startOf toySeg 0 toyRow ⟨⟨1, some 0, 99, .K3⟩, 0⟩).isNone

end ProofFile.Honest

#print axioms ProofFile.Honest.Want.entry_start
#print axioms ProofFile.Honest.Want.entry_count
#print axioms ProofFile.Honest.Want.entry_owner
#print axioms ProofFile.Honest.Want.entry_spender
#print axioms ProofFile.Honest.partWants_all
#print axioms ProofFile.Honest.partWants_spender
#print axioms ProofFile.Honest.partWants_first
#print axioms ProofFile.Honest.partsWants_mem
#print axioms ProofFile.Honest.partsWants_first
#print axioms ProofFile.Honest.segment_start
