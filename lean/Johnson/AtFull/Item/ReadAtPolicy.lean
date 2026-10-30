-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Item/ReadAtPolicy.lean: what the item's reader of the parameter file
(`Proof.ParamLines.read`, OnBytes/Proof/RequestItem.lean) returns on `VerifierAndGoals.policyFile v`, at all
values v of the eight free numbers: a written list of lines, each cut at its blanks. A law: the file
is not evaluated.

Why. In the goals' scope the parameter file is `policyFile v` (Ladder/Stored.lean). Lean's kernel
did not get through `ByteArray.toList` on the stored file's 2,629 bytes.
Johnson/Goal/Meaning/ScopeLines.lean has the file's bytes as written lines, for the scan's reader.
Here the same is had for the item's reader.

Main names.
* `rawAt v`: the file's lines without their line feeds: the 32 lines of the frame, four written
  lists, and between them the eleven free lines.
* `bytes_policyFile`: the file's bytes are these lines, each with its line feed.
* `splitAt_joined`: cutting such a text at the line feeds gives the lines back, and an empty piece.
* `read_policyFile`: `ParamLines.read (policyFile v)` is `rawAt v` with each line cut at its blanks.

Limits. General in v; nothing on any other file. The order of the lines is the file's. No soundness
is claimed.
-/
import Johnson.Goal.Meaning.ScopeLines
import OnBytes.Proof.RequestItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Item
open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Config
open VerifierAndGoals VerifierAndGoals.Lines

/-- Free lines without their line feeds. -/
def fl0 (l : List (String × Nat)) : List (List UInt8) := l.map fun p => fl p.1 p.2

/-- The lines of `policyFile v`, without their line feeds. -/
def rawAt (v : FreeLines) : List (List UInt8) :=
  frameLines ++ (linesA1 ++ (fl0 (free1 v) ++ (linesA2 ++ (fl0 (free2 v) ++
    (linesA3 ++ (fl0 (free3 v) ++ linesB))))))

/-- `concatenatedWithLineFeeds` of two lists of lines: the two joined texts, one behind the other. -/
theorem joined_append (a b : List (List UInt8)) : concatenatedWithLineFeeds (a ++ b) = concatenatedWithLineFeeds a ++ concatenatedWithLineFeeds b := by
  unfold concatenatedWithLineFeeds fed
  rw [List.map_append, List.flatten_append]

/-- `concatenatedWithLineFeeds` of a line and more lines: the line, a line feed, and the rest. -/
theorem joined_cons (l : List UInt8) (t : List (List UInt8)) :
    concatenatedWithLineFeeds (l :: t) = l ++ 0x0A :: concatenatedWithLineFeeds t := by
  unfold concatenatedWithLineFeeds fed
  simp

/-- **The bytes of the parameter file are its lines, each with its line feed.** -/
theorem bytes_policyFile (v : FreeLines) : (policyFile v).toList = concatenatedWithLineFeeds (rawAt v) := by
  have e : (policyFile v).toList = concatenatedWithLineFeeds frameLines ++ bytesOf (behindText v) := by
    rw [← frame_bytes, policyFile_eq, K.Left.toList_data, K.Left.toList_data,
      ByteArray.data_append, Array.toList_append, ConfigReaders.bytesOf_data]
  have e1 : "\neps1_hi " = "\n" ++ "eps1_hi " := by decide +kernel
  have e2 : "\neps2_hi " = "\n" ++ "eps2_hi " := by decide +kernel
  have e3 : "\nKF " = "\n" ++ "KF " := by decide +kernel
  have e4 : "\nepsF_hi " = "\n" ++ "epsF_hi " := by decide +kernel
  have e5 : "\ntheta " = "\n" ++ "theta " := by decide +kernel
  have e6 : "\ncap " = "\n" ++ "cap " := by decide +kernel
  rw [e]
  unfold rawAt behindText
  simp only [toString, e1, e2, e3, e4, e5, e6, bytesOf_append, feed_text, bytesA1, bytesA2,
    bytesA3, bytesB, joined_append, joined_cons, fl0, free1, free2, free3, fl, List.map_cons,
    List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Cutting, as a walk from the right. -/
theorem splitAt_foldr (c : UInt8) (l : List UInt8) :
    splitAt c l = l.foldr (fun x acc =>
      if x == c then [] :: acc
      else
        match acc with
        | [] => [[x]]
        | p :: ps => (x :: p) :: ps) [[]] := by
  unfold splitAt
  rw [List.foldl_reverse]
  rfl

/-- A piece without the byte c, then c, then more. -/
theorem splitAt_piece (c : UInt8) : ∀ (l : List UInt8), (∀ x ∈ l, x ≠ c) → ∀ t : List UInt8,
    splitAt c (l ++ c :: t) = l :: splitAt c t
  | [], _, t => by
    rw [List.nil_append, splitAt_foldr, List.foldr_cons, ← splitAt_foldr]
    simp
  | x :: l, h, t => by
    have hx : (x == c) = false := by simpa using h x (List.mem_cons_self ..)
    have ih := splitAt_piece c l (fun y hy => h y (List.mem_cons_of_mem _ hy)) t
    rw [List.cons_append, splitAt_foldr, List.foldr_cons, ← splitAt_foldr, ih, hx]
    rfl

/-- **Cutting a text of lines at the line feeds gives the lines back**, and an empty piece. -/
theorem splitAt_joined : ∀ (ls : List (List UInt8)), (∀ l ∈ ls, ∀ x ∈ l, x ≠ 0x0A) →
    splitAt 0x0A (concatenatedWithLineFeeds ls) = ls ++ [[]]
  | [], _ => rfl
  | l :: ls, h => by
    rw [joined_cons, splitAt_piece 0x0A l (h l (List.mem_cons_self ..)),
      splitAt_joined ls fun m hm => h m (List.mem_cons_of_mem _ hm)]
    rfl

/-- Lines that are not empty stay; the empty piece at the end goes. -/
theorem filter_lines : ∀ (ls : List (List UInt8)), (∀ l ∈ ls, l ≠ []) →
    (ls ++ [[]]).filter (fun l => !l.isEmpty) = ls
  | [], _ => rfl
  | l :: ls, h => by
    have hl : (!l.isEmpty) = true := by
      have := h l (List.mem_cons_self ..)
      cases l with
      | nil => exact absurd rfl this
      | cons _ _ => rfl
    rw [List.cons_append, List.filter_cons]
    simp only [hl, if_true]
    rw [filter_lines ls fun m hm => h m (List.mem_cons_of_mem _ hm)]

/-- A written list of lines: none is empty, none holds a line feed. -/
def plainB (ls : List (List UInt8)) : Bool :=
  ls.all fun l => !l.isEmpty && l.all fun x => x != 0x0A

/-- What `plainB` says: no line is empty, and no line holds a line feed. -/
theorem plain_of {ls : List (List UInt8)} (h : plainB ls = true) :
    ∀ l ∈ ls, l ≠ [] ∧ ∀ x ∈ l, x ≠ 0x0A := by
  intro l hl
  have := List.all_eq_true.1 h l hl
  rw [Bool.and_eq_true] at this
  refine ⟨?_, fun x hx => by simpa using List.all_eq_true.1 this.2 x hx⟩
  intro e
  rw [e] at this
  exact absurd this.1 (by decide)

/-- A free line is not empty and holds no line feed, where its name is so. -/
theorem free_plain {q : String} (hq : plainB [bytesOf q] = true) (x : Nat) :
    fl q x ≠ [] ∧ ∀ c ∈ fl q x, c ≠ 0x0A := by
  obtain ⟨h0, h1⟩ := plain_of hq _ (List.mem_singleton.2 rfl)
  refine ⟨?_, fun c hc => ?_⟩
  · intro e
    exact h0 (List.append_eq_nil_iff.1 e).1
  · rcases List.mem_append.1 hc with h | h
    · exact h1 c h
    · exact feed_not_mem x c h

/-- Every line of the file is not empty and holds no line feed. -/
theorem raw_plain (v : FreeLines) : ∀ l ∈ rawAt v, l ≠ [] ∧ ∀ x ∈ l, x ≠ 0x0A := by
  intro l hl
  unfold rawAt at hl
  simp only [List.mem_append, fl0, free1, free2, free3, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h | h | h | h | h
  · exact plain_of (by decide +kernel) l h
  · exact plain_of (by decide +kernel) l h
  · rcases h with rfl | rfl | rfl | rfl <;> exact free_plain (by decide +kernel) _
  · exact plain_of (by decide +kernel) l h
  · rcases h with rfl | rfl | rfl | rfl <;> exact free_plain (by decide +kernel) _
  · exact plain_of (by decide +kernel) l h
  · rcases h with rfl | rfl | rfl <;> exact free_plain (by decide +kernel) _
  · exact plain_of (by decide +kernel) l h

/-- **What the item's reader returns on the parameter file**, at all values of the eight free
numbers. -/
theorem read_policyFile (v : FreeLines) :
    ParamLines.read (policyFile v) = ⟨(rawAt v).map (splitAt 0x20)⟩ := by
  unfold ParamLines.read
  rw [bytes_policyFile, splitAt_joined _ fun l hl => (raw_plain v l hl).2,
    filter_lines _ fun l hl => (raw_plain v l hl).1]

end Johnson.AtFull.Item

#print axioms Johnson.AtFull.Item.joined_append
#print axioms Johnson.AtFull.Item.joined_cons
#print axioms Johnson.AtFull.Item.bytes_policyFile
#print axioms Johnson.AtFull.Item.splitAt_foldr
#print axioms Johnson.AtFull.Item.splitAt_piece
#print axioms Johnson.AtFull.Item.splitAt_joined
#print axioms Johnson.AtFull.Item.filter_lines
#print axioms Johnson.AtFull.Item.plain_of
#print axioms Johnson.AtFull.Item.free_plain
#print axioms Johnson.AtFull.Item.raw_plain
#print axioms Johnson.AtFull.Item.read_policyFile
#print axioms Johnson.AtFull.Item.fl0
#print axioms Johnson.AtFull.Item.rawAt
#print axioms Johnson.AtFull.Item.plainB
