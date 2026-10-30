-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Grows.lean: a statement only grows: a relation on the plain record of a statement, and
that each of the plain changes of a statement keeps it. Theorems.

  GroupGrows G G'    the same code and mask code; a mark inRun is not taken back; every member
                     stays a member.
  OracleGrows x x'   the same shape; the mark sampled is not taken back; every group that the
                     message names stays named.
  Grows T T'         the same codes; at every number at which T has a group, T' has one that has
                     grown out of it; the like for the oracle messages. So none is dropped, none
                     changes its number, none loses a mark.
  Grows.refl, Grows.trans
  grows_modGroup, grows_modOracle   a change of one group, or one message, that grows it.
  grows_stSent · grows_withGroup · grows_admitted · grows_joined · grows_withRow ·
  grows_closeLedgers · grows_begun  the plain changes of a statement, one by one.
WHAT OF `verify-on-bytes` IS USED: its plain records Statement, Group and Oracle
(OnBytes/Iop/Ground.lean) and the pure functions on them stSent, withGroup, admitted, withMessageInGroup,
withRow, closeLedgers, begun (OnBytes/Slice/). No routine in a context is reached from a statement
or a proof here.
What is not claimed. NOTHING ON ROWS: a group's open rows, a message's sample rows, its pad and its
ledger are left out of the relation: rows are taken out where a test begins. A member's place among
the members may move. Nothing on which block of the protocol makes which change.

-/
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Slice

/-- A group has grown out of another. -/
def GroupGrows (G G' : Group) : Prop :=
  G'.code = G.code ∧ G'.maskCode = G.maskCode ∧ (G.inRun = true → G'.inRun = true) ∧
    ∀ o ∈ G.members, o ∈ G'.members

/-- An oracle message has grown out of another. -/
def OracleGrows (x x' : Oracle) : Prop :=
  x'.shape = x.shape ∧ (x.sampled = true → x'.sampled = true) ∧ ∀ g ∈ x.groups, g ∈ x'.groups

/-- **A statement has grown out of another.** -/
def Grows (T T' : Statement) : Prop :=
  T'.codes = T.codes ∧
    (∀ (i : Nat) G, T.groups[i]? = some G → ∃ G', T'.groups[i]? = some G' ∧ GroupGrows G G') ∧
    ∀ (i : Nat) x, T.oracles[i]? = some x → ∃ x', T'.oracles[i]? = some x' ∧ OracleGrows x x'

/-- A group has grown out of itself. -/
theorem GroupGrows.refl (G : Group) : GroupGrows G G := ⟨rfl, rfl, id, fun _ h => h⟩

/-- Growing goes on: from G to G' to G''. -/
theorem GroupGrows.trans {A B C : Group} (h : GroupGrows A B) (k : GroupGrows B C) :
    GroupGrows A C :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, fun x => k.2.2.1 (h.2.2.1 x),
    fun o x => k.2.2.2 o (h.2.2.2 o x)⟩

/-- An oracle message has grown out of itself. -/
theorem OracleGrows.refl (x : Oracle) : OracleGrows x x := ⟨rfl, id, fun _ h => h⟩

/-- Growing goes on, for oracle messages. -/
theorem OracleGrows.trans {a b c : Oracle} (h : OracleGrows a b) (k : OracleGrows b c) :
    OracleGrows a c :=
  ⟨k.1.trans h.1, fun x => k.2.1 (h.2.1 x), fun g x => k.2.2 g (h.2.2 g x)⟩

/-- A statement has grown out of itself. -/
theorem Grows.refl (T : Statement) : Grows T T :=
  ⟨rfl, fun _ G h => ⟨G, h, GroupGrows.refl G⟩, fun _ x h => ⟨x, h, OracleGrows.refl x⟩⟩

/-- Growing goes on, for statements. -/
theorem Grows.trans {A B C : Statement} (h : Grows A B) (k : Grows B C) : Grows A C := by
  refine ⟨k.1.trans h.1, fun i G hG => ?_, fun i x hx => ?_⟩
  · obtain ⟨G', h1, g1⟩ := h.2.1 i G hG
    obtain ⟨G'', h2, g2⟩ := k.2.1 i G' h1
    exact ⟨G'', h2, g1.trans g2⟩
  · obtain ⟨x', h1, g1⟩ := h.2.2 i x hx
    obtain ⟨x'', h2, g2⟩ := k.2.2 i x' h1
    exact ⟨x'', h2, g1.trans g2⟩

/-- An array of which one entry is changed: every entry is related to what stood there. -/
theorem modify_rel {α : Type} (P : α → α → Prop) (hr : ∀ a, P a a) (xs : Array α) (k : Nat)
    (f : α → α) (hf : ∀ a, P a (f a)) (i : Nat) (a : α) (h : xs[i]? = some a) :
    ∃ a', (xs.modify k f)[i]? = some a' ∧ P a a' := by
  rw [Array.getElem?_modify]
  split
  · exact ⟨f a, by simp [h], hf a⟩
  · exact ⟨a, h, hr a⟩

/-- A change of one group that grows it. -/
theorem grows_modGroup (T : Statement) (k : Nat) (f : Group → Group)
    (hf : ∀ G, GroupGrows G (f G)) : Grows T { T with groups := T.groups.modify k f } :=
  ⟨rfl, fun i G h => modify_rel GroupGrows GroupGrows.refl T.groups k f hf i G h,
    fun _ x h => ⟨x, h, OracleGrows.refl x⟩⟩

/-- A change of one oracle message that grows it. -/
theorem grows_modOracle (T : Statement) (k : Nat) (f : Oracle → Oracle)
    (hf : ∀ x, OracleGrows x (f x)) : Grows T { T with oracles := T.oracles.modify k f } :=
  ⟨rfl, fun _ G h => ⟨G, h, GroupGrows.refl G⟩,
    fun i x h => modify_rel OracleGrows OracleGrows.refl T.oracles k f hf i x h⟩

/-- Oracle messages that are sent. -/
theorem grows_stSent (T : Statement) (sent : Array OracleNotice) : Grows T (stSent T sent) := by
  refine ⟨rfl, fun _ G h => ⟨G, h, GroupGrows.refl G⟩, fun i x h => ⟨x, ?_, OracleGrows.refl x⟩⟩
  obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.1 h
  rw [stSent_old T sent i hi, h]

/-- One more group. -/
theorem grows_withGroup (T : Statement) (code maskCode : Nat) :
    Grows T (withGroup T code maskCode) := by
  refine ⟨rfl, fun i G h => ⟨G, ?_, GroupGrows.refl G⟩, fun _ x h => ⟨x, h, OracleGrows.refl x⟩⟩
  obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.1 h
  show (T.groups.push _)[i]? = some G
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hi), h]

/-- An oracle message that is admitted. -/
theorem grows_admitted (T : Statement) (o : Nat) (s : OracleShape) (p : List PadPlace)
    (rows : Array Row) : Grows T (admitted T o s p rows) :=
  grows_modOracle T o (fun x => { x with
      sampled := true, sampleRows := rows, pad := p.map fun q => (q.part, q.index),
      ledger := freshLedger T.codes s }) fun _ => ⟨rfl, fun _ => rfl, fun _ h => h⟩

/-- What was in an array is in it behind an insertion. -/
theorem mem_insertIfIn {α : Type} (xs : Array α) (i : Nat) (a b : α) (h : b ∈ xs) :
    b ∈ xs.insertIdxIfInBounds i a := by
  unfold Array.insertIdxIfInBounds
  split
  · exact Array.mem_insertIdx.2 (Or.inr h)
  · exact h

/-- An oracle message that joins a group. -/
theorem grows_joined (T : Statement) (g o : Nat) (kept : Bool) (G : Group) :
    Grows T (withMessageInGroup T g o kept G) :=
  (grows_modGroup T g (fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept })
    fun _ => ⟨rfl, rfl, id, fun _ h => mem_insertIfIn _ _ _ _ h⟩).trans
    (grows_modOracle _ o (fun x => { x with groups := x.groups ++ [g] })
      fun _ => ⟨rfl, id, fun _ h => List.mem_append_left _ h⟩)

/-- One more open row. -/
theorem grows_withRow (T : Statement) (g : Nat) (row : Row) : Grows T (withRow T g row) :=
  grows_modGroup T g (fun G => { G with rows := G.rows.push row })
    fun _ => ⟨rfl, rfl, id, fun _ h => h⟩

/-- Ledgers that are closed. -/
theorem grows_closeLedgers (l : List Nat) : ∀ T : Statement, Grows T (closeLedgers T l) := by
  induction l with
  | nil => exact Grows.refl
  | cons o l ih =>
    intro T
    exact (grows_modOracle T o
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      fun _ => ⟨rfl, id, fun _ h => h⟩).trans (ih _)

/-- The beginning of a proximity test. -/
theorem grows_begun (T : Statement) (g : Nat) (G : Group) : Grows T (begun T g G) :=
  (grows_closeLedgers G.members.toList T).trans
    (grows_modGroup _ g (fun G => { G with inRun := true, rows := #[] })
      fun _ => ⟨rfl, rfl, fun _ => rfl, fun _ h => h⟩)

end VerifiableInference.Desc
