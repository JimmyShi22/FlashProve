-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxEarlierMessagesAndGroups.lean: what a change of the statement leaves of its older oracle messages
and groups.

A proximity test (OnBytes/Iop/Prox.lean: ioppVerify) enters new oracle messages and new groups into
the statement and changes them. Of what was there before it changes little. This file has the
relation that says so, for statements, and shows it of each function by which the files on the
program's calls describe a changed statement (stSent, admitted, withMessageInGroup, withRow, withRows,
withGroup, closeLedgers, ledgerShut, begun).

Main definitions.
  SameOracle   an oracle message is as it was, but perhaps for the mark that it was spent as a mask.
  Old          a statement has the codes of another; each oracle message with a number below n0 is
               as it was (SameOracle); each group with a number below g0 is as it was; no oracle
               message or group has gone.
  shut         an oracle message with its ledger closed.
Main theorems.
  Old.refl, Old.trans, Old.of_get   the relation is reflexive and transitive; it holds if the
               older entries are equal.
  closeLedgers_get   what closing the ledgers of a list of oracle messages does to each.
  old_stSent, old_admitted, old_joined, old_withRows, old_withGroup, old_closeLedgers,
  old_ledgerShut, old_begun, old_spent   the relation, of each function.

Not claimed. Nothing on the new oracle messages and groups. Nothing on a run of the program.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkCsRun

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun

/-- The oracle message x' is x, but perhaps for the mark that it was spent as a mask: if sp is
false, that mark is kept too. -/
structure SameOracle (sp : Prop) (x x' : Oracle) : Prop where
  /-- the shape -/
  shape : x'.shape = x.shape
  /-- whether it is sampled -/
  sampled : x'.sampled = x.sampled
  /-- the sample rows -/
  sampleRows : x'.sampleRows = x.sampleRows
  /-- the entries that mask the answers -/
  pad : x'.pad = x.pad
  /-- the groups that it belongs to -/
  groups : x'.groups = x.groups
  /-- the free mask entries -/
  ledger : x'.ledger = x.ledger
  /-- the mark that it was spent as a mask -/
  spent : ¬ sp → x'.spentAsMask = x.spentAsMask

/-- An oracle message is as it is. -/
theorem SameOracle.refl (sp : Prop) (x : Oracle) : SameOracle sp x x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- The relation goes through an oracle message between. -/
theorem SameOracle.trans {sp : Prop} {x y z : Oracle} (h1 : SameOracle sp x y)
    (h2 : SameOracle sp y z) : SameOracle sp x z :=
  ⟨h2.shape.trans h1.shape, h2.sampled.trans h1.sampled, h2.sampleRows.trans h1.sampleRows,
    h2.pad.trans h1.pad, h2.groups.trans h1.groups, h2.ledger.trans h1.ledger,
    fun h => (h2.spent h).trans (h1.spent h)⟩

/-- What the statement S' keeps of the statement S. n0, g0: the oracle messages and groups with
lower numbers are meant. sp: the oracle messages that may have been spent as masks. -/
structure Old (n0 g0 : Nat) (sp : Nat → Prop) (S S' : Statement) : Prop where
  /-- the codes -/
  codes : S'.codes = S.codes
  /-- each older oracle message -/
  oracle : ∀ o x, o < n0 → S.oracles[o]? = some x →
    ∃ x', S'.oracles[o]? = some x' ∧ SameOracle (sp o) x x'
  /-- each older group -/
  group : ∀ g, g < g0 → S'.groups[g]? = S.groups[g]?
  /-- no oracle message has gone -/
  osize : S.oracles.size ≤ S'.oracles.size
  /-- no group has gone -/
  gsize : S.groups.size ≤ S'.groups.size

/-- A statement keeps what is its own. -/
theorem Old.refl (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) : Old n0 g0 sp S S :=
  ⟨rfl, fun _ x _ h => ⟨x, h, SameOracle.refl _ x⟩, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- The relation goes through a statement between. -/
theorem Old.trans {n0 g0 : Nat} {sp : Nat → Prop} {A B C : Statement} (h1 : Old n0 g0 sp A B)
    (h2 : Old n0 g0 sp B C) : Old n0 g0 sp A C :=
  ⟨h2.codes.trans h1.codes, fun o x ho hx => by
    obtain ⟨y, hy, e1⟩ := h1.oracle o x ho hx
    obtain ⟨z, hz, e2⟩ := h2.oracle o y ho hy
    exact ⟨z, hz, e1.trans e2⟩, fun g hg => (h2.group g hg).trans (h1.group g hg),
    h1.osize.trans h2.osize, h1.gsize.trans h2.gsize⟩

/-- The relation holds if the codes and the older entries are equal and nothing has gone. -/
theorem Old.of_get {n0 g0 : Nat} {sp : Nat → Prop} {S S' : Statement} (hc : S'.codes = S.codes)
    (ho : ∀ o, o < n0 → S'.oracles[o]? = S.oracles[o]?)
    (hg : ∀ g, g < g0 → S'.groups[g]? = S.groups[g]?) (h1 : S.oracles.size ≤ S'.oracles.size)
    (h2 : S.groups.size ≤ S'.groups.size) : Old n0 g0 sp S S' :=
  ⟨hc, fun o x h hx => ⟨x, (ho o h).trans hx, SameOracle.refl _ x⟩, hg, h1, h2⟩

/-! ## The functions that describe a changed statement -/

/-- New oracle messages at the end. -/
theorem old_stSent (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (sent : Array OracleNotice)
    (hn : n0 ≤ S.oracles.size) : Old n0 g0 sp S (stSent S sent) :=
  Old.of_get rfl (fun o h => Array.getElem?_append_left (Nat.lt_of_lt_of_le h hn))
    (fun _ _ => rfl) (by simp [stSent]) (Nat.le_refl _)

/-- A change of one oracle message that is not among the older ones. -/
theorem old_modify (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (o : Nat) (f : Oracle → Oracle)
    (hn : n0 ≤ o) : Old n0 g0 sp S { S with oracles := S.oracles.modify o f } :=
  Old.of_get rfl (fun o' h => by
    have hne : o ≠ o' := by omega
    simp [Array.getElem?_modify, hne]) (fun _ _ => rfl) (by simp) (Nat.le_refl _)

/-- A change of one group that is not among the older ones. -/
theorem old_modifyGroup (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (g : Nat)
    (f : Group → Group) (hg : g0 ≤ g) : Old n0 g0 sp S { S with groups := S.groups.modify g f } :=
  Old.of_get rfl (fun _ _ => rfl) (fun g' h => by
    have hne : g ≠ g' := by omega
    simp [Array.getElem?_modify, hne]) (Nat.le_refl _) (by simp)

/-- The sample rows of a new oracle message are entered. -/
theorem old_admitted (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (o : Nat) (s : OracleShape)
    (p : List PadPlace) (rows : Array Row) (hn : n0 ≤ o) :
    Old n0 g0 sp S (admitted S o s p rows) := old_modify n0 g0 sp S o _ hn

/-- A new oracle message joins a new group. -/
theorem old_joined (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (g o : Nat) (k : Bool)
    (G : Group) (hn : n0 ≤ o) (hg : g0 ≤ g) : Old n0 g0 sp S (withMessageInGroup S g o k G) :=
  Old.of_get rfl (fun o' h => by
    have hne : o ≠ o' := by omega
    simp [withMessageInGroup, Array.getElem?_modify, hne]) (fun g' h => by
                have hne : g ≠ g' := by omega
                simp [withMessageInGroup, Array.getElem?_modify, hne]) (by simp [withMessageInGroup]) (by simp [withMessageInGroup])

/-- A new open row of a new group. -/
theorem old_withRow (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (g : Nat) (r : Row)
    (hg : g0 ≤ g) : Old n0 g0 sp S (withRow S g r) := old_modifyGroup n0 g0 sp S g _ hg

/-- New open rows of a new group. -/
theorem old_withRows (n0 g0 : Nat) (sp : Nat → Prop) (g : Nat) (hg : g0 ≤ g) :
    ∀ (l : List Row) (S : Statement), Old n0 g0 sp S (withRows S g l)
  | [], S => Old.refl n0 g0 sp S
  | r :: l, S => (old_withRow n0 g0 sp S g r hg).trans (old_withRows n0 g0 sp g hg l _)

/-- A new group at the end. -/
theorem old_withGroup (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (a b : Nat)
    (hg : g0 ≤ S.groups.size) : Old n0 g0 sp S (withGroup S a b) :=
  Old.of_get rfl (fun _ _ => rfl)
    (fun g h => Array.getElem?_push_lt (Nat.lt_of_lt_of_le h hg) |>.trans (by simp))
    (Nat.le_refl _) (by simp [withGroup])

/-- An oracle message is marked as spent: an older one that may be, or a new one. -/
theorem old_spent (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (o : Nat)
    (h : sp o ∨ n0 ≤ o) :
    Old n0 g0 sp S
      { S with oracles := S.oracles.modify o fun x => { x with spentAsMask := true } } := by
  refine ⟨rfl, fun o' x _ hx => ?_, fun _ _ => rfl, by simp, Nat.le_refl _⟩
  by_cases e : o = o'
  · subst e
    refine ⟨{ x with spentAsMask := true }, by simp [Array.getElem?_modify, hx], rfl, rfl, rfl, rfl,
      rfl, rfl, fun hs => ?_⟩
    rcases h with h | h
    · exact absurd h hs
    · omega
  · exact ⟨x, by simp [Array.getElem?_modify, e, hx], SameOracle.refl _ x⟩

/-! ## Closing ledgers -/

/-- The oracle message with its ledger closed, if it has one. -/
def shut (x : Oracle) : Oracle :=
  { x with ledger := x.ledger.map fun l => { l with closed := true } }

/-- Closing a closed ledger changes nothing. -/
theorem shut_shut (x : Oracle) : shut (shut x) = shut x := by
  unfold shut
  cases x.ledger <;> rfl

/-- Closing ledgers leaves the groups as they were. -/
theorem closeLedgers_groups : ∀ (l : List Nat) (S : Statement),
    (closeLedgers S l).groups = S.groups
  | [], _ => rfl
  | _ :: l, _ => closeLedgers_groups l _

/-- Closing ledgers leaves the number of oracle messages as it was. -/
theorem closeLedgers_size : ∀ (l : List Nat) (S : Statement),
    (closeLedgers S l).oracles.size = S.oracles.size
  | [], _ => rfl
  | _ :: l, _ => (closeLedgers_size l _).trans (by simp)

/-- What closing the ledgers of the listed oracle messages does to the oracle message number o. -/
theorem closeLedgers_get : ∀ (l : List Nat) (S : Statement) (o : Nat),
    (closeLedgers S l).oracles[o]? = (S.oracles[o]?).map fun x => if o ∈ l then shut x else x
  | [], S, o => by simp [closeLedgers]
  | a :: l, S, o => by
    have ih := closeLedgers_get l { S with oracles := S.oracles.modify a shut } o
    have e : closeLedgers S (a :: l) =
        closeLedgers { S with oracles := S.oracles.modify a shut } l := rfl
    rw [e, ih]
    by_cases h : a = o
    · subst h
      cases hx : S.oracles[a]? with
      | none => simp [Array.getElem?_modify, hx]
      | some x =>
        by_cases hl : a ∈ l <;> simp [Array.getElem?_modify, hx, hl, shut_shut]
    · have h' : o ≠ a := fun e => h e.symm
      simp [Array.getElem?_modify, h, h']

/-- Closing the ledgers of new oracle messages. -/
theorem old_closeLedgers (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (l : List Nat)
    (hl : ∀ o ∈ l, n0 ≤ o) : Old n0 g0 sp S (closeLedgers S l) :=
  Old.of_get (closeLedgers_codes l S) (fun o h => by
    have hn : o ∉ l := fun hm => absurd (hl o hm) (by omega)
    rw [closeLedgers_get]
    simp [hn]) (fun _ _ => by rw [closeLedgers_groups]) (by rw [closeLedgers_size])
    (by rw [closeLedgers_groups])

/-- The ledger of a switch's new oracle message is closed. -/
theorem old_ledgerShut (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (T : SwitchTarget)
    (o : Nat) (hn : n0 ≤ o) : Old n0 g0 sp S (ledgerShut S T o) := by
  unfold ledgerShut
  split
  · exact old_closeLedgers n0 g0 sp S [o] fun a ha => by
      rw [List.mem_singleton.1 ha]
      exact hn
  · exact Old.refl n0 g0 sp S

/-- The test on a new group of new oracle messages begins. -/
theorem old_begun (n0 g0 : Nat) (sp : Nat → Prop) (S : Statement) (g : Nat) (G : Group)
    (hl : ∀ o ∈ G.members.toList, n0 ≤ o) (hg : g0 ≤ g) : Old n0 g0 sp S (begun S g G) :=
  (old_closeLedgers n0 g0 sp S _ hl).trans (old_modifyGroup n0 g0 sp _ g _ hg)

end OnBytes.Slice.ProxRun
