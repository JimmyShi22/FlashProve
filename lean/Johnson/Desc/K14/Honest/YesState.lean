--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesState.lean: tools for saying that a function of the shared rounds
returns: the ground's small calls read forwards, where the places of a message's pad lie, and how
facts on a message are carried from one statement to the next.

Main names:
  newGroupP_of, joinP_of, takeMaskP_of   a new group, a joining and the taking of a mask entry
                      return where their named tests hold; the state behind is written out
  mapM_makes          a list is made item by item where each item can be made
  mem_entered         the members of a group behind a joining
  mem_pad_mask, mem_pad_main   the places of a message's pad, written out: in the last mask row, or
                      in the last main row of a message over the large field without mask rows
  pad_main_lt         a place of the pad in the main table lies inside the table
  Alike T T'          two statements with the same codes whose messages have the same shapes and
                      pads; Alike.has_eq, Alike.tableBits_eq; alike_mod, alike_joined, alike_withRow
  Sits.alike          Sits is carried along Alike
  sits_of_msg         **a message as a sending leaves it sits in a group of which it is a member**:
                      from "n entries fit in the message" (roomOf)
  mask_first          a message with mask rows and a free mask entry: its first entry lies in its
                      mask table and masks no answer

What is not claimed. That a message stands as a sending leaves it: that is a premise of sits_of_msg
and mask_first here, and is shown in Johnson/Desc/K14/Honest/YesSend.lean (send_left). Nothing on
what a message holds, on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesCut
import Johnson.Desc.K14.Law.Placed
import Johnson.Desc.Own.RoomPlaces
import Johnson.Desc.Key.Laid.JoinedDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Slice (withMessageInGroup withRow)
open VerifiableInference.Desc.Ground (newGroupP newGroupL groupL groupOk withGroup joinP joinL
  takeMaskP takeMaskL ok)
open VerifiableInference.Desc.Key (entered)
open Desc.K14.Law (tableBits_main le_two_pow_ceilLog2)

/-! ## The ground's small calls, read forwards -/

/-- A new group: where both codes are there and the mask code is not longer. -/
theorem newGroupP_of {L : Type} (d : DState L) (c z : Nat) (h : groupOk d.st.codes c z = true) :
    newGroupP d c z = some (d.st.groups.size, { d with st := withGroup d.st c z }) := by
  have hok : ok (newGroupL d.st c z) = true := by
    unfold groupOk at h
    cases hb : d.st.codes.base[c]? with
    | none =>
      rw [hb] at h
      simp at h
    | some cc =>
      cases hm : d.st.codes.mask[z]? with
      | none =>
        rw [hb, hm] at h
        simp at h
      | some zz =>
        rw [hb, hm] at h
        simp only [ok, newGroupL, groupL, List.all_cons, List.all_nil, Bool.and_true,
          Bool.and_eq_true]
        rw [hb, hm]
        exact ⟨rfl, rfl, h⟩
  unfold newGroupP
  rw [if_pos hok]

/-- A message joins a group, not as a kept member. -/
theorem joinP_of {L : Type} (d : DState L) (g o : Nat) (G : Group) (x : Oracle)
    (hG : d.st.groups[g]? = some G) (hx : d.st.oracles[o]? = some x) (h1 : x.sampled = true)
    (h2 : G.inRun = false) (h3 : x.shape.mainRows = 0 ∨ x.shape.code = G.code)
    (h4 : x.shape.maskRows = 0 ∨ x.shape.maskCode = G.maskCode)
    (h5 : G.members.contains o = false) :
    joinP d g o false = some { d with st := withMessageInGroup d.st g o false G } := by
  have hok : ok (joinL d.st g o false) = true := by
    simp only [ok, joinL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    rw [hG, hx]
    refine ⟨rfl, rfl, h1, ?_, ?_, ?_, ?_, rfl⟩
    · show (!G.inRun) = true
      rw [h2]
      rfl
    · show (x.shape.mainRows == 0 || x.shape.code == G.code) = true
      rcases h3 with h | h <;> simp [h]
    · show (x.shape.maskRows == 0 || x.shape.maskCode == G.maskCode) = true
      rcases h4 with h | h <;> simp [h]
    · show (!G.members.contains o) = true
      rw [h5]
      rfl
  unfold joinP
  rw [if_pos hok, hG]
  rfl

/-- The next free mask entry is taken. -/
theorem takeMaskP_of {L : Type} (d : DState L) (o : Nat) (x : Oracle) (l : Ledger)
    (hx : d.st.oracles[o]? = some x) (hl : x.ledger = some l) (hc : l.closed = false)
    (hleft : 0 < l.left) :
    takeMaskP d o = some (Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next,
      { d with st := { d.st with oracles := d.st.oracles.modify o fun x =>
        { x with ledger := some { l with
          next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1,
          left := l.left - 1 } } } }) := by
  have hb : (d.st.oracles[o]?).bind (·.ledger) = some l := by
    rw [hx]
    exact hl
  have hok : ok (takeMaskL d.st o) = true := by
    simp only [ok, takeMaskL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    rw [hb, hx]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · show x.ledger.isSome = true
      rw [hl]
      rfl
    · show (!l.closed) = true
      rw [hc]
      rfl
    · show decide (0 < l.left) = true
      exact decide_eq_true hleft
  unfold takeMaskP
  rw [if_pos hok, hb]
  rfl

/-- A list is made item by item where each item can be made. -/
theorem mapM_makes {α β : Type} (f : α → Option β) : ∀ l : List α,
    (∀ a ∈ l, ∃ b, f a = some b) → ∃ out, l.mapM f = some out
  | [], _ => ⟨[], by simp⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨bs, hbs⟩ := mapM_makes f l fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨b :: bs, ?_⟩
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq]
    exact ⟨b, hb, bs, hbs, rfl⟩

/-- The members of a group behind a joining: the new one and the old ones. -/
theorem mem_entered (G : Group) (o : Nat) (k : Bool) (a : Nat) :
    a ∈ (entered G o k).members ↔ a = o ∨ a ∈ G.members := by
  have hle : (G.members.filter (· < o)).size ≤ G.members.size := Array.size_filter_le
  show a ∈ G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o ↔ _
  unfold Array.insertIdxIfInBounds
  split
  · exact Array.mem_insertIdx
  · rename_i hn
    exact absurd hle hn

/-! ## Where the places of a pad lie -/

/-- The pad of a message with mask rows lies at the end of its last mask row. -/
theorem mem_pad_mask (codes : Codes) (s : OracleShape) (places : List PadPlace)
    (hk : 0 < s.maskRows) (h : Send.pad codes s = some places) (p : PadPlace) (hp : p ∈ places) :
    p.part = Part.mask ∧ ∃ i, i < s.answers ∧
      s.answers ≤ (codes.mask.getD s.maskCode default).ell ∧
      p.index = (s.maskRows - 1) +
        ((codes.mask.getD s.maskCode default).ell - s.answers + i) * 2 ^ ceilLog2 s.maskRows := by
  have hc : (Send.cube codes s).hasMask = true := by simp [Send.cube, hk]
  have hb : (Send.cube codes s).maskRowBits = ceilLog2 s.maskRows := by simp [Send.cube, hk]
  unfold Send.pad at h
  simp only [hc, hb, Bool.true_or, ↓reduceIte, Nat.one_mul] at h
  split at h
  · cases h
  · rename_i hlen
    obtain rfl := Option.some.inj h
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, t, ht, rfl⟩ := hp
    have t0 : t = 0 := by omega
    subst t0
    exact ⟨rfl, i, hi, by omega, rfl⟩

/-- The pad of a message over the large field without mask rows lies at the end of its last main
row. -/
theorem mem_pad_main (codes : Codes) (s : OracleShape) (places : List PadPlace)
    (hk : s.maskRows = 0) (h0 : 0 < s.mainRows) (hdeg : s.mainDeg = 3)
    (h : Send.pad codes s = some places) (p : PadPlace) (hp : p ∈ places) :
    ∃ i, i < s.answers ∧ s.answers ≤ (codes.base.getD s.code default).ell ∧
      p.index = (s.mainRows - 1) +
        ((codes.base.getD s.code default).ell - s.answers + i) * 2 ^ ceilLog2 s.mainRows := by
  have hc : (Send.cube codes s).hasMask = false := by simp [Send.cube, hk]
  have hb : (Send.cube codes s).mainRowBits = ceilLog2 s.mainRows := by simp [Send.cube, h0]
  unfold Send.pad at h
  simp only [hc, hb, hdeg, Bool.false_or, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
    Nat.one_mul] at h
  split at h
  · cases h
  · rename_i hlen
    obtain rfl := Option.some.inj h
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, t, ht, rfl⟩ := hp
    have t0 : t = 0 := by omega
    subst t0
    exact ⟨i, hi, by omega, rfl⟩

/-- A place of the pad in the main table lies inside the table. -/
theorem pad_main_lt (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (places : List PadPlace)
    (h0 : 0 < s.mainRows) (hdeg : s.mainDeg = 3) (h : Send.pad codes s = some places)
    (p : PadPlace) (hp : p ∈ places) (hm : p.part = Part.main) :
    p.index < 2 ^ (vectorLay codes s rowsHigh).bits := by
  by_cases hk : 0 < s.maskRows
  · have := (mem_pad_mask codes s places hk h p hp).1
    rw [hm] at this
    cases this
  · obtain ⟨i, hi, hle, e⟩ := mem_pad_main codes s places (by omega) h0 hdeg h p hp
    rw [e]
    show _ < 2 ^ (ceilLog2 s.mainRows + ceilLog2 (codes.base.getD s.code default).ell)
    have h2 : (codes.base.getD s.code default).ell - s.answers + i + 1 ≤
        2 ^ ceilLog2 (codes.base.getD s.code default).ell :=
      Nat.le_trans (by omega) (le_two_pow_ceilLog2 _)
    have h3 := Nat.mul_le_mul_right (2 ^ ceilLog2 s.mainRows) h2
    rw [Nat.succ_mul] at h3
    have h4 := le_two_pow_ceilLog2 s.mainRows
    rw [Nat.pow_add, Nat.mul_comm (2 ^ ceilLog2 s.mainRows)]
    omega

/-! ## Statements that are alike -/

/-- Two statements with the same codes whose messages have the same shapes and pads. -/
structure Alike (T T' : Statement) : Prop where
  codes : T'.codes = T.codes
  there : ∀ (o : Nat) (x' : Oracle), T'.oracles[o]? = some x' →
    ∃ x, T.oracles[o]? = some x ∧ x'.shape = x.shape ∧ x'.pad = x.pad
  lacks : ∀ o : Nat, T'.oracles[o]? = none → T.oracles[o]? = none

/-- Statements that are alike have the same tables. -/
theorem Alike.has_eq {T T' : Statement} (h : Alike T T') (o : Nat) (p : Part) :
    T'.has o p = T.has o p := by
  cases hx : T'.oracles[o]? with
  | none => simp [Statement.has, hx, h.lacks o hx]
  | some x' =>
    obtain ⟨x, e, s, _⟩ := h.there o x' hx
    simp [Statement.has, hx, e, s]

/-- Their tables have the same numbers of index bits. -/
theorem Alike.tableBits_eq {T T' : Statement} (h : Alike T T') (o : Nat) (p : Part) :
    T'.tableBits o p = T.tableBits o p := by
  cases hx : T'.oracles[o]? with
  | none =>
    simp [Statement.tableBits, Statement.rowBits, Statement.placeBits, hx, h.lacks o hx]
  | some x' =>
    obtain ⟨x, e, s, _⟩ := h.there o x' hx
    simp [Statement.tableBits, Statement.rowBits, Statement.placeBits, hx, e, s, h.codes]

/-- A statement is like itself. -/
theorem Alike.refl (T : Statement) : Alike T T :=
  ⟨rfl, fun _ x' h => ⟨x', h, rfl, rfl⟩, fun _ h => h⟩

/-- Alike goes on. -/
theorem Alike.trans {A B C : Statement} (h : Alike A B) (k : Alike B C) : Alike A C :=
  ⟨k.codes.trans h.codes, fun o x'' hx => by
    obtain ⟨x', e1, s1, p1⟩ := k.there o x'' hx
    obtain ⟨x, e2, s2, p2⟩ := h.there o x' e1
    exact ⟨x, e2, s1.trans s2, p1.trans p2⟩, fun o hx => h.lacks o (k.lacks o hx)⟩

/-- Other groups, and one message turned in a way that leaves its shape and pad. -/
theorem alike_mod (T : Statement) (Gs : Array Group) (o : Nat) (f : Oracle → Oracle)
    (hf : ∀ x, (f x).shape = x.shape ∧ (f x).pad = x.pad) :
    Alike T { T with groups := Gs, oracles := T.oracles.modify o f } := by
  refine ⟨rfl, fun o' x' hx => ?_, fun o' hx => ?_⟩
  · have hx' : (T.oracles.modify o f)[o']? = some x' := hx
    rw [Array.getElem?_modify] at hx'
    split at hx'
    · obtain ⟨x, e, rfl⟩ := Option.map_eq_some_iff.1 hx'
      exact ⟨x, e, (hf x).1, (hf x).2⟩
    · exact ⟨x', hx', rfl, rfl⟩
  · have hx' : (T.oracles.modify o f)[o']? = none := hx
    rw [Array.getElem?_modify] at hx'
    split at hx'
    · simpa using hx'
    · exact hx'

/-- A joining leaves the statement alike. -/
theorem alike_joined (T : Statement) (g o : Nat) (k : Bool) (G : Group) :
    Alike T (withMessageInGroup T g o k G) :=
  alike_mod T _ o _ fun _ => ⟨rfl, rfl⟩

/-- A further row leaves the statement alike. -/
theorem alike_withRow (T : Statement) (g : Nat) (r : Row) : Alike T (withRow T g r) :=
  ⟨rfl, fun _ x' h => ⟨x', h, rfl, rfl⟩, fun _ h => h⟩

/-- Sits is carried along Alike, to any group that has the message as a member. -/
theorem Sits.alike {T T' : Statement} {G : Group} {o : Nat} {lay : VectorLay} {n : Nat}
    (h : Sits T G o lay n) (a : Alike T T') (G' : Group) (hm : G'.members.contains o = true) :
    Sits T' G' o lay n :=
  ⟨hm, by rw [a.has_eq]; exact h.table, by rw [a.tableBits_eq]; exact h.bits, h.small,
    fun x' hx' q hq e => by
      obtain ⟨x, e1, _, e2⟩ := a.there o x' hx'
      exact h.pad x e1 q (e2 ▸ hq) e⟩

/-! ## A message as a sending leaves it -/

/-- **A message as a sending leaves it sits in a group of which it is a member.** n: entries that
fit in the message. -/
theorem sits_of_msg (T : Statement) (G : Group) (o : Nat) (x : Oracle) (s : OracleShape)
    (rowsHigh : Bool) (n : Nat) (hx : T.oracles[o]? = some x) (hs : x.shape = s)
    (hp : x.pad = ((Send.pad T.codes s).getD []).map fun p => (p.part, p.index))
    (hm : G.members.contains o = true) (h0 : 0 < s.mainRows) (hdeg : s.mainDeg = 3)
    (ha : s.answers ≠ 0) (h1 : 1 ≤ n)
    (hroom : n ≤ VerifiableInference.Desc.Own.roomOf T.codes s rowsHigh) :
    Sits T G o (vectorLay T.codes s rowsHigh) n := by
  obtain ⟨t1, t2⟩ := tableBits_main T o x hx (by rw [hs]; omega) rowsHigh
  rw [hs] at t2
  obtain ⟨r1, _, r3⟩ := (VerifiableInference.Desc.Own.le_roomOf T.codes s rowsHigh n h1).1 hroom
  obtain ⟨_, r5, r6⟩ := (VerifiableInference.Desc.Own.roomCan_iff T.codes s rowsHigh).1 r1
  refine ⟨hm, t1, t2, by omega, ?_⟩
  intro x' hx' q hq e
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  rw [hp] at hq
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hq
  have hsome : ∃ places, Send.pad T.codes s = some places := by
    rcases r6 with h | h
    · exact absurd h ha
    · exact Option.isSome_iff_exists.1 h
  obtain ⟨places, hpl⟩ := hsome
  rw [hpl] at hpm
  have hpm' : p ∈ places := hpm
  refine ⟨pad_main_lt T.codes s rowsHigh places h0 hdeg hpl p hpm' e, r3 p ?_ e⟩
  have hb : (s.answers == 0) = false := by simpa using ha
  rw [hb]
  show p ∈ (Send.pad T.codes s).getD []
  rw [hpl]
  exact hpm'

/-- A message of mask rows with a free mask entry: its first entry lies in its mask table and masks
no answer. -/
theorem mask_first (T : Statement) (o : Nat) (x : Oracle) (s : OracleShape)
    (hx : T.oracles[o]? = some x) (hs : x.shape = s)
    (hp : x.pad = ((Send.pad T.codes s).getD []).map fun p => (p.part, p.index))
    (hfree : 0 < Send.freeMaskEntries s.maskRows (T.codes.mask.getD s.maskCode default).ell
      s.answers) :
    T.has o .mask = true ∧ (Part.mask, 0) ∉ x.pad := by
  have hk : 0 < s.maskRows := by
    unfold Send.freeMaskEntries at hfree
    by_contra hn
    have : s.maskRows = 0 := by omega
    simp [this] at hfree
  constructor
  · simp [Statement.has, hx, hs, OracleShape.rows, hk]
  · intro hq
    rw [hp] at hq
    obtain ⟨p, hpm, e⟩ := List.mem_map.1 hq
    cases hpl : Send.pad T.codes s with
    | none =>
      rw [hpl] at hpm
      simp at hpm
    | some places =>
      rw [hpl] at hpm
      obtain ⟨_, i, _, hle, e2⟩ := mem_pad_mask T.codes s places hk hpl p hpm
      have e3 : p.index = 0 := congrArg Prod.snd e
      rw [e3] at e2
      have hpos : 0 < 2 ^ ceilLog2 s.maskRows := Nat.two_pow_pos _
      have z1 : s.maskRows - 1 = 0 := by omega
      have z2 : ((T.codes.mask.getD s.maskCode default).ell - s.answers + i) *
          2 ^ ceilLog2 s.maskRows = 0 := by omega
      have z3 : (T.codes.mask.getD s.maskCode default).ell - s.answers + i = 0 := by
        rcases Nat.mul_eq_zero.1 z2 with h | h
        · exact h
        · omega
      unfold Send.freeMaskEntries at hfree
      split at hfree
      · omega
      · have z4 : (T.codes.mask.getD s.maskCode default).ell - s.answers = 0 := by omega
        rw [z4, z1] at hfree
        simp at hfree

end Desc.K14.Honest

#print axioms Desc.K14.Honest.newGroupP_of
#print axioms Desc.K14.Honest.joinP_of
#print axioms Desc.K14.Honest.takeMaskP_of
#print axioms Desc.K14.Honest.mapM_makes
#print axioms Desc.K14.Honest.mem_entered
#print axioms Desc.K14.Honest.mem_pad_mask
#print axioms Desc.K14.Honest.mem_pad_main
#print axioms Desc.K14.Honest.pad_main_lt
#print axioms Desc.K14.Honest.Alike.has_eq
#print axioms Desc.K14.Honest.Alike.tableBits_eq
#print axioms Desc.K14.Honest.Alike.refl
#print axioms Desc.K14.Honest.Alike.trans
#print axioms Desc.K14.Honest.alike_mod
#print axioms Desc.K14.Honest.alike_joined
#print axioms Desc.K14.Honest.alike_withRow
#print axioms Desc.K14.Honest.Sits.alike
#print axioms Desc.K14.Honest.sits_of_msg
#print axioms Desc.K14.Honest.mask_first
