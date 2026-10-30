-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/SeatLaws.lean: the caller that a seat makes (OnBytes/G4/Seat.lean), what is asked of the
seat, and that a good seat's caller meets the laws of OnBytes/G4/AnyCaller.lean.

`Seat.SlotFine s`: the mask entry s lies in a mask table of a member of the group, and is no entry
that masks an answer to a sample. `Seat.RowFine row`: what Lkp.leave and Blk.addRow test of a row,
said at the base's statement: the row is plain, has no run and no form; its structured vectors are
in order, fit their tables and read main tables only of messages that the public inputs declare; its
single entries are mask entries that fit; its coefficient on every entry that masks an answer to a
sample is 0. The first ledger counts as having entries left only if it is open and all entries that
it can still give are SlotFine (`Seat.ledB`, a fact that can be evaluated); else as having none. The
second counts if it is open: its entries go into no row of the group.
`Seat.Good`: the two messages differ; they and the messages that are read are there and sampled; the
group is there and its proximity test has not begun; and adding a vector of product form on the bits
by planesAt keeps a row fine. The last is a statement for all rows and vectors; the others are facts
on the base.

Main definitions: Seat.groupOf, Seat.padsOf, Seat.SlotFine, Seat.RowFine, Seat.ledB, Seat.caller,
Seat.Good.
Main theorems: Seat.leave, Seat.laws, Seat.ctx_self.
Not claimed. That a given context of the program is good.


-/
import OnBytes.G4.Seat

set_option autoImplicit false

namespace OnBytes.G4

open Blk

namespace Seat

/-- The group of the base's statement. -/
def groupOf (Z : Seat) : Group := (Z.base.st.groups[Z.group]?).getD default

/-- The entries of message o that mask the answers to a sample. -/
def padsOf (Z : Seat) (o : Nat) : List (Part × Nat) := ((Z.base.st.oracles[o]?).map Oracle.pad).getD
    []

/-- A mask entry that a row of the group may read, as a test. -/
def slotB (Z : Seat) (s : Slot) : Bool :=
  placeOk Z.base.st Z.groupOf s.oracle .mask (Z.base.st.tableBits s.oracle .mask) s.index &&
  Z.groupOf.members.all fun o => (Z.padsOf o).all fun p =>
    !(s.oracle == o && Part.mask == p.1 && s.index == p.2)

/-- A mask entry that a row of the group may read. -/
def SlotFine (Z : Seat) (s : Slot) : Prop := Z.slotB s = true

/-- A row that the group takes through the lookup's door. -/
structure RowFine (Z : Seat) (row : Row) : Prop where
  kind : row.kind = .plain
  runs : row.runs = #[]
  forms : row.forms = #[]
  terms : ∀ t ∈ row.terms, t.v.ok = true ∧
    placeOk Z.base.st Z.groupOf t.oracle t.part t.v.vars 0 = true ∧
    (t.part != .main || Z.S.readFrom.contains t.oracle) = true
  units : ∀ u ∈ row.units, u.part = .mask ∧
    placeOk Z.base.st Z.groupOf u.oracle u.part (Z.base.st.tableBits u.oracle u.part) u.index = true
  pads : ∀ o ∈ Z.groupOf.members, ∀ p ∈ Z.padsOf o, isZeroE (row.coefficient o p.1 p.2) = true

/-- The ledger of message o is open, and all entries that it can still give may be read by a row. -/
def ledB (Z : Seat) (o : Nat) (l : Ledger) : Bool :=
  !l.closed && (takesOf l l.left).1.all fun i => Z.slotB ⟨o, i⟩

/-- The caller that a seat makes. -/
def caller (Z : Seat) : Caller where
  S := Z.S
  planesAt := Z.planesAt
  masks := Z.masks
  keyMasks := Z.keyMasks
  group := Z.group
  Led := Ledger × Ledger
  ctx := Z.ctx
  take := fun σ n => (slotsAt Z.masks (takesOf σ.1 n).1, ((takesOf σ.1 n).2, σ.2))
  takeKey := fun σ n => (slotsAt Z.keyMasks (takesOf σ.2 n).1, (σ.1, (takesOf σ.2 n).2))
  left := fun σ => if Z.ledB Z.masks σ.1 then σ.1.left else 0
  keyLeft := fun σ => if σ.2.closed then 0 else σ.2.left
  SlotOK := Z.SlotFine
  Fine := Z.RowFine

/-- What is asked of a seat. -/
structure Good (Z : Seat) : Prop where
  /-- the two messages that give mask entries differ -/
  apart : Z.masks ≠ Z.keyMasks
  /-- the messages that the lookup names are there and sampled -/
  sampled : ∀ o, (o = Z.masks ∨ o = Z.keyMasks ∨ o ∈ Z.S.readFrom) →
    ∃ x, Z.base.st.oracles[o]? = some x ∧ x.sampled = true
  /-- the group is there -/
  group : ∃ G, Z.base.st.groups[Z.group]? = some G
  /-- the group's proximity test has not begun -/
  open_ : Z.groupOf.inRun = false
  /-- adding a vector of product form on the bits keeps a row fine -/
  planes : ∀ (r : Row) (v : Tensor), Z.RowFine r → v.vars = Z.S.mu + Z.S.d → v.ok = true →
    v.denseVars = [] → Z.RowFine (Z.planesAt r v)

/-! ## The group -/

theorem groupAt (Z : Seat) (g : Z.Good) (σ rows) :
    (Z.st σ rows).groups[Z.group]? = some { Z.groupOf with rows := rows } := by
  obtain ⟨G, hG⟩ := g.group
  simp [st, Array.getElem?_modify, groupOf, hG]

theorem groups_push (Z : Seat) (σ rows) (row : Row) :
    ((Z.st σ rows).groups.modify Z.group fun G => { G with rows := G.rows.push row }) =
      (Z.st σ (rows.push row)).groups := by
  apply Array.ext_getElem?
  intro i
  simp only [st, Array.getElem?_modify]
  by_cases h1 : Z.group = i <;> cases Z.base.st.groups[i]? <;> simp_all

/-- A fine row goes into the group through the lookup's own door. -/
theorem leave (Z : Seat) (g : Z.Good) (es rs last σ rows) (row : Row) (h : Z.RowFine row) :
    (Lkp.leave Z.caller.env row) (Z.ctx es none rs last σ rows) =
      .ok ((), Z.ctx es none rs last σ (rows.push row)) := by
  have hd : ((row.terms.all fun t => t.part != .main || Z.caller.env.S.readFrom.contains t.oracle)
      &&
      (row.units.all fun t => t.part != .main || Z.caller.env.S.readFrom.contains t.oracle) &&
      (row.runs.all fun t => t.part != .main || Z.caller.env.S.readFrom.contains t.oracle) &&
      row.forms.all fun t => Z.caller.env.S.readFrom.contains t.oracle) = true := by
    simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro t ht
      exact (h.terms t ht).2.2
    · intro u hu
      simp [(h.units u hu).1]
    · intro x hx
      simp [h.runs] at hx
    · intro f hf
      simp [h.forms] at hf
  have h0 : Blk.statement (Z.ctx es none rs last σ rows) =
      .ok (Z.st σ rows, Z.ctx es none rs last σ rows) := rfl
  have h1 : (Blk.group Z.group) (Z.ctx es none rs last σ rows) =
      .ok ({ Z.groupOf with rows := rows }, Z.ctx es none rs last σ rows) := by
    show (Blk.get ((Z.st σ rows).groups[Z.group]?)) _ = _
    rw [groupAt Z g]
    rfl
  have h2 : Blk.isDry (Z.ctx es none rs last σ rows) = .ok (false, Z.ctx es none rs last σ rows) :=
      rfl
  have hT : (row.terms.all fun t => t.v.ok &&
      placeOk (Z.st σ rows) { Z.groupOf with rows := rows } t.oracle t.part t.v.vars 0) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro t ht
    rw [placeOk_st, (h.terms t ht).1, (h.terms t ht).2.1]
    rfl
  have hU : (row.units.all fun u => placeOk (Z.st σ rows) { Z.groupOf with rows := rows } u.oracle
      u.part
      ((Z.st σ rows).tableBits u.oracle u.part) u.index) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro u hu
    rw [placeOk_st, tableBits_st]
    exact (h.units u hu).2
  have hP : (({ Z.groupOf with rows := rows } : Group).members.all fun o =>
      (((Z.st σ rows).oracles[o]?).map (·.pad)).getD [] |>.all fun p =>
        isZeroE (row.coefficient o p.1 p.2)) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro o ho
    have e : (((Z.st σ rows).oracles[o]?).map (·.pad)).getD [] = Z.padsOf o := pad_st Z σ rows o
    rw [e, List.all_eq_true]
    intro p hp
    exact h.pads o ho p hp
  have hsize : Z.group < (Z.ctx es none rs last σ rows).st.groups.size := by
    obtain ⟨G, hG⟩ := g.group
    have := (Array.getElem?_eq_some_iff.1 hG).1
    simpa [ctx, st] using this
  have hon : (Blk.onGroup Z.group fun G => { G with rows := G.rows.push row })
      (Z.ctx es none rs last σ rows) = .ok ((), Z.ctx es none rs last σ (rows.push row)) := by
    unfold Blk.onGroup
    rw [if_pos hsize]
    have e : ((Z.ctx es none rs last σ rows).st.groups.modify Z.group fun G =>
        { G with rows := G.rows.push row }) = (Z.st σ (rows.push row)).groups := groups_push Z σ
            rows row
    simp only [e]
    rfl
  show ((Blk.must _) >>= fun _ => Blk.addRow Z.group row) _ = _
  rw [bind_ok (must_ok hd _)]
  unfold Blk.addRow
  rw [bind_ok h0, bind_ok h1, bind_ok (must_ok (by simp [g.open_, h.kind]) _), bind_ok h2]
  simp only [Bool.false_eq_true, if_false]
  rw [bind_ok (pure_ok _ _), bind_ok (must_ok hT _), bind_ok (must_ok hU _),
    bind_ok (must_ok (by simp [h.runs]) _), bind_ok (must_ok (by simp [h.forms]) _),
    bind_ok (test_ok hP _)]
  exact hon

/-! ## Fine rows -/

theorem fineTarget (Z : Seat) (x : E) : Z.RowFine { target := x } :=
  { kind := rfl, runs := rfl, forms := rfl, terms := by simp, units := by simp
    pads := fun _ _ _ _ => rfl }

/-- A single entry elsewhere does not turn a row's coefficient on an entry. -/
theorem coefficient_addUnit_ne (r : Row) (o' : Nat) (part' : Part) (index' : Nat) (x : E) (o : Nat)
    (part : Part) (index : Nat) (h : ¬((o' = o ∧ part' = part) ∧ index' = index)) :
    (r.addUnit o' part' index' x).coefficient o part index = r.coefficient o part index := by
  simp [Row.coefficient, Row.addUnit, h]

theorem fineUnit (Z : Seat) (r : Row) (s : Slot) (x : E) (h : Z.RowFine r) (hs : Z.SlotFine s) :
    Z.RowFine (r.addUnit s.oracle .mask s.index x) := by
  unfold SlotFine slotB at hs
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, List.all_eq_true] at hs
  exact
    { kind := h.kind, runs := h.runs, forms := h.forms, terms := h.terms
      units := by
        intro u hu
        simp only [Row.addUnit, Array.mem_push] at hu
        rcases hu with hu | rfl
        · exact h.units u hu
        · exact ⟨rfl, hs.1⟩
      pads := by
        intro o ho p hp
        have hne := hs.2 o ho p hp
        rw [coefficient_addUnit_ne]
        · exact h.pads o ho p hp
        · intro hh
          simp [hh.1.1, hh.1.2, hh.2] at hne }

/-! ## The messages are sampled -/

theorem sampledAll (Z : Seat) (g : Z.Good) (es rs last σ rows) : ∀ (l : List Nat),
    (∀ o ∈ l, o = Z.masks ∨ o = Z.keyMasks ∨ o ∈ Z.S.readFrom) →
    (Lkp.mustBeSampled l) (Z.ctx es none rs last σ rows) = .ok ((), Z.ctx es none rs last σ rows)
  | [], _ => rfl
  | o :: l, h => by
    obtain ⟨x, hx, hs⟩ := g.sampled o (h o (by simp))
    have ho : (Blk.oracle o) (Z.ctx es none rs last σ rows) =
        .ok (Z.fix σ o x, Z.ctx es none rs last σ rows) := by
      show (Blk.get ((Z.st σ rows).oracles[o]?)) _ = _
      rw [oracleAt, hx]
      rfl
    show ((Blk.oracle o) >>= fun y => (Blk.must y.sampled) >>= fun _ => Lkp.mustBeSampled l) _ = _
    rw [bind_ok ho, bind_ok (must_ok (by rw [fix_sampled]; exact hs) _)]
    exact sampledAll Z g es rs last σ rows l (fun q hq => h q (by simp [hq]))

/-! ## The ledgers' counts -/

/-- After n takes of a ledger that counts, with n at most what is left, the ledger still counts. -/
theorem ledB_takes (Z : Seat) (o : Nat) (l : Ledger) (n : Nat) (h : Z.ledB o l = true)
    (hn : n ≤ l.left) : Z.ledB o (takesOf l n).2 = true ∧ ∀ i ∈ (takesOf l n).1, Z.slotB ⟨o, i⟩ =
        true := by
  unfold ledB at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  have hsplit := takesOf_add n (l.left - n) l
  rw [show n + (l.left - n) = l.left from by omega] at hsplit
  refine ⟨⟨by rw [takesOf_closed]; exact h.1, ?_⟩, ?_⟩
  · intro i hi
    rw [takesOf_left] at hi
    exact h.2 i (by rw [hsplit]; exact List.mem_append_right _ hi)
  · intro i hi
    exact h.2 i (by rw [hsplit]; exact List.mem_append_left _ hi)

theorem ledB_open (Z : Seat) (o : Nat) (l : Ledger) (h : Z.ledB o l = true) : l.closed = false := by
  unfold ledB at h
  simp only [Bool.and_eq_true] at h
  simpa using h.1

/-- A GOOD SEAT's CALLER MEETS THE LAWS. -/
theorem laws (Z : Seat) (g : Z.Good) : Z.caller.Laws where
  recv := Z.recv
  close := Z.close
  note := Z.note
  take := by
    intro es rs last σ rows n hn
    obtain ⟨x, hx, _⟩ := g.sampled Z.masks (Or.inl rfl)
    by_cases hb : Z.ledB Z.masks σ.1 = true
    · have hn' : n ≤ σ.1.left := by simpa [caller, hb] using hn
      exact takeSlots_first Z g.apart x hx es rs last rows n σ (ledB_open Z _ _ hb) hn'
    · have hn' : n = 0 := by simpa [caller, hb] using hn
      subst hn'
      rfl
  takeKey := by
    intro es rs last σ rows n hn
    obtain ⟨x, hx, _⟩ := g.sampled Z.keyMasks (Or.inr (Or.inl rfl))
    cases hb : σ.2.closed with
    | false =>
      have hn' : n ≤ σ.2.left := by simpa [caller, hb] using hn
      exact takeSlots_second Z x hx es rs last rows n σ hb hn'
    | true =>
      have hn' : n = 0 := by simpa [caller, hb] using hn
      subst hn'
      rfl
  takeLength := by intro σ n; simp [caller, slotsAt, takesOf_length]
  takeKeyLength := by intro σ n; simp [caller, slotsAt, takesOf_length]
  leftTake := by
    intro σ n hn
    by_cases hb : Z.ledB Z.masks σ.1 = true
    · have hn' : n ≤ σ.1.left := by simpa [caller, hb] using hn
      simp [caller, hb, (ledB_takes Z _ _ n hb hn').1, takesOf_left]
    · have hn' : n = 0 := by simpa [caller, hb] using hn
      subst hn'
      simp [caller, takesOf]
  keyLeftTake := by intro σ n; rfl
  leftTakeKey := by intro σ n; rfl
  keyLeftTakeKey := by
    intro σ n hn
    simp [caller, takesOf_closed, takesOf_left]
    cases σ.2.closed <;> simp
  takeOK := by
    intro σ n hn s hs
    by_cases hb : Z.ledB Z.masks σ.1 = true
    · have hn' : n ≤ σ.1.left := by simpa [caller, hb] using hn
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hs
      exact (ledB_takes Z _ _ n hb hn').2 i hi
    · have hn' : n = 0 := by simpa [caller, hb] using hn
      subst hn'
      simp [caller, slotsAt, takesOf] at hs
  leave := Z.leave g
  fineTarget := Z.fineTarget
  fineUnit := Z.fineUnit
  finePlanes := g.planes
  sampled := Z.sampledAll g

/-! ## A context of the program as a seat's context -/

/-- A context is its own seat's context, at its own moving parts, if it is no dry run, keeps no
intermediate values, and no block has asked for the last round's number of rows. -/
theorem ctx_self (Z : Seat) (y1 y2 : Oracle) (l1 l2 : Ledger) (G : Group)
    (h1 : Z.base.st.oracles[Z.masks]? = some y1) (hl1 : y1.ledger = some l1)
    (h2 : Z.base.st.oracles[Z.keyMasks]? = some y2) (hl2 : y2.ledger = some l2)
    (hG : Z.base.st.groups[Z.group]? = some G)
    (hdry : Z.base.ch.dry = false) (hnotes : Z.base.keepNotes = false)
    (hasked : Z.base.ch.askedRows = false) :
    Z.ctx Z.base.ch.entries Z.base.ch.cur Z.base.ch.left Z.base.ch.last (l1, l2) G.rows =
        Z.base := by
  have ho : ((Z.base.st.oracles.modify Z.masks fun x => { x with ledger := some l1 }).modify
      Z.keyMasks fun x => { x with ledger := some l2 }) = Z.base.st.oracles := by
    apply Array.ext_getElem?
    intro i
    simp only [Array.getElem?_modify]
    by_cases a : Z.keyMasks = i <;> by_cases b : Z.masks = i
    · subst a
      simp only [if_true, b]
      rw [h2]
      simp [← hl2]
    · subst a
      simp only [if_true, b, if_false]
      rw [h2]
      simp [← hl2]
    · subst b
      simp only [a, if_false, if_true]
      rw [h1]
      simp [← hl1]
    · simp [a, b]
  have hg : (Z.base.st.groups.modify Z.group fun H => { H with rows := G.rows }) =
      Z.base.st.groups := by
    apply Array.ext_getElem?
    intro i
    simp only [Array.getElem?_modify]
    by_cases a : Z.group = i
    · subst a
      simp [hG]
    · simp [a]
  unfold ctx st
  rw [ho, hg]
  obtain ⟨base, S, planesAt, masks, keyMasks, group⟩ := Z
  obtain ⟨ch, st, book, notes, keepNotes, failed⟩ := base
  obtain ⟨dry, firstTree, samples, entries, left, cur, opened, roots, last, askedRows, items,
      noted⟩ := ch
  simp only at hdry hnotes hasked
  subst hdry hnotes hasked
  rfl

end Seat

end OnBytes.G4

#print axioms OnBytes.G4.Seat.laws
#print axioms OnBytes.G4.Seat.ctx_self
