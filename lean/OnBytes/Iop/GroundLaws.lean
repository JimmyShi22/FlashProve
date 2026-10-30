-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/GroundLaws.lean: laws on the type of a block (OnBytes/Iop/Ground.lean).

The words (view, dry run, channel, plan, named test, book of trees) are explained in the section
comments of Ground.lean. A decision made of blocks is taken apart block by block. The laws say what
a run of a block is:
 - Blk.Yields b c x c' (Ground.lean) says that b, run from the context c, succeeds with the value
   x and leaves the context c'. The laws on single calls are stated with it, so they do not depend
   on how a failure is written; yields_iff says what it means for the block applied to the context.
 - A run of "b1, then b2" is a run of b1 followed by a run of b2 from what b1 has left.
 - A decision is yes exactly if the block's run succeeds, uses up the view's rounds and opened
   columns and the plan's entries, leaves no round open and the channel settled (Chan.settled), and
   leaves no named test recorded as failed.
 - Five calls on the channel (item, recvE, recvAnswer, close, closeOne), in a run on a view: what
   each takes of the view's rounds and what it returns. Laws on further calls are in
   OnBytes/Iop/OpenLaws.lean, OnBytes/Slice/BlkBegin.lean and OnBytes/Slice/BlkCalls.lean.
The laws on must, test, get, testOnView and getOnView are stated for the call without a name of its
own, which is how the blocks call them.

Main definitions: Chan.pending, Blk.SameBut, Blk.SameButNotes.
Main theorems: yields_iff, yields_pure, yields_bind, yields_must, yields_test, yields_check,
yields_get, yields_statement, yields_theBook, yields_setBook, yields_onView, yields_getOnView,
yields_testOnView, yields_checkOnView, yields_note, yields_noteBy, spendAsMask_inv, closeOne_inv,
decides_iff, runOn_ok_iff, decides_iff_runOn, item_inv, recvE_inv, recvAnswer_inv, close_inv.

What is not claimed. Nothing on soundness. A law with the hypothesis c.ch.dry = false says nothing
on the dry run; the other laws hold in both runs. No law says what a dry run notes. The laws speak
of all functions of the type Blk and of all contexts, not only of those that occur in a run of the
program. A call of Ground.lean that is not named above has no law here. The program does not import
this file.
-/
import OnBytes.Iop.Ground

namespace OnBytes

namespace Blk

/-- b.Yields c x c' holds exactly if b, applied to c, is .ok (x, c'). -/
theorem yields_iff {α : Type} (b : Blk α) (c : Ctx) (x : α) (c' : Ctx) :
    b.Yields c x c' ↔ b c = .ok (x, c') := by
  unfold Yields outcome
  cases b c <;> simp [Except.toOption]

/-- A block that only returns a value leaves the context as it was. -/
theorem yields_pure {α : Type} (a x : α) (c c' : Ctx) :
    (pure a : Blk α).Yields c x c' ↔ x = a ∧ c' = c := by
  rw [yields_iff]
  show (Except.ok (a, c) : Except Failure (α × Ctx)) = .ok (x, c') ↔ _
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A run of "b1, then b2" is a run of b1 followed by a run of b2 from what b1 has left. -/
theorem yields_bind {α β : Type} (b1 : Blk α) (b2 : α → Blk β) (c c2 : Ctx) (y : β) :
    (b1 >>= b2).Yields c y c2 ↔ ∃ x c1, b1.Yields c x c1 ∧ (b2 x).Yields c1 y c2 := by
  simp only [yields_iff]
  show (b1 c >>= fun p => b2 p.1 p.2) = .ok (y, c2) ↔ _
  cases h : b1 c with
  | error f =>
    constructor
    · intro e
      cases e
    · rintro ⟨x, c1, e, _⟩
      cases e
  | ok p =>
    obtain ⟨x, c1⟩ := p
    constructor
    · intro e
      exact ⟨x, c1, rfl, e⟩
    · rintro ⟨x', c1', e, e2⟩
      cases e
      exact e2

/-- A public condition that passes was true, and it changes nothing. -/
theorem yields_must (b : Bool) (c c' : Ctx) :
    (must b).Yields c () c' ↔ b = true ∧ c' = c := by
  rw [yields_iff]
  unfold must
  cases b
  · simp
  · simp [eq_comm]

/-- A condition on values that passes in a run on a view was true, and it changes nothing. -/
theorem yields_test (b : Bool) (c c' : Ctx) (hd : c.ch.dry = false) :
    (test b).Yields c () c' ↔ b = true ∧ c' = c := by
  rw [yields_iff]
  unfold test
  cases b
  · simp [hd]
  · simp [eq_comm]

/-- If a named test has run on a view and no named test is recorded as failed after it, then it was
true and it has changed nothing. -/
theorem yields_check (name : String) (b : Bool) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (check name b).Yields c () c') (hf : c'.failed = none) : b = true ∧ c' = c := by
  rw [yields_iff] at h
  unfold check at h
  cases b
  · cases hc : c.failed with
    | none =>
      simp [hd, hc] at h
      rw [← h] at hf
      cases hf
    | some n =>
      simp [hd, hc] at h
      rw [← h, hc] at hf
      cases hf
  · simp at h
    exact ⟨rfl, h.symm⟩

/-- A value that is taken was there, and taking it changes nothing. -/
theorem yields_get {α : Type} (x : Option α) (a : α) (c c' : Ctx) :
    (get x).Yields c a c' ↔ x = some a ∧ c' = c := by
  rw [yields_iff]
  unfold get
  cases x
  · simp
  · simp [eq_comm]

/-- Reading the statement returns it and changes nothing. -/
theorem yields_statement (S : Statement) (c c' : Ctx) :
    statement.Yields c S c' ↔ S = c.st ∧ c' = c := by
  rw [yields_iff]
  unfold statement
  simp [eq_comm]

/-- Reading the book of trees returns it and changes nothing. -/
theorem yields_theBook (B : TreeBook) (c c' : Ctx) :
    theBook.Yields c B c' ↔ B = c.book ∧ c' = c := by
  rw [yields_iff]
  unfold theBook
  simp [eq_comm]

/-- Replacing the book changes nothing but the book. -/
theorem yields_setBook (B : TreeBook) (c c' : Ctx) :
    (setBook B).Yields c () c' ↔ c' = { c with book := B } := by
  rw [yields_iff]
  unfold setBook
  simp [eq_comm]

/-- A condition that only a run on a view computes, and that passes there, was true, and it changes
nothing. -/
theorem yields_testOnView (f : Unit → Bool) (c c' : Ctx) (hd : c.ch.dry = false) :
    (testOnView f).Yields c () c' ↔ f () = true ∧ c' = c := by
  rw [yields_iff]
  unfold testOnView
  cases f ()
  · simp [hd]
  · simp [eq_comm]

/-- A value that only a run on a view computes is computed there, and nothing changes. -/
theorem yields_onView {α : Type} (dflt : α) (f : Unit → α) (x : α) (c c' : Ctx)
    (hd : c.ch.dry = false) : (onView dflt f).Yields c x c' ↔ x = f () ∧ c' = c := by
  rw [yields_iff]
  unfold onView
  simp [hd, eq_comm]

/-- A value that only a run on a view computes and that may be missing: on a view it was there, and
nothing changes. -/
theorem yields_getOnView {α : Type} (dflt : α) (f : Unit → Option α) (x : α) (c c' : Ctx)
    (hd : c.ch.dry = false) : (getOnView dflt f).Yields c x c' ↔ f () = some x ∧ c' = c := by
  rw [yields_iff]
  unfold getOnView
  cases f () <;> simp [hd, eq_comm]

/-- A named test that only a run on a view computes: if no named test is recorded as failed after
it, it was true and it has changed nothing. -/
theorem yields_checkOnView (name : String) (f : Unit → Bool) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (checkOnView name f).Yields c () c') (hf : c'.failed = none) :
    f () = true ∧ c' = c := by
  rw [yields_iff] at h
  unfold checkOnView at h
  cases hb : f ()
  · cases hc : c.failed with
    | none =>
      simp [hd, hc, hb] at h
      rw [← h] at hf
      cases hf
    | some n =>
      simp [hd, hc] at h
      rw [← h, hc] at hf
      cases hf
  · simp [hb] at h
    exact ⟨rfl, h.symm⟩

/-- What a call that only keeps an intermediate value leaves as it was. -/
structure SameButNotes (c c' : Ctx) : Prop where
  ch : c'.ch = c.ch
  st : c'.st = c.st
  book : c'.book = c.book
  failed : c'.failed = c.failed

/-- Keeping an intermediate value leaves the channel, the statement, the book and the record of a
failed test as they were (SameButNotes). -/
theorem yields_note (what : String) (value : E) (c c' : Ctx)
    (h : (note what value).Yields c () c') : SameButNotes c c' := by
  rw [yields_iff] at h
  unfold note at h
  cases Except.ok.inj h
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Keeping an intermediate value that is computed only if such values are kept leaves the same four
fields as they were (SameButNotes). -/
theorem yields_noteBy (what : String) (value : Unit → E) (c c' : Ctx)
    (h : (noteBy what value).Yields c () c') : SameButNotes c c' := by
  rw [yields_iff] at h
  unfold noteBy at h
  cases Except.ok.inj h
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- An oracle message that was spent as a mask gets its mark, and nothing else changes. Nothing is
said of the three conditions that spendAsMask tests first. -/
theorem spendAsMask_inv (o : Nat) (c c' : Ctx) (h : (spendAsMask o).Yields c () c') :
    c' = { c with st := { c.st with
      oracles := c.st.oracles.modify o fun x => { x with spentAsMask := true } } } := by
  unfold spendAsMask oracle at h
  obtain ⟨x, c1, k1, k2⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨S, c0, k3, k4⟩ := (yields_bind _ _ _ _ _).1 k1
  obtain ⟨_, e0⟩ := (yields_statement _ _ _).1 k3
  obtain ⟨_, e1⟩ := (yields_get _ _ _ _).1 k4
  obtain ⟨u, c2, k5, k6⟩ := (yields_bind _ _ _ _ _).1 k2
  obtain ⟨_, e2⟩ := (yields_must _ _ _).1 k5
  have e3 : c2 = c := e2.trans (e1.trans e0)
  rw [e3] at k6
  rw [yields_iff] at k6
  unfold onOracle at k6
  split at k6
  · exact (congrArg Prod.snd (Except.ok.inj k6)).symm
  · cases k6

/-- A round that was closed for one element: it was closed, and the elements that it drew are that
one element. Nothing is said of what else the round drew. -/
theorem closeOne_inv (name : String) (kind : Fmt.Kind) (nz : Nat) (x : E) (c c' : Ctx)
    (h : (closeOne name kind nz).Yields c x c') :
    ∃ d, (close name kind nz).Yields c d c' ∧ d.elems = [x.triple] := by
  unfold closeOne at h
  obtain ⟨d, c1, h1, h2⟩ := (yields_bind _ _ _ _ _).1 h
  cases hel : d.elems with
  | nil =>
    rw [hel] at h2
    cases h2
  | cons a l =>
    cases l with
    | nil =>
      rw [hel] at h2
      obtain ⟨rfl, rfl⟩ := (yields_pure _ _ _ _).1 h2
      exact ⟨d, h1, by rw [E.triple_ofTriple]; exact hel⟩
    | cons a' l' =>
      rw [hel] at h2
      cases h2

/-- A decision is yes exactly if the block's run on the view (Blk.runFrom) succeeds, uses up the
view's rounds and opened columns and the plan's entries, leaves no round open, leaves the channel
settled (Chan.settled), and leaves no named test recorded as failed. -/
theorem decides_iff (b : Blk Unit) (s : Start) (v : Fmt.View) :
    b.decides s v = true ↔ ∃ c : Ctx, b.runFrom s false v.rounds v.opened = some ((), c) ∧
      c.ch.left = [] ∧ c.ch.cur = none ∧ c.ch.entries = [] ∧ c.ch.opened = [] ∧
      c.ch.settled = true ∧ c.failed = none := by
  have hr : b.runFrom s false v.rounds v.opened =
      (b.runNamed s false v.rounds v.opened).toOption := rfl
  rw [hr]
  unfold decides Walk.decides walk
  cases h : b.runNamed s false v.rounds v.opened with
  | error f => simp [Except.toOption]
  | ok p =>
    obtain ⟨u, c⟩ := p
    cases u
    by_cases hc : (c.ch.cur.isNone && c.ch.entries.isEmpty && c.ch.opened.isEmpty &&
        c.ch.settled && c.failed.isNone) = true
    · have hc' := hc
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff] at hc'
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc'
      simp only [hc, if_true]
      cases hl : c.ch.left with
      | nil =>
        simp only [true_iff]
        exact ⟨c, rfl, hl, h1, h2, h3, h4, h5⟩
      | cons r t =>
        constructor
        · intro e
          cases e
        · rintro ⟨c2, e, e1, _⟩
          cases e
          rw [hl] at e1
          cases e1
    · simp only [hc]
      constructor
      · intro e
        cases e
      · rintro ⟨c2, e, _, h1, h2, h3, h4, h5⟩
        cases e
        exact absurd (by simp [h1, h2, h3, h4, h5]) hc

/-- Blk.runOn gives a value exactly if Blk.walk gives that value and leaves no round. -/
theorem runOn_ok_iff {α : Type} (b : Blk α) (s : Start) (v : Fmt.View) (a : α) :
    b.runOn s v = .ok a ↔ b.walk s v.opened v.rounds = some (a, []) := by
  unfold runOn walk
  cases h : b.runNamed s false v.rounds v.opened with
  | error f => simp
  | ok p =>
    obtain ⟨a', c⟩ := p
    cases hf : c.failed with
    | some n => simp [hf]
    | none =>
      cases he : c.ch.entries.isEmpty <;> cases hs : c.ch.settled <;> cases hc : c.ch.cur.isNone <;>
        cases ho : c.ch.opened.isEmpty <;> cases hl : c.ch.left <;> simp [he, hs, hc, ho, hl, hf]

/-- The decision is yes exactly if Blk.runOn succeeds. -/
theorem decides_iff_runOn (b : Blk Unit) (s : Start) (v : Fmt.View) :
    b.decides s v = true ↔ b.runOn s v = .ok () := by
  rw [runOn_ok_iff]
  unfold decides Walk.decides
  cases h : b.walk s v.opened v.rounds with
  | none => simp
  | some p =>
    obtain ⟨u, l⟩ := p
    cases u
    cases l <;> simp

/-! ## The channel, in a run on a view -/

end Blk

/-- The view's rounds that are not yet closed. If a message is open, the first of them is its round,
with the items that are not yet taken. -/
def Chan.pending (ch : Chan) : List Fmt.RoundView :=
  match ch.cur with
  | some r => r :: ch.left
  | none => ch.left

namespace Blk

/-- What a call that only receives an item leaves as it was. -/
structure SameBut (c c' : Ctx) : Prop where
  st : c'.st = c.st
  book : c'.book = c.book
  failed : c'.failed = c.failed
  dry : c'.ch.dry = c.ch.dry
  entries : c'.ch.entries = c.ch.entries
  opened : c'.ch.opened = c.ch.opened
  last : c'.ch.last = c.ch.last
  asked : c'.ch.askedRows = c.ch.askedRows
  roots : c'.ch.roots = c.ch.roots
  firstTree : c'.ch.firstTree = c.ch.firstTree
  samples : c'.ch.samples = c.ch.samples

/-- In a run on a view: an item that was received was the next item of the first round that is not
yet closed. -/
theorem item_inv (i : Fmt.Item) (dflt g : Fmt.ItemValue) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (item i dflt).Yields c g c') :
    ∃ r rest vs, c.ch.pending = r :: rest ∧ r.vals = g :: vs ∧
      c'.ch.pending = { r with vals := vs } :: rest ∧ SameBut c c' := by
  rw [yields_iff] at h
  unfold item at h
  simp only [hd, Bool.false_eq_true, if_false] at h
  cases hc : c.ch.cur with
  | some r =>
    simp only [hc] at h
    cases hv : r.vals with
    | nil => simp [hv] at h
    | cons g' gs =>
      simp only [hv, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨r, c.ch.left, gs, by simp [Chan.pending, hc], hv, by simp [Chan.pending],
        ⟨rfl, rfl, rfl, hd.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | none =>
    simp only [hc] at h
    cases hl : c.ch.left with
    | nil => simp [hl] at h
    | cons r t =>
      simp only [hl] at h
      cases hv : r.vals with
      | nil => simp [hv] at h
      | cons g' gs =>
        simp only [hv, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨r, t, gs, by simp [Chan.pending, hc, hl], hv, by simp [Chan.pending],
          ⟨rfl, rfl, rfl, hd.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- In a run on a view: an element that was received was the next item of the first round that is
not yet closed. -/
theorem recvE_inv (x : E) (c c' : Ctx) (hd : c.ch.dry = false) (h : recvE.Yields c x c') :
    ∃ r rest vs, c.ch.pending = r :: rest ∧ r.vals = .e x.triple :: vs ∧
      c'.ch.pending = { r with vals := vs } :: rest ∧ SameBut c c' := by
  unfold recvE at h
  obtain ⟨g, c1, h1, h2⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨r, rest, vs, e1, e2, e3, e4⟩ := item_inv _ _ _ _ _ hd h1
  cases g with
  | e y =>
    obtain ⟨rfl, rfl⟩ := (yields_pure _ _ _ _).1 h2
    exact ⟨r, rest, vs, e1, by rw [E.triple_ofTriple]; exact e2, e3, e4⟩
  | f _ => cases h2
  | word _ => cases h2
  | root _ => cases h2
  | answer _ => cases h2

/-- In a run on a view: an answer that was received was the next item of the first round that is not
yet closed. -/
theorem recvAnswer_inv (x : E) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : recvAnswer.Yields c x c') :
    ∃ r rest vs, c.ch.pending = r :: rest ∧ r.vals = .answer x.triple :: vs ∧
      c'.ch.pending = { r with vals := vs } :: rest ∧ SameBut c c' := by
  unfold recvAnswer at h
  obtain ⟨g, c1, h1, h2⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨r, rest, vs, e1, e2, e3, e4⟩ := item_inv _ _ _ _ _ hd h1
  cases g with
  | answer y =>
    obtain ⟨rfl, rfl⟩ := (yields_pure _ _ _ _).1 h2
    exact ⟨r, rest, vs, e1, by rw [E.triple_ofTriple]; exact e2, e3, e4⟩
  | f _ => cases h2
  | word _ => cases h2
  | root _ => cases h2
  | e _ => cases h2

/-- In a run on a view: a round that was closed was the first round not yet closed, and all its
items had been taken. The call returns what that round drew: as many elements, positions and trits
as the plan's next entry says. That entry has the name and the number nz under which the round was
closed. Nothing is said of Chan.settled, which close also tests. -/
theorem close_inv (name : String) (kind : Fmt.Kind) (nz : Nat) (d : Fmt.Drawn) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (close name kind nz).Yields c d c') :
    ∃ e es r rest, c.ch.entries = e :: es ∧ e.name = name ∧ e.drawNZ = nz ∧
      c.ch.pending = r :: rest ∧ r.vals = [] ∧ d = r.drawn ∧
      d.elems.length = e.drawE ∧ d.poss.length = e.poss ∧ d.trits.length = e.trits ∧
      c'.ch.pending = rest ∧ c'.ch.entries = es ∧ c'.ch.last = some e ∧
      c'.st = c.st ∧ c'.book = c.book ∧ c'.failed = c.failed ∧ c'.ch.dry = false ∧
      c'.ch.opened = c.ch.opened ∧ c'.ch.roots = c.ch.roots ∧
      c'.ch.firstTree = c.ch.firstTree ∧ c'.ch.samples = c.ch.samples := by
  rw [yields_iff] at h
  unfold close at h
  cases he : c.ch.entries with
  | nil => simp [he] at h
  | cons e es =>
    simp only [he] at h
    by_cases hg : (e.name != name || e.drawNZ != nz || !c.ch.settled) = true
    · simp [hg] at h
    · have hd' : ¬ (c.ch.dry = true) := by simp [hd]
      simp only [hg, Bool.false_eq_true, if_false, hd'] at h
      have hg' : e.name = name ∧ e.drawNZ = nz := by
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or] at hg
        exact ⟨Decidable.of_not_not hg.1.1, Decidable.of_not_not hg.1.2⟩
      have hx : ∃ r t, c.ch.pending = r :: t ∧
          (if (r.vals.isEmpty && r.drawn.elems.length == e.drawE &&
              r.drawn.poss.length == e.poss && r.drawn.trits.length == e.trits) = true then
            Except.ok (r.drawn, { c with ch := { c.ch with
              dry := false, entries := es, last := some e, askedRows := false, cur := none,
              left := t } })
          else Except.error ({ name := shapeName } : Failure)) = .ok (d, c') := by
        cases hc : c.ch.cur with
        | some r =>
          simp only [hc] at h
          exact ⟨r, c.ch.left, by simp [Chan.pending, hc], h⟩
        | none =>
          simp only [hc] at h
          cases hl : c.ch.left with
          | nil => simp [hl] at h
          | cons r t =>
            simp only [hl] at h
            exact ⟨r, t, by simp [Chan.pending, hc, hl], h⟩
      obtain ⟨r, t, hp, hh⟩ := hx
      by_cases hk : (r.vals.isEmpty && r.drawn.elems.length == e.drawE &&
            r.drawn.poss.length == e.poss && r.drawn.trits.length == e.trits) = true
      · simp only [hk, if_true, Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hk
        exact ⟨e, es, r, t, rfl, hg'.1, hg'.2, hp, hk.1.1.1, rfl, hk.1.1.2, hk.1.2, hk.2,
          by simp [Chan.pending], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp [hk] at hh

end Blk

end OnBytes

#print axioms OnBytes.Blk.yields_bind
#print axioms OnBytes.Blk.decides_iff
#print axioms OnBytes.Blk.recvE_inv
#print axioms OnBytes.Blk.close_inv
