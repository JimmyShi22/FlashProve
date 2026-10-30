-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCalls.lean: laws on single calls of a block that enter oracle messages and rows
into the statement.

A run of a block of the program (the Lean verifier in OnBytes/) is taken apart call by call
(OnBytes/Iop/Ground.lean: `Blk.Yields`; OnBytes/Iop/GroundLaws.lean: `yields_bind`;
OnBytes/Slice/BlkBegin.lean). This file says what a run of some further calls is. Each law names the
statement that the call leaves as a function of the statement before it.

Main definitions: `freshLedger`, `admitted` (an oracle message has its sample rows), `withMessageInGroup` (it is
a member of a group), `withRow`, `withRows` (a group has further open rows), `RowChecked`.
Main theorems: `yields_oracle`, `yields_lastEntry`, `yields_isDry`, `closePositions_inv`,
`seedsOf_one`, `admit_inv`, `join_inv`, `addRow_inv`, `addRowsOnView_inv`, `yields_forM_list`,
`withRows_group`, `withRows_oracles`.
Not claimed. The laws on rows hold for a run on a view; nothing is said of the dry run. Of the
public conditions that a call tests, a law keeps those that later laws use. Nothing on soundness.
-/
import OnBytes.Iop.Send
import OnBytes.Slice.BlkBegin

set_option autoImplicit false

namespace OnBytes.Slice

/-- Reading an oracle message returns it and changes nothing. -/
theorem yields_oracle (o : Nat) (x : Oracle) (c c' : Ctx) :
    (Blk.oracle o).Yields c x c' ↔ c.st.oracles[o]? = some x ∧ c' = c := by
  unfold Blk.oracle
  rw [Blk.yields_bind]
  constructor
  · rintro ⟨S, c1, h1, h2⟩
    obtain ⟨rfl, rfl⟩ := (Blk.yields_statement _ _ _).1 h1
    exact (Blk.yields_get _ _ _ _).1 h2
  · intro h
    exact ⟨c.st, c, (Blk.yields_statement _ _ _).2 ⟨rfl, rfl⟩, (Blk.yields_get _ _ _ _).2 h⟩

/-- Reading the entry of the round that was closed last returns it and changes nothing. -/
theorem yields_lastEntry (e : Fmt.Entry) (c c' : Ctx) :
    Blk.lastEntry.Yields c e c' ↔ c.ch.last = some e ∧ c' = c := by
  unfold Blk.Yields Blk.outcome Blk.lastEntry
  cases c.ch.last
  · simp [Except.toOption]
  · simp [Except.toOption, eq_comm]

/-- Asking whether the run is dry changes nothing. -/
theorem yields_isDry (b : Bool) (c c' : Ctx) :
    Blk.isDry.Yields c b c' ↔ b = c.ch.dry ∧ c' = c := by
  unfold Blk.Yields Blk.outcome Blk.isDry
  simp [Except.toOption, eq_comm]

/-- A round of positions that was closed: it was closed, the plan's entry has the range and at least
one position, and what is returned is what the round drew. -/
theorem closePositions_inv (name : String) (logN : Nat) (p : Positions × List E) (c c' : Ctx)
    (h : (Blk.closePositions name logN).Yields c p c') :
    ∃ d e, (Blk.close name .positions).Yields c d c' ∧ c'.ch.last = some e ∧ e.logN = logN ∧
      0 < e.poss ∧ p = (Positions.ofDraws logN d.poss, d.elems.map E.ofTriple) := by
  unfold Blk.closePositions at h
  obtain ⟨d, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨e, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨he, rfl⟩ := (yields_lastEntry _ _ _).1 h2
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨hm, rfl⟩ := (Blk.yields_must _ _ _).1 h3
  obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 a3
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  exact ⟨d, e, h1, he, hm.1, hm.2, rfl⟩

/-! ## An oracle message gets its sample rows -/

/-- What a round has drawn is cut into one seed: the point, one factor, and nothing after it. -/
theorem seedsOf_one (bits : Nat) (l : List E) (seeds : List SampleSeed)
    (h : Send.seedsOf bits 1 l = some seeds) :
    ∃ beta, l.drop bits = [beta] ∧ seeds = [⟨l.take bits, beta⟩] := by
  unfold Send.seedsOf at h
  cases hl : l.drop bits with
  | nil =>
    rw [hl] at h
    cases h
  | cons beta rest =>
    rw [hl] at h
    cases rest with
    | nil => exact ⟨beta, rfl, (Option.some.inj h).symm⟩
    | cons a t => cases h

/-- The ledger of a sampled oracle message's mask rows at the start; none without mask rows. -/
def freshLedger (codes : Codes) (s : OracleShape) : Option Ledger :=
  if 0 < s.maskRows then
    some { next := 0
           left :=
             Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers
           rows := max s.maskRows 1, logRows := ceilLog2 s.maskRows }
  else none

/-- The statement in which the oracle message o, of the shape s, has its sample rows and its pad. -/
def admitted (S : Statement) (o : Nat) (s : OracleShape) (places : List PadPlace)
    (rows : Array Row) : Statement :=
  { S with oracles := S.oracles.modify o fun x => { x with
      sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
      ledger := freshLedger S.codes s } }

/-- A run of the call that enters an oracle message's sample rows: the message was not sampled, the
rows are as many as its shape counts answers, at least one, and the call leaves `admitted`. -/
theorem admit_inv (o : Nat) (rows : Array Row) (c c' : Ctx)
    (h : (Send.admit o rows).Yields c () c') :
    ∃ x places, c.st.oracles[o]? = some x ∧ Send.pad c.st.codes x.shape = some places ∧
      x.sampled = false ∧ rows.size = x.shape.answers ∧ 1 ≤ x.shape.answers ∧
      c' = { c with st := admitted c.st o x.shape places rows } := by
  unfold Send.admit at h
  obtain ⟨S, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨x, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨hx, rfl⟩ := (yields_oracle _ _ _ _).1 h2
  obtain ⟨places, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨hp, rfl⟩ := (Blk.yields_get _ _ _ _).1 h3
  obtain ⟨_, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨hm, rfl⟩ := (Blk.yields_must _ _ _).1 h4
  obtain ⟨_, rfl⟩ := onOracle_inv _ _ _ _ a4
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hm
  exact ⟨x, places, hx, hp, hm.1.1, hm.1.2, hm.2, rfl⟩

/-! ## An oracle message joins a group -/

/-- The statement in which the oracle message o is a member of the group g. G: the group before. -/
def withMessageInGroup (S : Statement) (g o : Nat) (kept : Bool) (G : Group) : Statement :=
  { S with
    groups := S.groups.modify g fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept }
    oracles := S.oracles.modify o fun x => { x with groups := x.groups ++ [g] } }

/-- A run of the call by which an oracle message joins a group: the message is sampled, the group is
in no test and does not have it as a member, and the call leaves `withMessageInGroup`. -/
theorem join_inv (g o : Nat) (kept : Bool) (c c' : Ctx) (h : (Blk.join g o kept).Yields c () c') :
    ∃ G x, c.st.groups[g]? = some G ∧ c.st.oracles[o]? = some x ∧ x.sampled = true ∧
      G.inRun = false ∧ G.members.contains o = false ∧
      c' = { c with st := withMessageInGroup c.st g o kept G } := by
  unfold Blk.join at h
  obtain ⟨G, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨hG, rfl⟩ := (yields_group _ _ _ _).1 h1
  obtain ⟨x, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨hx, rfl⟩ := (yields_oracle _ _ _ _).1 h2
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨m1, rfl⟩ := (Blk.yields_must _ _ _).1 h3
  obtain ⟨_, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h4
  obtain ⟨_, c5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h5
  obtain ⟨_, c6, h6, a6⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
  obtain ⟨m4, rfl⟩ := (Blk.yields_must _ _ _).1 h6
  obtain ⟨_, c7, h7, a7⟩ := (Blk.yields_bind _ _ _ _ _).1 a6
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h7
  obtain ⟨_, c8, h8, a8⟩ := (Blk.yields_bind _ _ _ _ _).1 a7
  obtain ⟨_, rfl⟩ := onGroup_inv _ _ _ _ h8
  obtain ⟨_, rfl⟩ := onOracle_inv _ _ _ _ a8
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at m1 m4
  exact ⟨G, x, hG, hx, m1.1, m1.2, m4, rfl⟩

/-! ## New open rows -/

/-- The statement in which the group g has one more open row. -/
def withRow (S : Statement) (g : Nat) (row : Row) : Statement :=
  { S with groups := S.groups.modify g fun G => { G with rows := G.rows.push row } }

/-- What the call that adds an open row has tested of the row's parts: a structured vector has
as many variables as its table has index bits; a run's step is at least 1; a whole vector fits its
main table. -/
structure RowChecked (S : Statement) (row : Row) : Prop where
  terms : ∀ t ∈ row.terms.toList, t.v.vars = S.tableBits t.oracle t.part
  runs : ∀ w ∈ row.runs.toList, 1 ≤ w.step
  forms : ∀ f ∈ row.forms.toList, f.c.fits (S.tableBits f.oracle .main) = true

/-- A further open row of a group does not change what was tested of a row. -/
theorem RowChecked.withRow {S : Statement} {row : Row} (g : Nat) (r : Row)
    (h : RowChecked (withRow S g r) row) : RowChecked S row := ⟨h.terms, h.runs, h.forms⟩

/-- A run, on a view, of the call that adds an open row: the row is no sample row, its parts have
passed the call's tests, and it is appended to the group's rows. -/
theorem addRow_inv (g : Nat) (row : Row) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (Blk.addRow g row).Yields c () c') :
    row.kind ≠ .sample ∧ RowChecked c.st row ∧ c' = { c with st := withRow c.st g row } := by
  unfold Blk.addRow at h
  obtain ⟨S, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨G, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨_, rfl⟩ := (yields_group _ _ _ _).1 h2
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨m1, rfl⟩ := (Blk.yields_must _ _ _).1 h3
  obtain ⟨b, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨rfl, rfl⟩ := (yields_isDry _ _ _).1 h4
  rw [hd] at a4
  simp only [Bool.false_eq_true, if_false] at a4
  obtain ⟨_, c5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h5
  obtain ⟨_, c6, h6, a6⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
  obtain ⟨t1, rfl⟩ := (Blk.yields_must _ _ _).1 h6
  obtain ⟨_, c7, h7, a7⟩ := (Blk.yields_bind _ _ _ _ _).1 a6
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h7
  obtain ⟨_, c8, h8, a8⟩ := (Blk.yields_bind _ _ _ _ _).1 a7
  obtain ⟨t3, rfl⟩ := (Blk.yields_must _ _ _).1 h8
  obtain ⟨_, c9, h9, a9⟩ := (Blk.yields_bind _ _ _ _ _).1 a8
  obtain ⟨t4, rfl⟩ := (Blk.yields_must _ _ _).1 h9
  obtain ⟨_, c10, h10, a10⟩ := (Blk.yields_bind _ _ _ _ _).1 a9
  obtain ⟨_, rfl⟩ := (Blk.yields_test _ _ _ hd).1 h10
  obtain ⟨_, rfl⟩ := onGroup_inv _ _ _ _ a10
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at m1
  simp only [Array.all_eq_true_iff_forall_mem, Blk.placeOk, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at t1 t3 t4
  exact ⟨m1.2, ⟨fun t ht => (t1 t (Array.mem_toList_iff.1 ht)).2.1.2,
    fun w hw => (t3 w (Array.mem_toList_iff.1 hw)).1.2,
    fun f hf => (t4 f (Array.mem_toList_iff.1 hf)).2⟩, rfl⟩

/-- The statement in which the group g has the listed rows appended to its open rows. -/
def withRows (S : Statement) (g : Nat) (l : List Row) : Statement := l.foldl (withRow · g) S

/-- The runs, on a view, of the call that adds an open row, for the rows of a list. -/
theorem addRows_inv (g : Nat) : ∀ (l : List Row) (c c' : Ctx), c.ch.dry = false →
    RunAll (Blk.addRow g) l c c' →
    (∀ r ∈ l, r.kind ≠ .sample ∧ RowChecked c.st r) ∧ c' = { c with st := withRows c.st g l }
  | [], _, _, _, h => ⟨fun _ hr => (nomatch hr), h⟩
  | r :: l, c, c', hd, h => by
    obtain ⟨c1, h1, h2⟩ := h
    obtain ⟨hk, hch, rfl⟩ := addRow_inv g r c c1 hd h1
    obtain ⟨hl, rfl⟩ := addRows_inv g l { c with st := withRow c.st g r } c' hd h2
    refine ⟨fun x hx => ?_, rfl⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hk, hch⟩
    · exact ⟨(hl x hx).1, (hl x hx).2.withRow g r⟩

/-- A run of one call for each entry of a list is the runs of the calls, in the entries' order. -/
theorem yields_forM_list {α : Type} (f : α → Blk Unit) : ∀ (l : List α) (c c' : Ctx),
    (l.forM f).Yields c () c' ↔ RunAll f l c c'
  | [], c, c' => by
    show (pure () : Blk Unit).Yields c () c' ↔ _
    rw [Blk.yields_pure]
    exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  | a :: l, c, c' => by
    show (f a >>= fun _ => l.forM f).Yields c () c' ↔ _
    rw [Blk.yields_bind]
    constructor
    · rintro ⟨u, c1, h1, h2⟩
      exact ⟨c1, h1, (yields_forM_list f l c1 c').1 h2⟩
    · rintro ⟨c1, h1, h2⟩
      exact ⟨(), c1, h1, (yields_forM_list f l c1 c').2 h2⟩

/-- A run, on a view, of the call that adds rows which only a run on a view computes: the rows were
there, none is a sample row, their parts have passed the tests, and they are appended to the
group's rows. -/
theorem addRowsOnView_inv (g : Nat) (rows : Unit → Option (List Row)) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (Blk.addRowsOnView g rows).Yields c () c') :
    ∃ l, rows () = some l ∧ (∀ r ∈ l, r.kind ≠ .sample ∧ RowChecked c.st r) ∧
      c' = { c with st := withRows c.st g l } := by
  unfold Blk.addRowsOnView at h
  obtain ⟨G, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (yields_group _ _ _ _).1 h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h2
  obtain ⟨l, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨hl, rfl⟩ := (Blk.yields_getOnView _ _ _ _ _ hd).1 h3
  obtain ⟨hk, hc⟩ := addRows_inv g l _ c' hd ((yields_forM_list _ _ _ _).1 a3)
  exact ⟨l, hl, hk, hc⟩

/-- The group g with the listed rows added. -/
theorem withRows_group (g : Nat) : ∀ (l : List Row) (S : Statement) (G : Group),
    S.groups[g]? = some G →
    (withRows S g l).groups[g]? = some { G with rows := G.rows ++ l.toArray }
  | [], S, G, h => by
    show S.groups[g]? = _
    rw [h]
    simp
  | r :: l, S, G, h => by
    have h1 : (withRow S g r).groups[g]? = some { G with rows := G.rows.push r } := by
      show (S.groups.modify g _)[g]? = _
      rw [Array.getElem?_modify, if_pos rfl, h]
      rfl
    have h2 := withRows_group g l (withRow S g r) _ h1
    show (withRows (withRow S g r) g l).groups[g]? = _
    rw [h2]
    simp

/-- Adding rows to a group leaves the oracle messages and the codes as they were. -/
theorem withRows_oracles (g : Nat) : ∀ (l : List Row) (S : Statement),
    (withRows S g l).oracles = S.oracles ∧ (withRows S g l).codes = S.codes
  | [], _ => ⟨rfl, rfl⟩
  | r :: l, S => withRows_oracles g l (withRow S g r)

end OnBytes.Slice

#print axioms OnBytes.Slice.closePositions_inv
#print axioms OnBytes.Slice.admit_inv
#print axioms OnBytes.Slice.join_inv
#print axioms OnBytes.Slice.addRow_inv
#print axioms OnBytes.Slice.addRowsOnView_inv
#print axioms OnBytes.Slice.withRows_group
#print axioms OnBytes.Slice.yields_oracle
#print axioms OnBytes.Slice.yields_lastEntry
#print axioms OnBytes.Slice.yields_isDry
#print axioms OnBytes.Slice.seedsOf_one
#print axioms OnBytes.Slice.RowChecked.withRow
#print axioms OnBytes.Slice.addRows_inv
#print axioms OnBytes.Slice.yields_forM_list
#print axioms OnBytes.Slice.withRows_oracles
