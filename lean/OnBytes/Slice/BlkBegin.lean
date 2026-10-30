-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkBegin.lean: further laws on single calls of a block, on one call for each entry of
an array, and on the beginning of a proximity test.

A run of a block of the program (the Lean verifier in OnBytes/) is taken apart call by call
(OnBytes/Iop/Ground.lean: `Blk.Yields`; OnBytes/Iop/GroundLaws.lean: `yields_bind`). This file says
what a run of some further calls is: the question whether a round batches as many rows as the plan's
entry counts; reading a group or its layout; changing a group or an oracle message; a loop over an
array. With these it takes apart the call with which every proximity test begins (`Blk.beginRun`):
which rows it hands to the batching, in which order, and which statement it leaves.

Main definitions.
 `RunAll`        the runs of a call on the entries of a list, one after the other.
 `closeLedgers`  the statement with the ledgers of the listed oracle messages closed.
 `runRows`       the rows that a proximity test takes in, in the fixed order.
 `begun`         the statement after the beginning of a test.
Main theorems: `requireRows_inv`, `yields_group`, `yields_layout`,
`onGroup_inv`, `onOracle_inv`, `yields_forM`, `closeLedgers_inv`, `beginRun_inv`.
Not claimed. Nothing on the dry run. Nothing on soundness.
-/
import OnBytes.Iop.GroundLaws

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## Single calls -/

/-- Outside the dry run, the number of rows that a block holds against the plan's entry is the
entry's. -/
theorem requireRows_inv (rows : Nat) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (Blk.requireRows rows).Yields c () c') :
    ∃ e, c.ch.last = some e ∧ e.rows = rows ∧
      c' = { c with ch := { c.ch with askedRows := true } } := by
  unfold Blk.Yields Blk.outcome Blk.requireRows at h
  split at h
  · next e hl =>
    split at h
    · next hc =>
      have he : e.rows = rows := by simpa [hd] using hc
      exact ⟨e, hl, he, (congrArg Prod.snd (Option.some.inj h)).symm⟩
    · cases h
  · cases h

/-- Reading a group returns it and changes nothing. -/
theorem yields_group (g : Nat) (G : Group) (c c' : Ctx) :
    (Blk.group g).Yields c G c' ↔ c.st.groups[g]? = some G ∧ c' = c := by
  unfold Blk.group
  rw [Blk.yields_bind]
  constructor
  · rintro ⟨S, c1, h1, h2⟩
    obtain ⟨rfl, rfl⟩ := (Blk.yields_statement _ _ _).1 h1
    exact (Blk.yields_get _ _ _ _).1 h2
  · intro h
    exact ⟨c.st, c, (Blk.yields_statement _ _ _).2 ⟨rfl, rfl⟩, (Blk.yields_get _ _ _ _).2 h⟩

/-- Reading a group's layout returns it and changes nothing. -/
theorem yields_layout (g : Nat) (L : GroupLayout) (c c' : Ctx) :
    (Blk.layout g).Yields c L c' ↔ c.st.layout g = some L ∧ c' = c := by
  unfold Blk.layout
  rw [Blk.yields_bind]
  constructor
  · rintro ⟨S, c1, h1, h2⟩
    obtain ⟨rfl, rfl⟩ := (Blk.yields_statement _ _ _).1 h1
    exact (Blk.yields_get _ _ _ _).1 h2
  · intro h
    exact ⟨c.st, c, (Blk.yields_statement _ _ _).2 ⟨rfl, rfl⟩, (Blk.yields_get _ _ _ _).2 h⟩

/-- A change of a group changes that group alone. -/
theorem onGroup_inv (g : Nat) (f : Group → Group) (c c' : Ctx)
    (h : (Blk.onGroup g f).Yields c () c') :
    g < c.st.groups.size ∧
      c' = { c with st := { c.st with groups := c.st.groups.modify g f } } := by
  unfold Blk.Yields Blk.outcome Blk.onGroup at h
  split at h
  · next hg => exact ⟨hg, (congrArg Prod.snd (Option.some.inj h)).symm⟩
  · cases h

/-- A change of an oracle message changes that oracle message alone. -/
theorem onOracle_inv (o : Nat) (f : Oracle → Oracle) (c c' : Ctx)
    (h : (Blk.onOracle o f).Yields c () c') :
    o < c.st.oracles.size ∧
      c' = { c with st := { c.st with oracles := c.st.oracles.modify o f } } := by
  unfold Blk.Yields Blk.outcome Blk.onOracle at h
  split at h
  · next ho => exact ⟨ho, (congrArg Prod.snd (Option.some.inj h)).symm⟩
  · cases h

/-! ## One call for each entry of an array -/

/-- The runs of f on the entries of a list, one after the other. -/
def RunAll {α : Type} (f : α → Blk Unit) : List α → Ctx → Ctx → Prop
  | [], c, c' => c' = c
  | a :: l, c, c' => ∃ c1, (f a).Yields c () c1 ∧ RunAll f l c1 c'

/-- A run of a loop over a list is the runs of the calls, in the list's order. -/
theorem yields_foldlM {α : Type} (f : α → Blk Unit) : ∀ (l : List α) (c c' : Ctx),
    (l.foldlM (fun (_ : Unit) a => f a) ()).Yields c () c' ↔ RunAll f l c c'
  | [], c, c' => by
    rw [List.foldlM_nil, Blk.yields_pure]
    exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  | a :: l, c, c' => by
    rw [List.foldlM_cons, Blk.yields_bind]
    constructor
    · rintro ⟨u, c1, h1, h2⟩
      exact ⟨c1, h1, (yields_foldlM f l c1 c').1 h2⟩
    · rintro ⟨c1, h1, h2⟩
      exact ⟨(), c1, h1, (yields_foldlM f l c1 c').2 h2⟩

/-- A run of one call for each entry of an array is the runs of the calls, in the entries' order. -/
theorem yields_forM {α : Type} (f : α → Blk Unit) (as : Array α) (c c' : Ctx) :
    (as.forM f).Yields c () c' ↔ RunAll f as.toList c c' := by
  unfold Array.forM
  rw [← Array.foldlM_toList]
  exact yields_foldlM f as.toList c c'

/-! ## The beginning of a proximity test -/

/-- The statement with the ledgers of the listed oracle messages closed. -/
def closeLedgers (S : Statement) (l : List Nat) : Statement :=
  l.foldl (fun S o => { S with oracles := S.oracles.modify o fun x =>
    { x with ledger := x.ledger.map fun l => { l with closed := true } } }) S

/-- The rows that a proximity test takes in, in the fixed order: the plain rows; each member's
sample rows; the generator rows. -/
def runRows (S : Statement) (G : Group) : Array Row :=
  G.rows.filter (·.kind == .plain) ++
    G.members.foldl (fun a o => a ++ ((S.oracles[o]?).map (·.sampleRows)).getD #[]) #[] ++
    G.rows.filter (·.kind == .generator)

/-- The statement after the beginning of the test on group g: the members' ledgers are closed, the
group is marked and holds no open row. -/
def begun (S : Statement) (g : Nat) (G : Group) : Statement :=
  { closeLedgers S G.members.toList with
    groups := (closeLedgers S G.members.toList).groups.modify g fun G =>
      { G with inRun := true, rows := #[] } }

/-- Closing the ledgers of the listed oracle messages changes these ledgers alone. -/
theorem closeLedgers_inv : ∀ (l : List Nat) (c c' : Ctx), RunAll Blk.closeLedger l c c' →
    c' = { c with st := closeLedgers c.st l }
  | [], _, _, h => h
  | o :: l, c, c', h => by
    obtain ⟨c1, h1, h2⟩ := h
    obtain ⟨_, rfl⟩ := onOracle_inv o _ c c1 h1
    exact closeLedgers_inv l _ c' h2

/-- A run of the beginning of a proximity test: the group was in no test and has a member; the call
returns the layout with the rows `runRows` and leaves the statement `begun`. -/
theorem beginRun_inv (g : Nat) (input : RunInput) (c c' : Ctx)
    (h : (Blk.beginRun g).Yields c input c') :
    ∃ G L, c.st.groups[g]? = some G ∧ G.inRun = false ∧ G.members.isEmpty = false ∧
      c.st.layout g = some L ∧ input = ⟨L, runRows c.st G⟩ ∧
      c' = { c with st := begun c.st g G } := by
  unfold Blk.beginRun at h
  obtain ⟨G, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨hG, e1⟩ := (yields_group _ _ _ _).1 h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨hm, e2⟩ := (Blk.yields_must _ _ _).1 h2
  obtain ⟨L, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨hL, e3⟩ := (yields_layout _ _ _ _).1 h3
  obtain ⟨S, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨eS, e4⟩ := (Blk.yields_statement _ _ _).1 h4
  obtain ⟨_, c5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  have e5 := closeLedgers_inv _ _ _ ((yields_forM _ _ _ _).1 h5)
  obtain ⟨_, c6, h6, a6⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
  obtain ⟨_, e6⟩ := onGroup_inv _ _ _ _ h6
  obtain ⟨ei, e7⟩ := (Blk.yields_pure _ _ _ _).1 a6
  -- nothing has changed before the ledgers are closed
  have e2' : c2 = c := e2.trans e1
  have e3' : c3 = c := e3.trans e2'
  have e4' : c4 = c := e4.trans e3'
  rw [e2'] at hL
  rw [e3'] at eS
  rw [e4'] at e5
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm
  refine ⟨G, L, hG, hm.1, hm.2, hL, ?_, ?_⟩
  · rw [ei, eS]
    rfl
  · rw [e7, e6, e5]
    rfl

end OnBytes.Slice

#print axioms OnBytes.Slice.requireRows_inv
#print axioms OnBytes.Slice.yields_group
#print axioms OnBytes.Slice.yields_layout
#print axioms OnBytes.Slice.onGroup_inv
#print axioms OnBytes.Slice.onOracle_inv
#print axioms OnBytes.Slice.yields_foldlM
#print axioms OnBytes.Slice.yields_forM
#print axioms OnBytes.Slice.closeLedgers_inv
#print axioms OnBytes.Slice.beginRun_inv
