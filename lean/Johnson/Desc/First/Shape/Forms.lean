-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Forms.lean: THE MAKES OF A STATEMENT's ROWS THROUGH THE GROUND's THIRTEEN
ROUTINES (Johnson/Desc/First/Base/Ground.lean): wherever a routine accepts, the makes behind are a
written function of the makes in front and of the makes of the rows handed in. General in the
carried record; nothing is evaluated.

What it is for. A chain that takes in rows with a written-out factor cannot carry the mark that no
row's tensor has one (stPlainB, Johnson/Desc/Ground/Shape/Marks.lean; not the row's kind "plain");
what its closings and switches test of the rows is read off their makes (Rows.lean, FoldMake.lean).
This shape goes beside the one shape of statement, book and roots
(Johnson/Desc/Ground/Shape/Core.lean), which sees of a group's open rows their kinds and of a
message's sample rows their number.

  `FormsSh`: groups : List (List RowMk): each group's open rows' makes; oracles : List (List
    RowMk): each message's sample rows' makes. `grpMk`, `orcMk`, `formsOf`.
  1 `orc_same`, `grp_same`, `forms_closeLedgers`.
  2 `newGroup_forms` (a new empty list), `forms_stSent`, `recv_forms`, `adopt_forms` (as many new
    empty lists as messages), `admit_forms` (the sample rows' makes laid), `join_forms`,
    `takeMask_forms`, `takeMasks_forms`, `closeLedger_forms`, `spend_forms` (nothing turns),
    `addRow_forms`, `addRows_forms` (pushed), `RowMk.renamed`, `renamed_mk`, `elsewhere_forms` (the
    other statement's sample rows' makes under the number here).
  3 `runRowsS`, `members_loop`, `runRows_mk`, **`beginRun_forms`**: where a proximity test begins:
    the rows that go to the batching have the makes runRowsS (formsOf d.st) g ‹the group's
    members›: the plain open rows, the members' sample rows in the members' order, the generator
    rows; the layout is Own.layoutOf; behind, the group holds no open row.

With Rows.lean's batch_mk: whether the batching behind a beginning returns, and the batched row's
make, is batchS of the statement's row bits, the layout and runRowsS.

Limits. From an accept alone: that a routine accepts is Johnson/Desc/Ground/Shape/Ground.lean's
matter. The makes of the rows that a chain's steps hand in are not shown here to be functions of a
shape in front. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Rows
import Johnson.Desc.Ground.Shape.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Slice VerifiableInference.Desc
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc.Ground.Sh (modAt map_modify modAt_modAt)

variable {L : Type}

/-- The makes of a statement's rows: each group's open rows; each message's sample rows. -/
structure FormsSh where
  groups : List (List RowMk)
  oracles : List (List RowMk)

def grpMk (G : Group) : List RowMk := G.rows.toList.map rowMk
def orcMk (x : Oracle) : List RowMk := x.sampleRows.toList.map rowMk

def formsOf (S : Statement) : FormsSh :=
  ⟨S.groups.toList.map grpMk, S.oracles.toList.map orcMk⟩

/-! ## 1 Changes of the statement that turn no row -/

/-- A change of one message that leaves its sample rows. -/
theorem orc_same (a : Array Oracle) (o : Nat) (f : Oracle → Oracle)
    (h : ∀ x, (f x).sampleRows = x.sampleRows) :
    (a.modify o f).toList.map orcMk = a.toList.map orcMk := by
  rw [map_modify a o f orcMk id (fun x => by unfold orcMk; rw [h]; rfl)]
  unfold modAt
  simp

/-- A change of one group that leaves its open rows. -/
theorem grp_same (a : Array Group) (g : Nat) (f : Group → Group)
    (h : ∀ G, (f G).rows = G.rows) :
    (a.modify g f).toList.map grpMk = a.toList.map grpMk := by
  rw [map_modify a g f grpMk id (fun G => by unfold grpMk; rw [h]; rfl)]
  unfold modAt
  simp

theorem forms_closeLedgers : ∀ (l : List Nat) (S : Statement),
    formsOf (closeLedgers S l) = formsOf S
  | [], _ => rfl
  | o :: l, S => by
    unfold closeLedgers
    rw [List.foldl_cons]
    refine (forms_closeLedgers l _).trans ?_
    unfold formsOf
    dsimp only
    rw [orc_same]
    intro _
    rfl

/-! ## 2 The routines -/

theorem newGroup_forms {d : DState L} {code maskCode : Nat} {x : Nat × DState L}
    (h : Ground.newGroupP d code maskCode = some x) :
    formsOf x.2.st = { formsOf d.st with groups := (formsOf d.st).groups ++ [[]] } := by
  unfold Ground.newGroupP at h
  split at h
  · cases h
    unfold formsOf Ground.withGroup
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
    rfl
  · cases h

theorem forms_stSent (S : Statement) (sent : Array OracleNotice) :
    formsOf (stSent S sent) =
      { formsOf S with oracles := (formsOf S).oracles ++ List.replicate sent.size [] } := by
  unfold formsOf stSent
  simp only [Array.toList_append, Array.toList_map, List.map_append, List.map_map]
  congr 2
  rw [← Array.length_toList]
  generalize sent.toList = l
  induction l with
  | nil => rfl
  | cons n l ih =>
    rw [List.map_cons, ih, List.length_cons, List.replicate_succ]
    rfl

theorem recv_forms {firstTree : Nat} {d : DState L} {sent : Array OracleNotice}
    {x : Array Nat × DState L} (h : Ground.recvP firstTree d sent = some x) :
    formsOf x.2.st =
      { formsOf d.st with oracles := (formsOf d.st).oracles ++ List.replicate sent.size [] } := by
  unfold Ground.recvP at h
  split at h
  · obtain ⟨lay, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact forms_stSent d.st sent
  · cases h

theorem adopt_forms {d : DState L} {sent : Array OracleNotice} {given : Array (Nat × Fmt.Src)}
    {x : Array Nat × DState L} (h : Ground.adoptP d sent given = some x) :
    formsOf x.2.st =
      { formsOf d.st with oracles := (formsOf d.st).oracles ++ List.replicate sent.size [] } := by
  unfold Ground.adoptP at h
  split at h
  · obtain ⟨lay, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact forms_stSent d.st sent
  · cases h

theorem admit_forms {d d' : DState L} {o : Nat} {rows : Array OnBytes.Row}
    (h : Ground.admitP d o rows = some d') :
    formsOf d'.st = { formsOf d.st with
      oracles := modAt (formsOf d.st).oracles o fun _ => rows.toList.map rowMk } := by
  unfold Ground.admitP at h
  split at h
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨places, -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    unfold formsOf admitted
    dsimp only
    rw [map_modify _ o _ orcMk (fun _ => rows.toList.map rowMk) (fun _ => rfl)]
  · cases h

theorem join_forms {d d' : DState L} {g o : Nat} {kept : Bool}
    (h : Ground.joinP d g o kept = some d') : formsOf d'.st = formsOf d.st := by
  unfold Ground.joinP at h
  split at h
  · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold formsOf withMessageInGroup
    dsimp only
    rw [orc_same, grp_same]
    all_goals (intro _; rfl)
  · cases h

theorem addRow_forms {d d' : DState L} {g : Nat} {row : OnBytes.Row}
    (h : Ground.addRowP d g row = some d') :
    formsOf d'.st = { formsOf d.st with
      groups := modAt (formsOf d.st).groups g (· ++ [rowMk row]) } := by
  unfold Ground.addRowP at h
  split at h
  · cases h
    unfold formsOf withRow
    dsimp only
    rw [map_modify _ g _ grpMk (· ++ [rowMk row]) (fun G => by
      unfold grpMk
      simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil])]
  · cases h

theorem takeMask_forms {d : DState L} {o : Nat} {x : Nat × DState L}
    (h : Ground.takeMaskP d o = some x) : formsOf x.2.st = formsOf d.st := by
  unfold Ground.takeMaskP at h
  split at h
  · obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold formsOf
    dsimp only
    rw [orc_same]
    intro _
    rfl
  · cases h

theorem closeLedger_forms {d d' : DState L} {o : Nat} (h : Ground.closeLedgerP d o = some d') :
    formsOf d'.st = formsOf d.st := by
  unfold Ground.closeLedgerP at h
  split at h
  · cases h
    exact forms_closeLedgers [o] d.st
  · cases h

theorem spend_forms {d d' : DState L} {o : Nat} (h : Ground.spendAsMaskP d o = some d') :
    formsOf d'.st = formsOf d.st := by
  unfold Ground.spendAsMaskP at h
  split at h
  · cases h
    unfold formsOf
    dsimp only
    rw [orc_same]
    intro _
    rfl
  · cases h

theorem addRowsFrom_forms {g : Nat} : ∀ (rows : List OnBytes.Row) (d d' : DState L),
    Ground.addRowsFrom g rows d = some d' →
    formsOf d'.st = { formsOf d.st with
      groups := modAt (formsOf d.st).groups g (· ++ rows.map rowMk) }
  | [], d, d', h => by
    cases h
    unfold modAt
    simp
  | row :: rows, d, d', h => by
    unfold Ground.addRowsFrom at h
    obtain ⟨d1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    rw [addRowsFrom_forms rows d1 d' h, addRow_forms h1]
    dsimp only
    rw [modAt_modAt]
    congr 2
    funext l
    simp

theorem addRows_forms {d d' : DState L} {g : Nat} {rows : List OnBytes.Row}
    (h : Ground.addRowsP d g rows = some d') :
    formsOf d'.st = { formsOf d.st with
      groups := modAt (formsOf d.st).groups g (· ++ rows.map rowMk) } := by
  unfold Ground.addRowsP at h
  split at h
  · exact addRowsFrom_forms rows d d' h
  · cases h

theorem takeMasksInto_forms {o : Nat} : ∀ (n : Nat) (d : DState L) (acc : Array Nat)
    (x : List Nat × DState L), Ground.takeMasksInto o n d acc = some x →
    formsOf x.2.st = formsOf d.st
  | 0, d, acc, x, h => by
    cases h
    rfl
  | n + 1, d, acc, x, h => by
    unfold Ground.takeMasksInto at h
    split at h
    · cases h
    · rename_i i d1 h1
      rw [takeMasksInto_forms n d1 _ x h]
      exact takeMask_forms h1

theorem takeMasks_forms {d : DState L} {o count : Nat} {x : List Nat × DState L}
    (h : Ground.takeMasksP d o count = some x) : formsOf x.2.st = formsOf d.st :=
  takeMasksInto_forms count d #[] x h

/-- Row.renamed on makes. -/
def RowMk.renamed (r : RowMk) (o : Nat) : RowMk :=
  { r with
    terms := r.terms.map fun t => { t with oracle := o }
    units := r.units.map fun u => { u with oracle := o }
    runs := r.runs.map fun w => { w with oracle := o }
    forms := r.forms.map fun f => { f with oracle := o } }

theorem renamed_mk (r : OnBytes.Row) (o : Nat) : rowMk (r.renamed o) = (rowMk r).renamed o := by
  unfold OnBytes.Row.renamed rowMk RowMk.renamed
  simp only [Array.toList_map, List.map_map]
  rfl

theorem elsewhere_forms {d d' : DState L} {mine theirs : Nat} {other : Statement}
    (h : Ground.elsewhereP d mine other theirs = some d') :
    formsOf d'.st = { formsOf d.st with
      oracles := modAt (formsOf d.st).oracles mine fun _ =>
        (((formsOf other).oracles[theirs]?).getD []).map (·.renamed mine) } := by
  unfold Ground.elsewhereP at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
    have e : ((formsOf other).oracles[theirs]?).getD [] = y.sampleRows.toList.map rowMk := by
      unfold formsOf
      dsimp only
      rw [List.getElem?_map, Array.getElem?_toList, hy]
      rfl
    rw [e]
    unfold formsOf
    dsimp only
    rw [map_modify _ mine _ orcMk
      (fun _ => (y.sampleRows.toList.map rowMk).map (·.renamed mine)) (fun _ => by
        unfold orcMk
        simp only [Array.toList_map, List.map_map]
        apply List.map_congr_left
        intro r _
        exact renamed_mk r mine)]
  · cases h

/-! ## 3 A proximity test begins: what goes to the batching, and what is left -/

/-- runRows on makes. members: the group's members, in order. -/
def runRowsS (F : FormsSh) (g : Nat) (members : List Nat) : List RowMk :=
  ((F.groups[g]?).getD []).filter (·.kind == .plain) ++
    members.flatMap (fun o => (F.oracles[o]?).getD []) ++
    ((F.groups[g]?).getD []).filter (·.kind == .generator)

theorem members_loop (S : Statement) : ∀ (l : List Nat) (a : Array OnBytes.Row),
    (l.foldl (fun a o => a ++ ((S.oracles[o]?).map (·.sampleRows)).getD #[]) a).toList.map rowMk =
      a.toList.map rowMk ++ l.flatMap fun o => ((formsOf S).oracles[o]?).getD []
  | [], a => by simp
  | o :: l, a => by
    rw [List.foldl_cons, members_loop S l, Array.toList_append, List.map_append,
      List.flatMap_cons, List.append_assoc]
    congr 2
    unfold formsOf
    dsimp only
    rw [List.getElem?_map, Array.getElem?_toList]
    cases S.oracles[o]? with
    | none => rfl
    | some x => rfl

theorem runRows_mk (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    (runRows S G).toList.map rowMk = runRowsS (formsOf S) g G.members.toList := by
  have e : ((formsOf S).groups[g]?).getD [] = G.rows.toList.map rowMk := by
    unfold formsOf
    dsimp only
    rw [List.getElem?_map, Array.getElem?_toList, hG]
    rfl
  unfold runRows runRowsS
  rw [e, ← Array.foldl_toList]
  simp only [Array.toList_append, List.map_append, Array.toList_filter, List.filter_map]
  rw [members_loop]
  simp only [List.map_nil, List.nil_append]
  rfl

theorem beginRun_forms {d : DState L} {g : Nat} {x : RunInput × DState L}
    (h : Ground.beginRunP d g = some x) :
    ∃ G, d.st.groups[g]? = some G ∧ x.1.layout = Own.layoutOf d.st G ∧
      x.1.rows.toList.map rowMk = runRowsS (formsOf d.st) g G.members.toList ∧
      formsOf x.2.st = { formsOf d.st with
        groups := modAt (formsOf d.st).groups g fun _ => [] } := by
  unfold Ground.beginRunP at h
  split at h
  · obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    refine ⟨G, hG, rfl, runRows_mk d.st g G hG, ?_⟩
    have e := forms_closeLedgers G.members.toList d.st
    unfold formsOf at e ⊢
    unfold begun
    dsimp only
    rw [FormsSh.mk.injEq] at e
    rw [map_modify _ g _ grpMk (fun _ => []) (fun _ => rfl), e.1, e.2]
  · cases h

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.newGroup_forms
#print axioms VerifiableInference.Desc.First.Shape.recv_forms
#print axioms VerifiableInference.Desc.First.Shape.adopt_forms
#print axioms VerifiableInference.Desc.First.Shape.admit_forms
#print axioms VerifiableInference.Desc.First.Shape.join_forms
#print axioms VerifiableInference.Desc.First.Shape.addRow_forms
#print axioms VerifiableInference.Desc.First.Shape.addRows_forms
#print axioms VerifiableInference.Desc.First.Shape.takeMasks_forms
#print axioms VerifiableInference.Desc.First.Shape.elsewhere_forms
#print axioms VerifiableInference.Desc.First.Shape.takeMask_forms
#print axioms VerifiableInference.Desc.First.Shape.closeLedger_forms
#print axioms VerifiableInference.Desc.First.Shape.spend_forms
#print axioms VerifiableInference.Desc.First.Shape.runRows_mk
#print axioms VerifiableInference.Desc.First.Shape.beginRun_forms
