-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Rows.lean: THE MAKE OF A STATEMENT's ROWS, AND THE BATCHING ON MAKES:
Own.batch (Johnson/Desc/Own/Batch.lean) returns just where its step on makes returns, and the make
of what it returns is the step's value. General laws; nothing is evaluated.

THE FIELDS' TYPES (the records: OnBytes/Iop/Ground.lean:214-302):
  `TermMk` of Term: oracle : Nat, part : Part, v : TensorSh. `UnitMk` of Single: oracle, part,
    index; LEFT OUT: coeff. `RunMk` of Run: oracle, part, first, step; of coeffs its size. `MainMk`
    of MainForm: oracle, c : FormSh. `RowMk` of Row: kind : RowKind and the four lists; LEFT OUT:
    target. `GroupMk` of GroupRow: group, c : FormSh, kept : List (Nat × FormSh), of d its size;
    LEFT OUT: target.

The form of each law: (f x).map mk = fS (mk x): one equation says both that f returns just where
the step on makes returns and what the make behind is. The statement enters through its row bits
alone (rb := S.rowBits, a function of the messages' shapes).
  2 `onKeptS`, `findIdx_map`, `onKept_mk`.
  3 `entryIntoS` | `entryInto_mk`, `termIntoS` | `termInto_mk`, `foldlM_mk`, `runIntoS` |
    `runInto_mk`, `formIntoS` | `formInto_mk`.
  4 `GroupMk.ready` | `ready_mk`, `groupMk_target`, `bind_mk`, `rowIntoS` | **`rowInto_mk`**.
  5 `liesAsS` | `liesAs_mk`, `runMk_scaled`, `runMk_addScaled`, `addRunsS` | `addRuns_mk`,
    `RowMk.addScaled` | `addScaled_mk`: a run on the same entries as an earlier one leaves no new
    run: which runs lie so is read off the makes.
  6 `batchS`, **`batch_mk`**.

Limits. No state is shown at which batchS returns. That a step of a chain lays rows whose makes are
functions of a shape in front is not shown here. Nothing on what a row is worth. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Makes
import Johnson.Desc.Ground.Shape.Core
import Johnson.Desc.Own.Batch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.Ground.Sh (modAt map_modify)

/-! ## 1 The makes -/

structure TermMk where
  oracle : Nat
  part : Part
  v : TensorSh

structure UnitMk where
  oracle : Nat
  part : Part
  index : Nat

structure RunMk where
  oracle : Nat
  part : Part
  first : Nat
  step : Nat
  size : Nat

structure MainMk where
  oracle : Nat
  c : FormSh

/-- A row's make: all but its coefficients and its target. -/
structure RowMk where
  kind : RowKind
  terms : List TermMk
  units : List UnitMk
  runs : List RunMk
  forms : List MainMk

/-- A row on a group: its make. d: the size of the vector on the mask table. -/
structure GroupMk where
  group : Nat
  c : FormSh
  kept : List (Nat × FormSh)
  d : Nat

def termMk (t : Term) : TermMk := ⟨t.oracle, t.part, tensorSh t.v⟩
def unitMk (u : Single) : UnitMk := ⟨u.oracle, u.part, u.index⟩
def runMk (w : Run) : RunMk := ⟨w.oracle, w.part, w.first, w.step, w.coeffs.size⟩
def mainMk (f : MainForm) : MainMk := ⟨f.oracle, formSh f.c⟩
def rowMk (r : Row) : RowMk :=
  ⟨r.kind, r.terms.toList.map termMk, r.units.toList.map unitMk, r.runs.toList.map runMk,
    r.forms.toList.map mainMk⟩
def keptMk (k : KeptForm) : Nat × FormSh := (k.oracle, formSh k.c)
def groupMk (a : GroupRow) : GroupMk := ⟨a.group, formSh a.c, a.kept.toList.map keptMk, a.d.size⟩

/-! ## 2 The kept forms -/

/-- onKept on makes. -/
def onKeptS (kept : List (Nat × FormSh)) (o : Nat) (f : FormSh → FormSh) : List (Nat × FormSh) :=
  match kept.findIdx? (·.1 == o) with
  | some i => modAt kept i fun x => (x.1, f x.2)
  | none => kept.filter (·.1 < o) ++ [(o, f ⟨[], []⟩)] ++ kept.filter (o < ·.1)

theorem findIdx_map {α β : Type} (g : α → β) (p : β → Bool) : ∀ (l : List α),
    (l.map g).findIdx? p = l.findIdx? (fun x => p (g x)) := by
  intro l
  rw [List.findIdx?_map]
  rfl

theorem onKept_mk (kept : Array KeptForm) (o : Nat) (f : Form → Form) (fS : FormSh → FormSh)
    (h : ∀ c, formSh (f c) = fS (formSh c)) :
    (onKept kept o f).toList.map keptMk = onKeptS (kept.toList.map keptMk) o fS := by
  unfold onKept onKeptS
  have e : kept.findIdx? (·.oracle == o) = kept.toList.findIdx? (fun x => x.oracle == o) := by
    cases kept
    simp
  rw [findIdx_map, e]
  show _ = match kept.toList.findIdx? (fun x => x.oracle == o) with
    | some i => _
    | none => _
  cases kept.toList.findIdx? (fun x => x.oracle == o) with
  | some i =>
    exact map_modify kept i _ keptMk (fun x => (x.1, fS x.2)) (fun x => by
      show (x.oracle, formSh (f x.c)) = _
      rw [h]
      rfl)
  | none =>
    simp only [Array.toList_append, Array.toList_filter, List.map_append, List.filter_map]
    show _ ++ [(o, formSh (f {}))] ++ _ = _
    rw [h]
    rfl

/-! ## 3 Four of the batching's five steps (the fifth, rowInto, is section 4's) -/

/-- Own.entryInto on makes. rb: the statement's row bits. -/
def entryIntoS (rb : Nat → Part → Nat) (L : GroupLayout) (acc : GroupMk) (o : Nat) (part : Part)
    (index : Nat) : Option GroupMk :=
  match L.members.idxOf? o with
  | none => none
  | some i =>
    match part with
    | .mask =>
      match L.maskFirst.getD i none with
      | none => none
      | some first => if groupIndex index (rb o part) first L.h < acc.d then some acc else none
    | .main =>
      if L.kept.getD i false then
        some { acc with kept := onKeptS acc.kept o fun f => f.addEntry index }
      else
        match L.mainFirst.getD i none with
        | none => none
        | some first =>
          some { acc with c := acc.c.addEntry (groupIndex index (rb o part) first L.k) }

theorem entryInto_mk (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (o : Nat)
    (part : Part) (index : Nat) (coeff : E) :
    (Own.entryInto S L x acc o part index coeff).map groupMk =
      entryIntoS S.rowBits L (groupMk acc) o part index := by
  unfold Own.entryInto entryIntoS
  cases L.members.idxOf? o with
  | none => rfl
  | some i =>
    dsimp only
    cases part with
    | mask =>
      dsimp only
      cases L.maskFirst.getD i none with
      | none => rfl
      | some first =>
        dsimp only
        show Option.map groupMk (if _ < acc.d.size then _ else none) =
          if _ < acc.d.size then _ else none
        split
        · show some (GroupMk.mk _ _ _ _) = _
          rw [Array.size_modify]
          rfl
        · rfl
    | main =>
      dsimp only
      split
      · show some (GroupMk.mk _ _ _ _) = _
        rw [onKept_mk _ _ _ (fun f => f.addEntry index) (fun c => rfl)]
        rfl
      · cases L.mainFirst.getD i none with
        | none => rfl
        | some first => rfl

/-- Own.termInto on makes. -/
def termIntoS (rb : Nat → Part → Nat) (L : GroupLayout) (acc : GroupMk) (t : TermMk) :
    Option GroupMk :=
  match L.members.idxOf? t.oracle with
  | none => none
  | some i =>
    let a := rb t.oracle t.part
    match t.part with
    | .main =>
      if L.kept.getD i false then
        some { acc with kept := onKeptS acc.kept t.oracle fun f => f.add t.v }
      else
        match L.mainFirst.getD i none with
        | none => none
        | some _ =>
          if L.k < a then none
          else some { acc with c := acc.c.add (t.v.insertChoice a (L.k - a)) }
    | .mask =>
      match L.maskFirst.getD i none with
      | none => none
      | some _ => if L.h < a then none else some acc

theorem termInto_mk (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (t : Term) :
    (Own.termInto S L x acc t).map groupMk = termIntoS S.rowBits L (groupMk acc) (termMk t) := by
  unfold Own.termInto termIntoS
  show Option.map groupMk (match L.members.idxOf? t.oracle with
    | none => none
    | some i => _) = match L.members.idxOf? t.oracle with
    | none => none
    | some i => _
  cases L.members.idxOf? t.oracle with
  | none => rfl
  | some i =>
    obtain ⟨o, part, v⟩ := t
    dsimp only [termMk]
    cases part with
    | main =>
      dsimp only
      split
      · show some (GroupMk.mk _ _ _ _) = _
        rw [onKept_mk _ _ _ (fun f => f.add (tensorSh v))
          (fun c => by rw [formSh_add, tensorSh_scale])]
        rfl
      · cases L.mainFirst.getD i none with
        | none => rfl
        | some first =>
          dsimp only
          split
          · rfl
          · show some (GroupMk.mk _ _ _ _) = _
            rw [formSh_add, tensorSh_insertChoice, tensorSh_scale]
            rfl
    | mask =>
      dsimp only
      cases L.maskFirst.getD i none with
      | none => rfl
      | some first =>
        dsimp only
        split
        · rfl
        · show some (GroupMk.mk _ _ _ _) = _
          rw [Tensor.addTo_size]
          rfl

/-- A loop that may refuse, seen through a reader. -/
theorem foldlM_mk {α β ι κ : Type} (sh : α → β) (k : ι → κ) (f : α → ι → Option α)
    (fS : β → κ → Option β) (h : ∀ a i, (f a i).map sh = fS (sh a) (k i)) :
    ∀ (l : List ι) (a : α), (l.foldlM f a).map sh = (l.map k).foldlM fS (sh a)
  | [], _ => rfl
  | i :: l, a => by
    rw [List.foldlM_cons, List.map_cons, List.foldlM_cons, ← h]
    cases f a i with
    | none => rfl
    | some a' => exact foldlM_mk sh k f fS h l a'

/-- Own.runInto on makes. -/
def runIntoS (rb : Nat → Part → Nat) (L : GroupLayout) (acc : GroupMk) (w : RunMk) :
    Option GroupMk :=
  (List.range w.size).foldlM (fun acc j =>
    entryIntoS rb L acc w.oracle w.part (w.first + w.step * j)) acc

theorem runInto_mk (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (w : Run) :
    (Own.runInto S L x acc w).map groupMk = runIntoS S.rowBits L (groupMk acc) (runMk w) := by
  unfold Own.runInto runIntoS
  have := foldlM_mk groupMk id
    (fun acc j => Own.entryInto S L x acc w.oracle w.part (w.first + w.step * j) (w.coeffs.get j))
    (fun acc j => entryIntoS S.rowBits L acc w.oracle w.part (w.first + w.step * j))
    (fun a j => entryInto_mk S L x a _ _ _ _) (List.range w.coeffs.size) acc
  rw [List.map_id] at this
  exact this

/-- Own.formInto on makes. -/
def formIntoS (rb : Nat → Part → Nat) (L : GroupLayout) (acc : GroupMk) (f : MainMk) :
    Option GroupMk :=
  match L.members.idxOf? f.oracle with
  | none => none
  | some i =>
    if L.kept.getD i false then
      some { acc with kept := onKeptS acc.kept f.oracle fun c => c.plus f.c }
    else
      let a := rb f.oracle .main
      match L.mainFirst.getD i none with
      | none => none
      | some first =>
        if L.k < a then none
        else some { acc with c := acc.c.plus (f.c.insertChoice a (L.k - a) (first / 2 ^ a)) }

theorem formInto_mk (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (f : MainForm) :
    (Own.formInto S L x acc f).map groupMk = formIntoS S.rowBits L (groupMk acc) (mainMk f) := by
  unfold Own.formInto formIntoS
  show Option.map groupMk (match L.members.idxOf? f.oracle with
    | none => none
    | some i => _) = match L.members.idxOf? f.oracle with
    | none => none
    | some i => _
  cases L.members.idxOf? f.oracle with
  | none => rfl
  | some i =>
    dsimp only [mainMk]
    split
    · show some (GroupMk.mk _ _ _ _) = _
      rw [onKept_mk _ _ _ (fun c => c.plus (formSh f.c)) (fun c => formSh_addForm c f.c x)]
      rfl
    · cases L.mainFirst.getD i none with
      | none => rfl
      | some first =>
        dsimp only
        split
        · rfl
        · show some (GroupMk.mk _ _ _ _) = _
          rw [formSh_addForm, formSh_insertChoice]
          rfl

/-! ## 4 A whole row into a group's row -/

def GroupMk.ready (acc : GroupMk) (L : GroupLayout) : GroupMk :=
  if acc.d == 0 then { acc with d := 2 ^ (L.h + L.logEllZk) } else acc

theorem ready_mk (acc : GroupRow) (L : GroupLayout) :
    groupMk (acc.ready L) = (groupMk acc).ready L := by
  unfold GroupRow.ready GroupMk.ready
  by_cases h : acc.d.size = 0
  · have h1 : acc.d.isEmpty = true := by simp [Array.isEmpty, h]
    have h2 : ((groupMk acc).d == 0) = true := by
      show (acc.d.size == 0) = true
      simp [h]
    rw [if_pos h1, if_pos h2]
    show GroupMk.mk _ _ _ _ = _
    rw [Array.size_replicate]
    rfl
  · have h1 : ¬ acc.d.isEmpty = true := by simp [Array.isEmpty, h]
    have h2 : ¬ ((groupMk acc).d == 0) = true := by
      show ¬ (acc.d.size == 0) = true
      simp [h]
    rw [if_neg h1, if_neg h2]

theorem groupMk_target (a : GroupRow) (t : E) : groupMk { a with target := t } = groupMk a := by
  cases a
  rfl

theorem bind_mk {α β γ δ : Type} (sh : α → β) (sh' : γ → δ) (o : Option α) (f : α → Option γ)
    (fS : β → Option δ) (h : ∀ a, (f a).map sh' = fS (sh a)) :
    (o.bind f).map sh' = (o.map sh).bind fS := by
  cases o with
  | none => rfl
  | some a => exact h a

/-- Own.rowInto on makes. -/
def rowIntoS (rb : Nat → Part → Nat) (L : GroupLayout) (row : RowMk) (acc : GroupMk) :
    Option GroupMk :=
  (row.terms.foldlM (termIntoS rb L) (acc.ready L)).bind fun acc1 =>
    (row.units.foldlM (fun acc u => entryIntoS rb L acc u.oracle u.part u.index) acc1).bind
      fun acc2 =>
        (row.runs.foldlM (runIntoS rb L) acc2).bind fun acc3 =>
          row.forms.foldlM (formIntoS rb L) acc3

theorem rowInto_mk (S : Statement) (L : GroupLayout) (row : Row) (x : E) (acc : GroupRow) :
    (Own.rowInto S L row x acc).map groupMk = rowIntoS S.rowBits L (rowMk row) (groupMk acc) := by
  have e : Own.rowInto S L row x acc =
      (row.terms.toList.foldlM (Own.termInto S L x) (acc.ready L)).bind fun acc1 =>
        (row.units.toList.foldlM (fun acc u =>
          Own.entryInto S L x acc u.oracle u.part u.index u.coeff) acc1).bind fun acc2 =>
          (row.runs.toList.foldlM (Own.runInto S L x) acc2).bind fun acc3 =>
            (row.forms.toList.foldlM (Own.formInto S L x) acc3).bind fun acc4 =>
              some { acc4 with target := maddE acc4.target x row.target } := by
    unfold Own.rowInto
    simp only [Array.foldlM_toList]
    rfl
  rw [e]
  unfold rowIntoS
  rw [bind_mk groupMk groupMk _ _ _ (fun acc1 => ?_), foldlM_mk groupMk termMk _ _
    (fun a t => termInto_mk S L x a t), ready_mk]
  · rfl
  rw [bind_mk groupMk groupMk _ _ _ (fun acc2 => ?_), foldlM_mk groupMk unitMk
    (fun acc u => Own.entryInto S L x acc u.oracle u.part u.index u.coeff)
    (fun acc u => entryIntoS S.rowBits L acc u.oracle u.part u.index)
    (fun a u => entryInto_mk S L x a u.oracle u.part u.index u.coeff)]
  · rfl
  rw [bind_mk groupMk groupMk _ _ _ (fun acc3 => ?_), foldlM_mk groupMk runMk _ _
    (fun a w => runInto_mk S L x a w)]
  · rfl
  show _ = List.foldlM (formIntoS S.rowBits L) (groupMk acc3) (row.forms.toList.map mainMk)
  rw [← foldlM_mk groupMk mainMk _ _ (fun a f => formInto_mk S L x a f)]
  cases row.forms.toList.foldlM (Own.formInto S L x) acc3 with
  | none => rfl
  | some a => exact congrArg some (groupMk_target a _)

/-! ## 5 The written-out parts, added up -/

def liesAsS (a b : RunMk) : Bool :=
  a.oracle == b.oracle && a.part == b.part && a.first == b.first && a.step == b.step &&
    a.size == b.size

theorem liesAs_mk (a b : Run) : a.liesAs b = liesAsS (runMk a) (runMk b) := rfl

theorem runMk_scaled (w : Run) (x : E) : runMk (w.scaled x) = runMk w := by
  obtain ⟨o, p, f, s, c⟩ := w
  cases c with
  | own c => simp [Run.scaled, runMk, Coeffs.size]
  | stretch v start count => simp [Run.scaled, runMk, Coeffs.size]

theorem runMk_addScaled (r w : Run) (x : E) : runMk (r.addScaled w x) = runMk r := by
  obtain ⟨o, p, f, s, c⟩ := w
  cases c with
  | own c => simp [Run.addScaled, runMk, Coeffs.size]
  | stretch v start count => simp [Run.addScaled, runMk, Coeffs.size]

/-- Row.addRunsScaled on makes: a run on the same entries as an earlier one leaves no new run. -/
def addRunsS (runs other : List RunMk) : List RunMk :=
  other.foldl (fun runs w =>
    match runs.findIdx? (liesAsS · w) with
    | some _ => runs
    | none => runs ++ [w]) runs

theorem addRuns_mk (x : E) : ∀ (other : List Run) (runs : Array Run),
    (other.foldl (fun runs w =>
      match runs.findIdx? (·.liesAs w) with
      | some i => runs.modify i (·.addScaled w x)
      | none => runs.push (w.scaled x)) runs).toList.map runMk =
      addRunsS (runs.toList.map runMk) (other.map runMk)
  | [], _ => rfl
  | w :: other, runs => by
    unfold addRunsS
    rw [List.foldl_cons, List.map_cons, List.foldl_cons]
    refine (addRuns_mk x other _).trans ?_
    unfold addRunsS
    congr 1
    have e : runs.findIdx? (·.liesAs w) =
        (runs.toList.map runMk).findIdx? (liesAsS · (runMk w)) := by
      rw [findIdx_map]
      cases runs
      simp [liesAs_mk]
    rw [e]
    cases (runs.toList.map runMk).findIdx? (liesAsS · (runMk w)) with
    | some i =>
      dsimp only
      rw [map_modify runs i _ runMk id (fun r => runMk_addScaled r w x)]
      unfold modAt
      simp
    | none =>
      dsimp only
      rw [Array.toList_push, List.map_append, List.map_cons, runMk_scaled]
      rfl

/-- Row.addScaled on makes. -/
def RowMk.addScaled (r other : RowMk) : RowMk :=
  { r with
    terms := r.terms ++ other.terms, units := r.units ++ other.units
    runs := addRunsS r.runs other.runs, forms := r.forms ++ other.forms }

theorem addScaled_mk (r other : Row) (x : E) :
    rowMk (r.addScaled other x) = (rowMk r).addScaled (rowMk other) := by
  have hr := addRuns_mk x other.runs.toList r.runs
  rw [Array.foldl_toList] at hr
  have ht : (r.terms ++ other.terms.map fun (t : Term) =>
      ({ t with v := t.v.scale x } : Term)).toList.map termMk =
      r.terms.toList.map termMk ++ other.terms.toList.map termMk := by
    rw [Array.toList_append, Array.toList_map, List.map_append, List.map_map]
    refine congrArg (r.terms.toList.map termMk ++ ·) ?_
    apply List.map_congr_left
    intro t _
    show TermMk.mk t.oracle t.part (tensorSh (t.v.scale x)) =
      TermMk.mk t.oracle t.part (tensorSh t.v)
    rw [tensorSh_scale]
  have hu : (r.units ++ other.units.map fun (u : Single) =>
      ({ u with coeff := mulE u.coeff x } : Single)).toList.map unitMk =
      r.units.toList.map unitMk ++ other.units.toList.map unitMk := by
    rw [Array.toList_append, Array.toList_map, List.map_append, List.map_map]
    refine congrArg (r.units.toList.map unitMk ++ ·) ?_
    apply List.map_congr_left
    intro u _
    show UnitMk.mk u.oracle u.part u.index = UnitMk.mk u.oracle u.part u.index
    rfl
  have hf : (r.forms ++ other.forms.map fun (f : MainForm) =>
      ({ f with c := f.c.scale x } : MainForm)).toList.map mainMk =
      r.forms.toList.map mainMk ++ other.forms.toList.map mainMk := by
    rw [Array.toList_append, Array.toList_map, List.map_append, List.map_map]
    refine congrArg (r.forms.toList.map mainMk ++ ·) ?_
    apply List.map_congr_left
    intro f _
    show MainMk.mk f.oracle (formSh (f.c.scale x)) = MainMk.mk f.oracle (formSh f.c)
    rw [formSh_scale]
  show RowMk.mk r.kind _ _ _ _ = RowMk.mk r.kind _ _ _ _
  exact congr (congr (congr (congrArg (RowMk.mk r.kind) ht) hu) hr) hf

/-! ## 6 The batching -/

/-- Own.batch on makes. -/
def batchS (rb : Nat → Part → Nat) (g : Nat) (L : GroupLayout) (rows : List RowMk) :
    Option GroupMk :=
  (rows.foldlM (fun (s : GroupMk × RowMk) r =>
    (rowIntoS rb L { r with units := [], runs := [] } s.1).map fun acc =>
      (acc, s.2.addScaled ⟨.plain, [], r.units, r.runs, []⟩))
    (⟨g, ⟨[], []⟩, [], 0⟩, ⟨.plain, [], [], [], []⟩)).bind fun s => rowIntoS rb L s.2 s.1

/-- **The batching returns just where its step on makes returns, and the make of what it returns is
the step's value.** -/
theorem batch_mk (S : Statement) (g : Nat) (input : RunInput) (x : E) :
    (Own.batch S g input x).map groupMk =
      batchS S.rowBits g input.layout (input.rows.toList.map rowMk) := by
  have e : Own.batch S g input x =
      (input.rows.toList.foldlM (fun (s : GroupRow × Row × E) r =>
        (Own.rowInto S input.layout { r with units := #[], runs := #[] } s.2.2 s.1).bind fun acc =>
          some (acc, s.2.1.addScaled { units := r.units, runs := r.runs } s.2.2, mulE s.2.2 x))
        (({ group := g }, {}, oneE) : GroupRow × Row × E)).bind fun s =>
          Own.rowInto S input.layout s.2.1 oneE s.1 := by
    unfold Own.batch
    simp only [Array.foldlM_toList]
    rfl
  rw [e]
  unfold batchS
  rw [bind_mk (fun (s : GroupRow × Row × E) => (groupMk s.1, rowMk s.2.1)) groupMk _ _
    (fun s => rowIntoS S.rowBits input.layout s.2 s.1)
    (fun s => rowInto_mk S input.layout s.2.1 oneE s.1)]
  rw [foldlM_mk (fun (s : GroupRow × Row × E) => (groupMk s.1, rowMk s.2.1)) rowMk _
    (fun (s : GroupMk × RowMk) r =>
      (rowIntoS S.rowBits input.layout { r with units := [], runs := [] } s.1).map fun acc =>
        (acc, s.2.addScaled ⟨.plain, [], r.units, r.runs, []⟩))
    (fun s r => ?_)]
  · rfl
  · have hh := rowInto_mk S input.layout { r with units := #[], runs := #[] } s.2.2 s.1
    have hm : rowMk { r with units := #[], runs := #[] } =
        { rowMk r with units := [], runs := [] } := rfl
    rw [hm] at hh
    dsimp only
    rw [← hh]
    cases Own.rowInto S input.layout { r with units := #[], runs := #[] } s.2.2 s.1 with
    | none => rfl
    | some acc =>
      show some (groupMk acc, rowMk (s.2.1.addScaled { units := r.units, runs := r.runs } s.2.2)) =
        _
      rw [addScaled_mk]
      rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.rowInto_mk
#print axioms VerifiableInference.Desc.First.Shape.addScaled_mk
#print axioms VerifiableInference.Desc.First.Shape.batch_mk
#print axioms VerifiableInference.Desc.First.Shape.onKept_mk
#print axioms VerifiableInference.Desc.First.Shape.entryInto_mk
#print axioms VerifiableInference.Desc.First.Shape.termInto_mk
#print axioms VerifiableInference.Desc.First.Shape.runInto_mk
#print axioms VerifiableInference.Desc.First.Shape.formInto_mk
