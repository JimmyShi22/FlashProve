-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ground/Shape/More.lean: TWO MORE OF THE GROUND's FUNCTIONS, THE COUNT OF AN OPENING,
AND WHAT THE TEST ON A NEW ROW's SUMMANDS READS, ON SHAPES. Beside
Johnson/Desc/Ground/Shape/Core.lean and Ground.lean. It stands over the library's ground alone: no
kind, no chain, no frame for an honest side.

  1  `tableBitsS`, `placeFitsS`   a table's index bits, and "a summand fits its place", off the
      shape, with their equations to the library's.
  2  `rowRestS`   THE FIVE CLAUSES OF THE ADDING THAT READ A ROW's SUMMANDS (`rowRestB`,
      Ground.lean) READ THE STATEMENT THROUGH THE SHAPE ALONE: `rowRestS_eq`. They do not read the
      group's open rows: `rowRestS_kinds`, `rowRestB_withRow`.
  3  `addRowsS`   rows added one behind the other, with the two guards that are asked also at the
      empty list (`addRowsP`). carries: from the accept alone. returns: each row passes `rowRestB`
      AT THE STATEMENT IN FRONT.
  4  `takeMasksS`   the next free mask entries (`takeMasksP`), with the two laws.
  5  `countB`, `countS`   an opening is counted in the book (lists + 1): the update on shapes, with
      its law at the written term (`countB_sh`, `count_sh`). That term stands to the letter in each
      of the library's texts that count an opening.
     `openB`, `openG`   four guards on the structure as one Bool, at statement and books (`openB`)
      and on shapes (`openG`), with the equation between the two (`openG_eq`). They are the four
      that ONE of the library's texts asks at one tree (`openOne`,
      Johnson/Desc/First/Base/Meanwhile.lean, and its like in Johnson/Top/H0/Tw/L9/Switch.lean). NO
      LAW HERE TIES `openB` TO A TEXT.
  6  `X_frame`   each of the thirteen functions of the ground whose names end in P leaves the
      carried state's local part and its opened columns as they are: for whoever lays a shape of
      the local part beside the core's.

A READING OF OPENED COLUMNS IS NOT YET ON SHAPES: only its count, and one text's four guards at one
tree. The reading that calls `openOne` has two more guards on the structure (each message asked for
has a place in the book; the messages asked for are all that their trees hold) and chooses the
trees; none of that is here. The proximity test's last part counts an opening behind OTHER guards
(`lastTree`, Johnson/Desc/K12/JoinGuarded.lean: the tree's parts, number, depths and widths; it has not
been opened). So a reading's accept is NOT `openB` and a test on the columns.

THE THIRTEEN AND THE COUNT ARE NOT ALL THAT WRITES THE THREE EITHER. Two texts of the library mark
a message as spent in their own words, behind guards of their own (Johnson/Desc/K12/JoinGuarded.lean;
Johnson/Desc/First/Base/Meanwhile.lean). Statement, book and count are copied from one structure
into another (Johnson/Desc/K14/Blocks.lean, Johnson/Desc/Link/LinkDesc.lean,
Johnson/Desc/Key/Chain1.lean). The structure inside a proximity test is no carried state of the
ground: no law of these files speaks of it (for that: Johnson/Desc/K12/Honest/Shape/TestCore.lean).

ON Core.lean's AND Ground.lean's HEADS.
  · Ground.lean's eleven are not all that writes the three: see above.
  · "None holds a field element" is a reading of the types, no Lean statement: a test by type that
    admits only numbers, Bools, strings, lists, pairs and options cannot be shown at `CoreSh`,
    which is built of structures and arrays.

On names. In `countB` the B is the book's shape; in `openB`, `rowRestB` (and `stTidyB`, `stPlainB`,
Marks.lean) it marks a Bool at the statement, not on shapes.

Limits. `addRows_returns` asks `rowRestB` of each row; that the rows which a sub-protocol makes
pass it is owed where they are made. Nothing is evaluated here. Nothing on completeness, on
soundness or on what is hidden.


-/
import Johnson.Desc.Ground.Shape.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground.Sh
open OnBytes OnBytes.Slice Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {L : Type}

/-! ## 1 A table's index bits; a summand's place -/

def tableBitsS (a : StSh) (o : Nat) (part : Part) : Nat :=
  match a.oracles[o]? with
  | some x => ceilLog2 (x.shape.rows part) +
      (if x.shape.rows part == 0 then 0
       else match part with
        | .main => (a.codes.base.getD x.shape.code default).logEll
        | .mask => (a.codes.mask.getD x.shape.maskCode default).logEll)
  | none => 0

theorem tableBitsS_eq (S : Statement) (o : Nat) (part : Part) :
    tableBitsS (stSh S) o part = S.tableBits o part := by
  unfold tableBitsS Statement.tableBits Statement.rowBits Statement.placeBits
  rw [orc_get]
  cases S.oracles[o]? <;> rfl

def placeFitsS (a : StSh) (G : GrpSh) (o : Nat) (part : Part) (vars index : Nat) : Bool :=
  G.members.contains o && ((a.oracles[o]?).any fun x => decide (0 < x.shape.rows part)) &&
    vars == tableBitsS a o part && decide (index < 2 ^ tableBitsS a o part)

theorem placeFitsS_eq (S : Statement) (G : OnBytes.Group) (o : Nat) (part : Part)
    (vars index : Nat) :
    placeFitsS (stSh S) (grpSh G) o part vars index = Own.placeFits S G o part vars index := by
  unfold placeFitsS Own.placeFits Own.tableThere
  rw [tableBitsS_eq, orc_get]
  congr 3
  · show G.members.toList.contains o = _
    rw [Array.contains_toList]
  · cases S.oracles[o]? <;> rfl

/-! ## 2 The five clauses on a new row's summands -/

/-- The five clauses, with the statement read off its shape. -/
def rowRestS (a : StSh) (g : Nat) (row : OnBytes.Row) : Bool :=
  has a.groups[g]? fun G =>
    (row.terms.all fun t =>
      Own.tensorInOrder t.v && placeFitsS a G t.oracle t.part t.v.vars 0) &&
    (row.units.all fun u =>
      placeFitsS a G u.oracle u.part (tableBitsS a u.oracle u.part) u.index) &&
    (row.runs.all fun w =>
      Own.coeffsInside w.coeffs && decide (0 < w.coeffs.size) && decide (1 ≤ w.step) &&
        placeFitsS a G w.oracle w.part (tableBitsS a w.oracle w.part)
          (w.first + w.step * (w.coeffs.size - 1))) &&
    (row.forms.all fun f =>
      placeFitsS a G f.oracle .main (tableBitsS a f.oracle .main) 0 &&
        Own.formFits f.c (tableBitsS a f.oracle .main)) &&
    (G.members.all fun o =>
      ((a.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
        Own.allZero (row.coefficient o q.1 q.2))

theorem pad_get (S : Statement) (o : Nat) :
    ((stSh S).oracles[o]?).map (·.pad) = (S.oracles[o]?).map (·.pad) := by
  rw [orc_get]
  cases S.oracles[o]? <;> rfl

/-- **The five clauses read the statement through the shape alone.** -/
theorem rowRestS_eq (S : Statement) (g : Nat) (row : OnBytes.Row) :
    rowRestS (stSh S) g row = rowRestB S g row := by
  unfold rowRestS rowRestB ok rowL
  rw [grp_get]
  cases S.groups[g]? with
  | none => rfl
  | some G =>
    simp only [Option.map_some, has, Option.getD_some, placeFitsS_eq, tableBitsS_eq, pad_get,
      List.drop_succ_cons, List.drop_zero, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_assoc]
    congr 5
    show G.members.toList.all _ = _
    rw [Array.all_toList]

/-- They do not read the group's open rows. -/
theorem rowRestS_kinds (a : StSh) (g : Nat) (f : List RowKind → List RowKind)
    (row : OnBytes.Row) :
    rowRestS { a with groups := modAt a.groups g fun G => { G with kinds := f G.kinds } } g row =
      rowRestS a g row := by
  unfold rowRestS
  dsimp only
  rw [modAt_get]
  cases a.groups[g]? <;> rfl

theorem stSh_withRow (S : Statement) (g : Nat) (r : OnBytes.Row) :
    stSh (withRow S g r) = { stSh S with
      groups := modAt (stSh S).groups g fun G => { G with kinds := G.kinds ++ [r.kind] } } :=
  stSh_eq rfl rfl (map_modify _ _ _ grpSh (fun G => { G with kinds := G.kinds ++ [r.kind] })
    fun G => by
      show grpSh _ = _
      unfold grpSh
      simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil])

theorem rowRestB_withRow (S : Statement) (g : Nat) (r row : OnBytes.Row) :
    rowRestB (withRow S g r) g row = rowRestB S g row := by
  rw [← rowRestS_eq, ← rowRestS_eq, stSh_withRow]
  exact rowRestS_kinds (stSh S) g (· ++ [r.kind]) row

/-! ## 3 Rows added one behind the other -/

def addRowsFromS (g : Nat) : List RowKind → CoreSh → Option CoreSh
  | [], a => some a
  | k :: l, a => (addRowS a g k).bind (addRowsFromS g l)

/-- The two guards that are asked also at the empty list. -/
def rowsG (a : StSh) (g : Nat) : Bool := (a.groups[g]?).any fun G => !G.inRun

theorem rowsG_eq (S : Statement) (g : Nat) : rowsG (stSh S) g = ok (rowsL S g) := by
  unfold rowsG ok rowsL
  rw [grp_get]
  cases S.groups[g]? <;> simp [has, grpSh]

/-- **The adding of rows, on shapes.** kinds: the rows' kinds, in their order. -/
def addRowsS (a : CoreSh) (g : Nat) (kinds : List RowKind) : Option CoreSh :=
  if rowsG a.st g then addRowsFromS g kinds a else none

theorem addRowsFrom_carries (g : Nat) : ∀ (rows : List OnBytes.Row) (d d' : DState L),
    addRowsFrom g rows d = some d' → addRowsFromS g (rows.map (·.kind)) (shD d) = some (shD d')
  | [], d, d', h => by
    cases h
    rfl
  | r :: l, d, d', h => by
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
    show (addRowS (shD d) g r.kind).bind _ = _
    rw [addRow_carries d e g r he, Option.bind_some]
    exact addRowsFrom_carries g l e d' h

theorem addRows_carries (d d' : DState L) (g : Nat) (rows : List OnBytes.Row)
    (h : addRowsP d g rows = some d') :
    addRowsS (shD d) g (rows.map (·.kind)) = some (shD d') := by
  unfold addRowsP at h
  split at h
  · rename_i hok
    unfold addRowsS
    have hg : rowsG (shD d).st g = true := (rowsG_eq d.st g).trans hok
    rw [if_pos hg]
    exact addRowsFrom_carries g rows d d' h
  · cases h

theorem addRowsFrom_returns (g : Nat) : ∀ (rows : List OnBytes.Row) (d : DState L) (y : CoreSh),
    addRowsFromS g (rows.map (·.kind)) (shD d) = some y →
    (∀ r ∈ rows, rowRestB d.st g r = true) → ∃ d', addRowsFrom g rows d = some d'
  | [], d, _, _, _ => ⟨d, rfl⟩
  | r :: l, d, y, h, hv => by
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨d1, h1⟩ := addRow_returns d g r e he (hv r List.mem_cons_self)
    have c1 := addRow_carries d d1 g r h1
    have e1 : e = shD d1 := Option.some.inj (he.symm.trans c1)
    subst e1
    have hst : d1.st = withRow d.st g r := by
      unfold addRowP at h1
      split at h1
      · cases h1
        rfl
      · cases h1
    obtain ⟨d', h'⟩ := addRowsFrom_returns g l d1 y h fun x hx => by
      rw [hst, rowRestB_withRow]
      exact hv x (List.mem_cons_of_mem _ hx)
    refine ⟨d', ?_⟩
    show (addRowP d g r).bind _ = _
    rw [h1, Option.bind_some]
    exact h'

theorem addRows_returns (d : DState L) (g : Nat) (rows : List OnBytes.Row) (y : CoreSh)
    (h : addRowsS (shD d) g (rows.map (·.kind)) = some y)
    (hv : ∀ r ∈ rows, rowRestB d.st g r = true) : ∃ d', addRowsP d g rows = some d' := by
  unfold addRowsS at h
  split at h
  · rename_i hg
    unfold addRowsP
    rw [if_pos ((rowsG_eq d.st g).symm.trans hg)]
    exact addRowsFrom_returns g rows d y h hv
  · cases h

/-! ## 4 The next free mask entries -/

def takeMasksIntoS (o : Nat) : Nat → CoreSh → Array Nat → Option (List Nat × CoreSh)
  | 0, a, acc => some (acc.toList, a)
  | n + 1, a, acc =>
    match takeMaskS a o with
    | none => none
    | some (i, a') => takeMasksIntoS o n a' (acc.push i)

/-- **The taking of the next count free mask entries, on shapes.** -/
def takeMasksS (a : CoreSh) (o count : Nat) : Option (List Nat × CoreSh) :=
  takeMasksIntoS o count a #[]

theorem takeMasksInto_carries (o : Nat) : ∀ (n : Nat) (d d' : DState L) (acc : Array Nat)
    (l : List Nat), takeMasksInto o n d acc = some (l, d') →
    takeMasksIntoS o n (shD d) acc = some (l, shD d')
  | 0, d, d', acc, l, h => by
    cases h
    rfl
  | n + 1, d, d', acc, l, h => by
    rw [takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e he
      rw [takeMasksIntoS, takeMask_carries d e o i he]
      exact takeMasksInto_carries o n e d' _ l h

theorem takeMasks_carries (d d' : DState L) (o count : Nat) (l : List Nat)
    (h : takeMasksP d o count = some (l, d')) :
    takeMasksS (shD d) o count = some (l, shD d') :=
  takeMasksInto_carries o count d d' #[] l h

theorem takeMasksInto_returns (o : Nat) : ∀ (n : Nat) (d : DState L) (acc : Array Nat)
    (y : List Nat × CoreSh), takeMasksIntoS o n (shD d) acc = some y →
    ∃ x, takeMasksInto o n d acc = some x
  | 0, d, acc, _, _ => ⟨_, rfl⟩
  | n + 1, d, acc, y, h => by
    rw [takeMasksIntoS] at h
    split at h
    · cases h
    · rename_i i a' he
      obtain ⟨⟨i1, d1⟩, h1⟩ := takeMask_returns d o _ he
      have c1 := takeMask_carries d d1 o i1 h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (he.symm.trans c1))
      obtain ⟨x, hx⟩ := takeMasksInto_returns o n d1 _ y h
      refine ⟨x, ?_⟩
      rw [takeMasksInto, h1]
      exact hx

theorem takeMasks_returns (d : DState L) (o count : Nat) (y : List Nat × CoreSh)
    (h : takeMasksS (shD d) o count = some y) : ∃ x, takeMasksP d o count = some x :=
  takeMasksInto_returns o count d #[] y h

/-! ## 5 An opening is counted -/

/-- One more list at which a tree is opened: on the book's shape. -/
def countB (b : BookSh) (t : Nat) : BookSh :=
  { b with trees := modAt b.trees t fun x => { x with lists := x.lists + 1 } }

theorem countB_sh (B : TreeBook) (t : Nat) :
    bookSh { B with trees := B.trees.modify t fun x => { x with lists := x.lists + 1 } } =
      countB (bookSh B) t := by
  unfold countB bookSh
  dsimp only
  rw [map_modify _ _ _ treeSh (fun x => { x with lists := x.lists + 1 }) fun _ => rfl]

/-- The same on the core's shape. -/
def countS (c : CoreSh) (t : Nat) : CoreSh := { c with book := countB c.book t }

theorem count_sh (S : Statement) (B : TreeBook) (r t : Nat) :
    coreSh ⟨S, { B with trees := B.trees.modify t fun x => { x with lists := x.lists + 1 } }, r⟩ =
      countS (coreSh ⟨S, B, r⟩) t := by
  unfold countS coreSh
  dsimp only
  rw [countB_sh]

/-- The sampled parts of a tree belong to the same groups, and to one group at most if the tree is
opened at one list only. groups: for each sampled part the groups that it belongs to. -/
def sharesOk (groups : List (List Nat)) (oneList : Bool) : Bool :=
  match groups with
  | [] => true
  | a :: l => l.all (· == a) && (!oneList || decide (a.length ≤ 1))

/-- The four guards on the structure that a reading asks before it counts an opening of the tree t:
the tree is in the book as it is and as it was in front of the reading; its sampled parts belong to
the same groups, and to one group at most if it is opened at one list only; such a tree has not been
opened; it is not longer than the list's range. B: the book as it is. B0: in front. -/
def openB (S : Statement) (B B0 : TreeBook) (logN t : Nat) : Bool :=
  match B.trees[t]?, B0.trees[t]? with
  | some tree, some tree0 =>
    sharesOk (tree.parts.toList.filterMap fun o =>
        (S.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups)
      tree.oneList &&
    (!tree.oneList || tree.lists == 0) && decide (tree0.shape.logN ≤ logN)
  | _, _ => false

/-- The same on shapes. -/
def openG (a : StSh) (b b0 : BookSh) (logN t : Nat) : Bool :=
  match b.trees[t]?, b0.trees[t]? with
  | some tree, some tree0 =>
    sharesOk (tree.parts.filterMap fun o =>
        (a.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups)
      tree.oneList &&
    (!tree.oneList || tree.lists == 0) && decide (tree0.shape.logN ≤ logN)
  | _, _ => false

theorem openG_eq (S : Statement) (B B0 : TreeBook) (logN t : Nat) :
    openG (stSh S) (bookSh B) (bookSh B0) logN t = openB S B B0 logN t := by
  unfold openG openB
  rw [tree_get, tree_get]
  cases B.trees[t]? with
  | none => rfl
  | some tree =>
    cases B0.trees[t]? with
    | none => rfl
    | some tree0 =>
      have e : (fun (o : Nat) => ((stSh S).oracles[o]?).bind fun (x : OrcSh) =>
          if x.shape.answers == 0 then none else some x.groups) =
          fun (o : Nat) => (S.oracles[o]?).bind fun (x : OnBytes.Oracle) =>
            if x.shape.answers == 0 then none else some x.groups := by
        funext o
        rw [orc_get]
        cases S.oracles[o]? <;> rfl
      show (sharesOk ((treeSh tree).parts.filterMap fun (o : Nat) =>
        ((stSh S).oracles[o]?).bind fun (x : OrcSh) =>
          if x.shape.answers == 0 then none else some x.groups) _ && _ && _) = _
      rw [e]
      rfl

/-! ## 6 Each of the thirteen leaves the local part and the opened columns -/

theorem join_frame (d d' : DState L) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d') :
    d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold joinP at h
  split at h
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, rfl⟩
  · cases h

theorem addRow_frame (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') : d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold addRowP at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

theorem addRowsFrom_frame (g : Nat) : ∀ (rows : List OnBytes.Row) (d d' : DState L),
    addRowsFrom g rows d = some d' → d'.loc = d.loc ∧ d'.opened = d.opened
  | [], d, d', h => by
    cases h
    exact ⟨rfl, rfl⟩
  | r :: l, d, d', h => by
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a1, a2⟩ := addRow_frame d e g r he
    obtain ⟨b1, b2⟩ := addRowsFrom_frame g l e d' h
    exact ⟨b1.trans a1, b2.trans a2⟩

theorem addRows_frame (d d' : DState L) (g : Nat) (rows : List OnBytes.Row)
    (h : addRowsP d g rows = some d') : d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_frame g rows d d' h
  · cases h

theorem adopt_frame (d d' : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src))
    (ids : Array Nat) (h : adoptP d sent given = some (ids, d')) :
    d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold adoptP at h
  split at h
  · obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    exact ⟨rfl, rfl⟩
  · cases h

theorem recv_frame (first : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat)
    (h : recvP first d sent = some (ids, d')) : d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold recvP at h
  split at h
  · obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    exact ⟨rfl, rfl⟩
  · cases h

theorem elsewhere_frame (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') : d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold elsewhereP at h
  split at h
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, rfl⟩
  · cases h

theorem newGroup_frame (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) : d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold newGroupP at h
  split at h
  · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨rfl, rfl⟩
  · cases h

theorem takeMask_frame (d d' : DState L) (o n : Nat) (h : takeMaskP d o = some (n, d')) :
    d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj h
    exact ⟨rfl, rfl⟩
  · cases h

theorem takeMasksInto_frame (o : Nat) : ∀ (n : Nat) (d d' : DState L) (acc : Array Nat)
    (l : List Nat), takeMasksInto o n d acc = some (l, d') →
    d'.loc = d.loc ∧ d'.opened = d.opened
  | 0, d, d', acc, l, h => by
    cases h
    exact ⟨rfl, rfl⟩
  | n + 1, d, d', acc, l, h => by
    rw [takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e he
      obtain ⟨a1, a2⟩ := takeMask_frame d e o i he
      obtain ⟨b1, b2⟩ := takeMasksInto_frame o n e d' _ l h
      exact ⟨b1.trans a1, b2.trans a2⟩

theorem takeMasks_frame (d d' : DState L) (o count : Nat) (l : List Nat)
    (h : takeMasksP d o count = some (l, d')) : d'.loc = d.loc ∧ d'.opened = d.opened :=
  takeMasksInto_frame o count d d' #[] l h

theorem closeLedger_frame (d d' : DState L) (o : Nat) (h : closeLedgerP d o = some d') :
    d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold closeLedgerP at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

theorem spend_frame (d d' : DState L) (o : Nat) (h : spendAsMaskP d o = some d') :
    d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold spendAsMaskP at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

theorem admit_frame (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') : d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold admitP at h
  split at h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact ⟨rfl, rfl⟩
  · cases h

theorem beginRun_frame (d d' : DState L) (g : Nat) (run : RunInput)
    (h : beginRunP d g = some (run, d')) : d'.loc = d.loc ∧ d'.opened = d.opened := by
  unfold beginRunP at h
  split at h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨rfl, rfl⟩
  · cases h

end VerifiableInference.Desc.Ground.Sh

#print axioms VerifiableInference.Desc.Ground.Sh.tableBitsS_eq
#print axioms VerifiableInference.Desc.Ground.Sh.placeFitsS_eq
#print axioms VerifiableInference.Desc.Ground.Sh.pad_get
#print axioms VerifiableInference.Desc.Ground.Sh.rowRestS_eq
#print axioms VerifiableInference.Desc.Ground.Sh.rowRestS_kinds
#print axioms VerifiableInference.Desc.Ground.Sh.stSh_withRow
#print axioms VerifiableInference.Desc.Ground.Sh.rowRestB_withRow
#print axioms VerifiableInference.Desc.Ground.Sh.rowsG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.addRowsFrom_carries
#print axioms VerifiableInference.Desc.Ground.Sh.addRows_carries
#print axioms VerifiableInference.Desc.Ground.Sh.addRowsFrom_returns
#print axioms VerifiableInference.Desc.Ground.Sh.addRows_returns
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasksInto_carries
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasks_carries
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasksInto_returns
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasks_returns
#print axioms VerifiableInference.Desc.Ground.Sh.countB_sh
#print axioms VerifiableInference.Desc.Ground.Sh.count_sh
#print axioms VerifiableInference.Desc.Ground.Sh.openG_eq
#print axioms VerifiableInference.Desc.Ground.Sh.join_frame
#print axioms VerifiableInference.Desc.Ground.Sh.addRow_frame
#print axioms VerifiableInference.Desc.Ground.Sh.addRowsFrom_frame
#print axioms VerifiableInference.Desc.Ground.Sh.addRows_frame
#print axioms VerifiableInference.Desc.Ground.Sh.adopt_frame
#print axioms VerifiableInference.Desc.Ground.Sh.recv_frame
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_frame
#print axioms VerifiableInference.Desc.Ground.Sh.newGroup_frame
#print axioms VerifiableInference.Desc.Ground.Sh.takeMask_frame
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasksInto_frame
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasks_frame
#print axioms VerifiableInference.Desc.Ground.Sh.closeLedger_frame
#print axioms VerifiableInference.Desc.Ground.Sh.spend_frame
#print axioms VerifiableInference.Desc.Ground.Sh.admit_frame
#print axioms VerifiableInference.Desc.Ground.Sh.beginRun_frame
