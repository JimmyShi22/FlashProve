-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/WipeGround.lean: how the ground functions of the description
(Johnson/Desc/First/Base/Ground.lean: each a test in named clauses and an effect) behave at a wiped statement. Four
definitions with code, one of type Prop; the rest are theorems.

Words. To wipe a statement (`wipeSt`, Honest/K10/StAtZero.lean) is to set the target of every row in it to zero;
`wipeRow` does so to one row, and `wipeD` (Wipe/WipeLaws.lean) to the statement in the record that the effects carry.

What is proved, for the functions 1 to 10 of that file.
  4  `…L_wipe`   each test's list of clauses is the same list at a statement and at that statement wiped: so the verdict
                and the name of the first clause that fails are the same (`rowL_wipe`: at a row and at that row wiped;
                `admitL_wipe`: at any two arrays of rows of the same size)
  5  `…P_wipe`   each effect, at the wiped record (and at wiped rows, where it is handed rows), yields nothing where it
                yields nothing at the record, and else that value wiped
  6  `…P_rel`    so at two records that are equal once wiped, and at rows that differ in their targets alone, the two
                effects both yield nothing or yield values that are equal once wiped
  7  `GroundWipe`, `groundG_wipe`, `groundR_wipe`   the laws of 5, said of a record of the seven ground functions
                (Johnson/Desc/Ground/Calls.lean) and shown of the description's own record, under both of its names
On the way (2, 3): the same for `withGroup`, `stSent`, `admitted`, `withMessageInGroup`, `withRow`.

By what. Each body is unfolded; the test goes by its law of 4; the effect by a law on a change at one place of an array
(`map_modify_comm`, Honest/K10/BatWipe.lean), on a push or on an append.

Limits. The functions 11 and 12 of that file (messages of another chain) are not treated. The laws hold at all
arguments; they say nothing of what a statement or a row means. No member of a chain is named here. No property of the
protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeLaws
import Johnson.Desc.Ground.Calls
import Johnson.Desc.Ground.Record

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement Oracle Row RunInput OracleNotice)
open OnBytes.Slice (stSent admitted withMessageInGroup withRow closeLedgers runRows begun)
open Desc.Plain (DState)
open VerifiableInference.Desc.Own (placeFits padMade treesMade layoutOf)
open VerifiableInference.Desc.First.Close (onSt)
open VerifiableInference.Desc.Ground (ok has newGroupL withGroup newGroupP recvL recvP admitL admitP joinL joinP rowL
  addRowP rowsL addRowsFrom addRowsP takeMaskL takeMaskP takeMasksInto takeMasksP closeLedgerL closeLedgerP
  spendAsMaskL spendAsMaskP beginRunL beginRunP)

variable {L : Type}

/-! ## 1 General laws -/

/-- Where two tests are equal and p' is the image of p under a map, `if b' then p' else none` is the image of `if b
then p else none`. -/
theorem guard_map {α β : Type} (φ : α → β) {b b' : Bool} {p : Option α} {p' : Option β} (hb : b' = b)
    (hp : p' = p.map φ) : (if b' = true then p' else none) = (if b = true then p else none).map φ := by
  subst hb hp
  cases b' <;> rfl

/-- A clause on a value that is there is the test at that value. -/
theorem has_some {α : Type} (a : α) (f : α → Bool) : has (some a) f = f a := rfl

/-- A clause on the image of a value that is there is the test at the image. -/
theorem has_map_some {α : Type} (F : α → α) (a : α) (f : α → Bool) : has ((some a).map F) f = f (F a) := rfl

/-! ## 2 The wiping of a statement and of the carried record, piece by piece -/

/-- The wiped statement has the same codes. -/
theorem wipeSt_codes (S : Statement) : (wipeSt S).codes = S.codes := rfl

/-- The wiped statement has as many groups. -/
theorem wipeSt_gsize (S : Statement) : (wipeSt S).groups.size = S.groups.size := by
  show (S.groups.map wipeGr).size = _
  rw [Array.size_map]

/-- The wiped record's statement is the record's, wiped. -/
theorem wipeD_st (d : DState L) : (wipeD d).st = wipeSt d.st := rfl

/-- The wiping leaves the record's book of trees as it is. -/
theorem wipeD_book (d : DState L) : (wipeD d).book = d.book := rfl

/-- The wiping leaves the record's number of roots as it is. -/
theorem wipeD_roots (d : DState L) : (wipeD d).roots = d.roots := rfl

/-- A wiped statement as a carried record is the statement as a carried record, wiped. -/
theorem onSt_wipe (S : Statement) : onSt (wipeSt S) = wipeD (onSt S) := rfl

/-- A record with a new statement, wiped, is the wiped record with that statement wiped. -/
theorem some_st (d : DState L) {T T' : Statement} (h : T' = wipeSt T) :
    some ({ wipeD d with st := T' } : DState L) = (some ({ d with st := T } : DState L)).map wipeD := by
  subst h
  rfl

/-- The same for a pair of a value and such a record. -/
theorem some_pair {α : Type} (d : DState L) {n n' : α} {T T' : Statement} (hn : n' = n) (h : T' = wipeSt T) :
    some (n', ({ wipeD d with st := T' } : DState L)) =
      (some (n, ({ d with st := T } : DState L))).map (Prod.map id wipeD) := by
  subst hn h
  rfl

/-- Changing one oracle message by f and then wiping is wiping and then changing it by f', where f and f' are tied
so at every message. -/
theorem wipeSt_modifyO (S : Statement) (o : Nat) (f f' : Oracle → Oracle) (hf : ∀ x, wipeOr (f x) = f' (wipeOr x)) :
    ({ wipeSt S with oracles := (wipeSt S).oracles.modify o f' } : Statement) =
      wipeSt { S with oracles := S.oracles.modify o f } := by
  show (⟨S.codes, (S.oracles.map wipeOr).modify o f', S.groups.map wipeGr⟩ : Statement) =
    ⟨S.codes, (S.oracles.modify o f).map wipeOr, S.groups.map wipeGr⟩
  rw [map_modify_comm S.oracles o f wipeOr f' hf]

/-- Changing one group by f and then wiping is wiping and then changing it by f', where f and f' are tied so at
every group. -/
theorem wipeSt_modifyG (S : Statement) (g : Nat) (f f' : OnBytes.Group → OnBytes.Group)
    (hf : ∀ G, wipeGr (f G) = f' (wipeGr G)) :
    ({ wipeSt S with groups := (wipeSt S).groups.modify g f' } : Statement) =
      wipeSt { S with groups := S.groups.modify g f } := by
  show (⟨S.codes, S.oracles.map wipeOr, (S.groups.map wipeGr).modify g f'⟩ : Statement) =
    ⟨S.codes, S.oracles.map wipeOr, (S.groups.modify g f).map wipeGr⟩
  rw [map_modify_comm S.groups g f wipeGr f' hf]

/-- An oracle message's ledger is the same at a statement and at that statement wiped. -/
theorem ledger_at_wipe (S : Statement) (o : Nat) :
    ((wipeSt S).oracles[o]?).bind (·.ledger) = (S.oracles[o]?).bind (·.ledger) := by
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-- An oracle message's pad is the same at a statement and at that statement wiped. -/
theorem pad_at_wipe (S : Statement) (o : Nat) :
    ((wipeSt S).oracles[o]?).map (·.pad) = (S.oracles[o]?).map (·.pad) := by
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-- An oracle message's number of main rows is the same at a statement and at that statement wiped. -/
theorem mainRows_at_wipe (S : Statement) (o : Nat) :
    ((wipeSt S).oracles[o]?).map (·.shape.mainRows) = (S.oracles[o]?).map (·.shape.mainRows) := by
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-- Wiping leaves a group without rows as it is. -/
theorem wipeGr_new (c m : Nat) : wipeGr { code := c, maskCode := m } = { code := c, maskCode := m } := by
  show ({ code := c, maskCode := m, rows := (#[] : Array Row).map wipeRow } : OnBytes.Group) =
    { code := c, maskCode := m }
  rw [Array.map_empty]

/-- Wiping leaves an oracle message without sample rows as it is. -/
theorem wipeOr_new (s : OnBytes.OracleShape) : wipeOr { shape := s } = { shape := s } := by
  show ({ shape := s, sampleRows := (#[] : Array Row).map wipeRow } : Oracle) = { shape := s }
  rw [Array.map_empty]

/-! ## 3 The effects on the statement -/

/-- Adding a group and wiping give the same statement in either order. -/
theorem withGroup_wipe (S : Statement) (c m : Nat) : withGroup (wipeSt S) c m = wipeSt (withGroup S c m) := by
  show (⟨S.codes, S.oracles.map wipeOr, (S.groups.map wipeGr).push { code := c, maskCode := m }⟩ : Statement) =
    ⟨S.codes, S.oracles.map wipeOr, (S.groups.push { code := c, maskCode := m }).map wipeGr⟩
  rw [Array.map_push, wipeGr_new]

/-- Wiping leaves the oracle messages of a prover's message, as they come in, as they are. -/
theorem sent_wipe (sent : Array OracleNotice) :
    (sent.map fun n => ({ shape := n.shape } : Oracle)).map wipeOr = sent.map fun n => { shape := n.shape } := by
  rw [Array.map_map]
  exact congrArg (fun h => sent.map h) (funext fun n : OracleNotice => wipeOr_new n.shape)

/-- Entering a prover's oracle messages and wiping give the same statement in either order. -/
theorem stSent_wipe (S : Statement) (sent : Array OracleNotice) : stSent (wipeSt S) sent = wipeSt (stSent S sent) := by
  show (⟨S.codes, S.oracles.map wipeOr ++ sent.map (fun n => ({ shape := n.shape } : Oracle)),
      S.groups.map wipeGr⟩ : Statement) =
    ⟨S.codes, (S.oracles ++ sent.map fun n => ({ shape := n.shape } : Oracle)).map wipeOr, S.groups.map wipeGr⟩
  rw [Array.map_append, sent_wipe]

/-- Entering sample rows and then wiping gives what entering the wiped rows into the wiped statement gives. -/
theorem admitted_wipe (S : Statement) (o : Nat) (s : OnBytes.OracleShape) (places : List OnBytes.PadPlace)
    (rows : Array Row) :
    admitted (wipeSt S) o s places (rows.map wipeRow) = wipeSt (admitted S o s places rows) := by
  refine wipeSt_modifyO S o _ _ ?_
  intro x
  rfl

/-- An oracle message with one more group, as `withMessageInGroup` lays it. -/
def joinO (g : Nat) (x : Oracle) : Oracle := { x with groups := x.groups ++ [g] }

/-- A group with one more member at a place, as `withMessageInGroup` lays it. -/
def joinG (n o : Nat) (kept : Bool) (G : OnBytes.Group) : OnBytes.Group :=
  { G with members := G.members.insertIdxIfInBounds n o, kept := G.kept.insertIdxIfInBounds n kept }

/-- Joining a message to a group and wiping give the same statement in either order. -/
theorem joined_wipe (S : Statement) (g o : Nat) (kept : Bool) (G : OnBytes.Group) :
    withMessageInGroup (wipeSt S) g o kept (wipeGr G) = wipeSt (withMessageInGroup S g o kept G) := by
  show (⟨S.codes, (S.oracles.map wipeOr).modify o (joinO g),
      (S.groups.map wipeGr).modify g (joinG (G.members.filter (· < o)).size o kept)⟩ : Statement) =
    ⟨S.codes, (S.oracles.modify o (joinO g)).map wipeOr,
      (S.groups.modify g (joinG (G.members.filter (· < o)).size o kept)).map wipeGr⟩
  rw [map_modify_comm S.oracles o (joinO g) wipeOr (joinO g) fun _ => rfl,
    map_modify_comm S.groups g (joinG (G.members.filter (· < o)).size o kept) wipeGr
      (joinG (G.members.filter (· < o)).size o kept) fun _ => rfl]

/-- A group with one more open row, as `withRow` lays it. -/
def pushRow (row : Row) (G : OnBytes.Group) : OnBytes.Group := { G with rows := G.rows.push row }

/-- Adding an open row to a group and then wiping gives what adding the wiped row to the wiped group gives. -/
theorem pushRow_wipe (row : Row) (G : OnBytes.Group) : wipeGr (pushRow row G) = pushRow (wipeRow row) (wipeGr G) := by
  show ({ G with rows := (G.rows.push row).map wipeRow } : OnBytes.Group) =
    { G with rows := (G.rows.map wipeRow).push (wipeRow row) }
  rw [Array.map_push]

/-- Adding an open row and then wiping gives what adding the wiped row to the wiped statement gives. -/
theorem withRow_wipe (S : Statement) (g : Nat) (row : Row) :
    withRow (wipeSt S) g (wipeRow row) = wipeSt (withRow S g row) :=
  wipeSt_modifyG S g (pushRow row) (pushRow (wipeRow row)) (pushRow_wipe row)

/-! ## 4 The tests: named clauses that read no target -/

/-- The test of a new group is the same at a statement and at that statement wiped. -/
theorem newGroupL_wipe (S : Statement) (c m : Nat) : newGroupL (wipeSt S) c m = newGroupL S c m := rfl

/-- The test of a prover's message is the same at a statement and at that statement wiped. -/
theorem recvL_wipe (S : Statement) (B : OnBytes.TreeBook) (sent : Array OracleNotice) :
    recvL (wipeSt S) B sent = recvL S B sent := by
  unfold VerifiableInference.Desc.Ground.recvL
  rw [wipeSt_size, wipeSt_codes]

/-- The test of a sample's answers reads of the rows their number alone, and is the same at a statement and at that
statement wiped. -/
theorem admitL_wipe (S : Statement) (o : Nat) {rows rows' : Array Row} (h : rows'.size = rows.size) :
    admitL (wipeSt S) o rows' = admitL S o rows := by
  unfold VerifiableInference.Desc.Ground.admitL
  rw [wipeSt_oracle_at, h]
  cases S.oracles[o]? <;> rfl

/-- The test of a joining is the same at a statement and at that statement wiped. -/
theorem joinL_wipe (S : Statement) (g o : Nat) (kept : Bool) : joinL (wipeSt S) g o kept = joinL S g o kept := by
  unfold VerifiableInference.Desc.Ground.joinL
  rw [wipeSt_group_at, wipeSt_oracle_at]
  cases S.groups[g]? <;> cases S.oracles[o]? <;> rfl

/-- Whether a summand of a row fits its place is the same at a statement and at that statement wiped. -/
theorem placeFits_wipe (S : Statement) (G : OnBytes.Group) : placeFits (wipeSt S) (wipeGr G) = placeFits S G := by
  funext o part vars index
  unfold VerifiableInference.Desc.Own.placeFits
  rw [tableThere_wipe, tableBits_wipe]
  rfl

/-- The test of a new open row is the same at a statement and a row and at both wiped. -/
theorem rowL_wipe (S : Statement) (g : Nat) (row : Row) : rowL (wipeSt S) g (wipeRow row) = rowL S g row := by
  unfold VerifiableInference.Desc.Ground.rowL
  rw [wipeSt_group_at]
  cases S.groups[g]? with
  | none => rfl
  | some G =>
    simp only [has_some, has_map_some, placeFits_wipe, tableBits_wipe, pad_at_wipe]
    rfl

/-- The test of a new open row is the same at two rows that differ in their targets alone. -/
theorem rowL_rel (S : Statement) (g : Nat) {row row' : Row} (h : wipeRow row = wipeRow row') :
    rowL S g row = rowL S g row' := by
  rw [← rowL_wipe S g row, ← rowL_wipe S g row', h]

/-- The test in front of a list of new open rows is the same at a statement and at that statement wiped. -/
theorem rowsL_wipe (S : Statement) (g : Nat) : rowsL (wipeSt S) g = rowsL S g := by
  unfold VerifiableInference.Desc.Ground.rowsL
  rw [wipeSt_group_at]
  cases S.groups[g]? <;> rfl

/-- The test of the next free mask entry is the same at a statement and at that statement wiped. -/
theorem takeMaskL_wipe (S : Statement) (o : Nat) : takeMaskL (wipeSt S) o = takeMaskL S o := by
  unfold VerifiableInference.Desc.Ground.takeMaskL
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-- The test of the shutting of a ledger is the same at a statement and at that statement wiped. -/
theorem closeLedgerL_wipe (S : Statement) (o : Nat) : closeLedgerL (wipeSt S) o = closeLedgerL S o := by
  unfold VerifiableInference.Desc.Ground.closeLedgerL
  rw [wipeSt_size]

/-- The test of the spending of a message as a mask is the same at a statement and at that statement wiped. -/
theorem spendAsMaskL_wipe (S : Statement) (o : Nat) : spendAsMaskL (wipeSt S) o = spendAsMaskL S o := by
  unfold VerifiableInference.Desc.Ground.spendAsMaskL
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-! ## 5 The effects on the carried record, at the wiped record and at wiped rows -/

/-- `newGroupP` (one more group) at the wiped record yields nothing where it yields nothing at the record, and else
that value wiped. -/
theorem newGroupP_wipe (d : DState L) (c m : Nat) :
    newGroupP (wipeD d) c m = (newGroupP d c m).map (Prod.map id wipeD) := by
  unfold VerifiableInference.Desc.Ground.newGroupP
  exact guard_map _ (congrArg ok (newGroupL_wipe d.st c m))
    (some_pair d (wipeSt_gsize d.st) (withGroup_wipe d.st c m))

/-- `recvP` (the oracle messages of one prover's message) at the wiped record yields nothing where it yields nothing
at the record, and else that value wiped. -/
theorem recvP_wipe (ft : Nat) (d : DState L) (sent : Array OracleNotice) :
    recvP ft (wipeD d) sent = (recvP ft d sent).map (Prod.map id wipeD) := by
  have hs : (wipeD d).st.oracles.size = d.st.oracles.size := wipeSt_size d.st
  have ht : stSent (wipeD d).st sent = wipeSt (stSent d.st sent) := stSent_wipe d.st sent
  unfold VerifiableInference.Desc.Ground.recvP
  refine guard_map _ (congrArg ok (recvL_wipe d.st d.book sent)) ?_
  rw [hs, ht]
  show Option.map _ (treesMade d.st.codes sent) = Option.map _ (Option.map _ (treesMade d.st.codes sent))
  cases treesMade d.st.codes sent <;> rfl

/-- `admitP` (a sample's answers are in) at the wiped record and the wiped rows yields nothing where it yields
nothing at the record, and else that value wiped. -/
theorem admitP_wipe (d : DState L) (o : Nat) (rows : Array Row) :
    admitP (wipeD d) o (rows.map wipeRow) = (admitP d o rows).map wipeD := by
  have ho : (wipeD d).st.oracles[o]? = (d.st.oracles[o]?).map wipeOr := wipeSt_oracle_at d.st o
  unfold VerifiableInference.Desc.Ground.admitP
  refine guard_map _ (congrArg ok (admitL_wipe d.st o (by rw [Array.size_map]))) ?_
  rw [ho]
  cases d.st.oracles[o]? with
  | none => rfl
  | some x =>
    show ((padMade d.st.codes x.shape).bind fun places =>
        some ({ wipeD d with st := admitted (wipeSt d.st) o x.shape places (rows.map wipeRow) } : DState L)) =
      ((padMade d.st.codes x.shape).bind fun places =>
        some ({ d with st := admitted d.st o x.shape places rows } : DState L)).map wipeD
    cases padMade d.st.codes x.shape with
    | none => rfl
    | some places => exact some_st d (admitted_wipe d.st o x.shape places rows)

/-- `joinP` (a message joins a group) at the wiped record yields nothing where it yields nothing at the record, and
else that value wiped. -/
theorem joinP_wipe (d : DState L) (g o : Nat) (kept : Bool) :
    joinP (wipeD d) g o kept = (joinP d g o kept).map wipeD := by
  have hg : (wipeD d).st.groups[g]? = (d.st.groups[g]?).map wipeGr := wipeSt_group_at d.st g
  unfold VerifiableInference.Desc.Ground.joinP
  refine guard_map _ (congrArg ok (joinL_wipe d.st g o kept)) ?_
  rw [hg]
  cases d.st.groups[g]? with
  | none => rfl
  | some G => exact some_st d (joined_wipe d.st g o kept G)

/-- `addRowP` (a new open row) at the wiped record and the wiped row yields nothing where it yields nothing at the
record, and else that value wiped. -/
theorem addRowP_wipe (d : DState L) (g : Nat) (row : Row) :
    addRowP (wipeD d) g (wipeRow row) = (addRowP d g row).map wipeD := by
  unfold VerifiableInference.Desc.Ground.addRowP
  exact guard_map _ (congrArg ok (rowL_wipe d.st g row)) (some_st d (withRow_wipe d.st g row))

/-- `addRowsFrom` (new open rows, one by one) at the wiped record and the wiped rows yields nothing where it yields
nothing at the record, and else that value wiped. -/
theorem addRowsFrom_wipe (g : Nat) : ∀ (rows : List Row) (d : DState L),
    addRowsFrom g (rows.map wipeRow) (wipeD d) = (addRowsFrom g rows d).map wipeD
  | [], _ => rfl
  | row :: l, d => by
    show (addRowP (wipeD d) g (wipeRow row)).bind (addRowsFrom g (l.map wipeRow)) =
      ((addRowP d g row).bind (addRowsFrom g l)).map wipeD
    rw [addRowP_wipe]
    cases addRowP d g row with
    | none => rfl
    | some d' => exact addRowsFrom_wipe g l d'

/-- `addRowsP` (a list of new open rows) at the wiped record and the wiped rows yields nothing where it yields
nothing at the record, and else that value wiped. -/
theorem addRowsP_wipe (d : DState L) (g : Nat) (rows : List Row) :
    addRowsP (wipeD d) g (rows.map wipeRow) = (addRowsP d g rows).map wipeD := by
  unfold VerifiableInference.Desc.Ground.addRowsP
  exact guard_map _ (congrArg ok (rowsL_wipe d.st g)) (addRowsFrom_wipe g rows d)

/-- `takeMaskP` (the next free mask entry) at the wiped record yields nothing where it yields nothing at the record,
and else that value wiped. -/
theorem takeMaskP_wipe (d : DState L) (o : Nat) :
    takeMaskP (wipeD d) o = (takeMaskP d o).map (Prod.map id wipeD) := by
  have hl : ((wipeD d).st.oracles[o]?).bind (·.ledger) = (d.st.oracles[o]?).bind (·.ledger) :=
    ledger_at_wipe d.st o
  unfold VerifiableInference.Desc.Ground.takeMaskP
  refine guard_map _ (congrArg ok (takeMaskL_wipe d.st o)) ?_
  rw [hl]
  cases (d.st.oracles[o]?).bind (·.ledger) with
  | none => rfl
  | some l =>
    refine some_pair d rfl ?_
    refine wipeSt_modifyO d.st o _ _ ?_
    intro x
    rfl

/-- `takeMasksInto` (the next free mask entries, appended to a list) at the wiped record yields nothing where it
yields nothing at the record, and else that value wiped. -/
theorem takeMasksInto_wipe (o : Nat) : ∀ (n : Nat) (d : DState L) (acc : Array Nat),
    takeMasksInto o n (wipeD d) acc = (takeMasksInto o n d acc).map (Prod.map id wipeD)
  | 0, _, _ => rfl
  | n + 1, d, acc => by
    unfold VerifiableInference.Desc.Ground.takeMasksInto
    rw [takeMaskP_wipe]
    cases takeMaskP d o with
    | none => rfl
    | some z =>
      obtain ⟨i, d'⟩ := z
      exact takeMasksInto_wipe o n d' (acc.push i)

/-- `takeMasksP` (the next free mask entries) at the wiped record yields nothing where it yields nothing at the
record, and else that value wiped. -/
theorem takeMasksP_wipe (d : DState L) (o count : Nat) :
    takeMasksP (wipeD d) o count = (takeMasksP d o count).map (Prod.map id wipeD) :=
  takeMasksInto_wipe o count d #[]

/-- `closeLedgerP` (a ledger is shut) at the wiped record yields nothing where it yields nothing at the record, and
else that value wiped. -/
theorem closeLedgerP_wipe (d : DState L) (o : Nat) :
    closeLedgerP (wipeD d) o = (closeLedgerP d o).map wipeD := by
  unfold VerifiableInference.Desc.Ground.closeLedgerP
  exact guard_map _ (congrArg ok (closeLedgerL_wipe d.st o)) (some_st d (closeLedgers_wipe [o] d.st))

/-- `spendAsMaskP` (a message becomes a mask) at the wiped record yields nothing where it yields nothing at the
record, and else that value wiped. -/
theorem spendAsMaskP_wipe (d : DState L) (o : Nat) :
    spendAsMaskP (wipeD d) o = (spendAsMaskP d o).map wipeD := by
  unfold VerifiableInference.Desc.Ground.spendAsMaskP
  refine guard_map _ (congrArg ok (spendAsMaskL_wipe d.st o)) (some_st d ?_)
  refine wipeSt_modifyO d.st o _ _ ?_
  intro x
  rfl

/-- What the beginning of a test returns, wiped: the rows and the record. -/
def wipeRun (z : RunInput × DState L) : RunInput × DState L :=
  (⟨z.1.layout, z.1.rows.map wipeRow⟩, wipeD z.2)

/-- `beginRunP` (a proximity test begins) at the wiped record yields nothing where it yields nothing at the record,
and else that value wiped. (`beginRunP_wipe`, Honest/K10/BatWipe.lean, says it of one form of record.) -/
theorem beginRunP_wipeD (d : DState L) (g : Nat) :
    beginRunP (wipeD d) g = (beginRunP d g).map wipeRun := by
  have hg : (wipeD d).st.groups[g]? = (d.st.groups[g]?).map wipeGr := wipeSt_group_at d.st g
  unfold VerifiableInference.Desc.Ground.beginRunP
  refine guard_map _ (congrArg ok (beginRunL_wipe d.st g)) ?_
  rw [hg]
  cases d.st.groups[g]? with
  | none => rfl
  | some G =>
    show some ((⟨layoutOf (wipeSt d.st) (wipeGr G), runRows (wipeSt d.st) (wipeGr G)⟩ : RunInput),
        ({ d with st := begun (wipeSt d.st) g (wipeGr G) } : DState L)) =
      some (⟨layoutOf d.st G, (runRows d.st G).map wipeRow⟩, { d with st := wipeSt (begun d.st g G) })
    rw [layoutOf_wipe, runRows_wipe, begun_wipe]

/-! ## 6 The effects at two records that are equal once wiped, and at rows that differ in their targets alone -/

/-- `newGroupP` at two records that are equal once wiped: both yield nothing, or values that are equal once wiped. -/
theorem newGroupP_rel {d d' : DState L} (h : wipeD d = wipeD d') (c m : Nat) :
    (newGroupP d c m).map (Prod.map id wipeD) = (newGroupP d' c m).map (Prod.map id wipeD) := by
  rw [← newGroupP_wipe, ← newGroupP_wipe, h]

/-- `recvP` at two records that are equal once wiped: both yield nothing, or values that are equal once wiped. -/
theorem recvP_rel {d d' : DState L} (h : wipeD d = wipeD d') (ft : Nat) (sent : Array OracleNotice) :
    (recvP ft d sent).map (Prod.map id wipeD) = (recvP ft d' sent).map (Prod.map id wipeD) := by
  rw [← recvP_wipe, ← recvP_wipe, h]

/-- `admitP` at two records that are equal once wiped, and at rows that differ in their targets alone: both yield
nothing, or values that are equal once wiped. -/
theorem admitP_rel {d d' : DState L} (h : wipeD d = wipeD d') (o : Nat) {rows rows' : Array Row}
    (hr : rows.map wipeRow = rows'.map wipeRow) :
    (admitP d o rows).map wipeD = (admitP d' o rows').map wipeD := by
  rw [← admitP_wipe, ← admitP_wipe, h, hr]

/-- `joinP` at two records that are equal once wiped: both yield nothing, or values that are equal once wiped. -/
theorem joinP_rel {d d' : DState L} (h : wipeD d = wipeD d') (g o : Nat) (kept : Bool) :
    (joinP d g o kept).map wipeD = (joinP d' g o kept).map wipeD := by
  rw [← joinP_wipe, ← joinP_wipe, h]

/-- `addRowP` at two records that are equal once wiped, and at two rows that differ in their targets alone: both
yield nothing, or values that are equal once wiped. -/
theorem addRowP_rel {d d' : DState L} (h : wipeD d = wipeD d') (g : Nat) {row row' : Row}
    (hr : wipeRow row = wipeRow row') :
    (addRowP d g row).map wipeD = (addRowP d' g row').map wipeD := by
  rw [← addRowP_wipe, ← addRowP_wipe, h, hr]

/-- `addRowsFrom` at two records that are equal once wiped, and at rows that differ in their targets alone: both
yield nothing, or values that are equal once wiped. -/
theorem addRowsFrom_rel {d d' : DState L} (h : wipeD d = wipeD d') (g : Nat) {rows rows' : List Row}
    (hr : rows.map wipeRow = rows'.map wipeRow) :
    (addRowsFrom g rows d).map wipeD = (addRowsFrom g rows' d').map wipeD := by
  rw [← addRowsFrom_wipe, ← addRowsFrom_wipe, h, hr]

/-- `addRowsP` at two records that are equal once wiped, and at rows that differ in their targets alone: both yield
nothing, or values that are equal once wiped. -/
theorem addRowsP_rel {d d' : DState L} (h : wipeD d = wipeD d') (g : Nat) {rows rows' : List Row}
    (hr : rows.map wipeRow = rows'.map wipeRow) :
    (addRowsP d g rows).map wipeD = (addRowsP d' g rows').map wipeD := by
  rw [← addRowsP_wipe, ← addRowsP_wipe, h, hr]

/-- `takeMaskP` at two records that are equal once wiped: both yield nothing, or values that are equal once wiped. -/
theorem takeMaskP_rel {d d' : DState L} (h : wipeD d = wipeD d') (o : Nat) :
    (takeMaskP d o).map (Prod.map id wipeD) = (takeMaskP d' o).map (Prod.map id wipeD) := by
  rw [← takeMaskP_wipe, ← takeMaskP_wipe, h]

/-- `takeMasksInto` at two records that are equal once wiped: both yield nothing, or values that are equal once
wiped. -/
theorem takeMasksInto_rel {d d' : DState L} (h : wipeD d = wipeD d') (o n : Nat) (acc : Array Nat) :
    (takeMasksInto o n d acc).map (Prod.map id wipeD) = (takeMasksInto o n d' acc).map (Prod.map id wipeD) := by
  rw [← takeMasksInto_wipe, ← takeMasksInto_wipe, h]

/-- `takeMasksP` at two records that are equal once wiped: both yield nothing, or values that are equal once wiped. -/
theorem takeMasksP_rel {d d' : DState L} (h : wipeD d = wipeD d') (o count : Nat) :
    (takeMasksP d o count).map (Prod.map id wipeD) = (takeMasksP d' o count).map (Prod.map id wipeD) := by
  rw [← takeMasksP_wipe, ← takeMasksP_wipe, h]

/-- `closeLedgerP` at two records that are equal once wiped: both yield nothing, or values that are equal once
wiped. -/
theorem closeLedgerP_rel {d d' : DState L} (h : wipeD d = wipeD d') (o : Nat) :
    (closeLedgerP d o).map wipeD = (closeLedgerP d' o).map wipeD := by
  rw [← closeLedgerP_wipe, ← closeLedgerP_wipe, h]

/-- `spendAsMaskP` at two records that are equal once wiped: both yield nothing, or values that are equal once
wiped. -/
theorem spendAsMaskP_rel {d d' : DState L} (h : wipeD d = wipeD d') (o : Nat) :
    (spendAsMaskP d o).map wipeD = (spendAsMaskP d' o).map wipeD := by
  rw [← spendAsMaskP_wipe, ← spendAsMaskP_wipe, h]

/-- `beginRunP` at two records that are equal once wiped: both yield nothing, or values that are equal once wiped. -/
theorem beginRunP_rel {d d' : DState L} (h : wipeD d = wipeD d') (g : Nat) :
    (beginRunP d g).map wipeRun = (beginRunP d' g).map wipeRun := by
  rw [← beginRunP_wipeD, ← beginRunP_wipeD, h]

/-! ## 7 The record of the seven ground functions -/

/-- **A record of ground functions whose effects at the wiped record are their effects wiped**: a field for each
function, in the form of section 5. -/
structure GroundWipe (G : _root_.Desc.Plain.Ground L) : Prop where
  newGroup : ∀ p d c m, G.newGroup p (wipeD d) c m = (G.newGroup p d c m).map (Prod.map id wipeD)
  recv : ∀ p d sent, G.recv p (wipeD d) sent = (G.recv p d sent).map (Prod.map id wipeD)
  admit : ∀ p d o (rows : Array Row), G.admit p (wipeD d) o (rows.map wipeRow) = (G.admit p d o rows).map wipeD
  join : ∀ p d g o kept, G.join p (wipeD d) g o kept = (G.join p d g o kept).map wipeD
  addRow : ∀ p d g row, G.addRow p (wipeD d) g (wipeRow row) = (G.addRow p d g row).map wipeD
  addRows : ∀ p d g (rows : List Row), G.addRows p (wipeD d) g (rows.map wipeRow) = (G.addRows p d g rows).map wipeD
  takeMask : ∀ p d o, G.takeMask p (wipeD d) o = (G.takeMask p d o).map (Prod.map id wipeD)

/-- The description's own record of the seven ground functions is such a record. -/
theorem groundG_wipe : GroundWipe (_root_.Desc.Plain.groundG : _root_.Desc.Plain.Ground L) where
  newGroup := fun _ d c m => newGroupP_wipe d c m
  recv := fun p d sent => recvP_wipe p.firstTree d sent
  admit := fun _ d o rows => admitP_wipe d o rows
  join := fun _ d g o kept => joinP_wipe d g o kept
  addRow := fun _ d g row => addRowP_wipe d g row
  addRows := fun _ d g rows => addRowsP_wipe d g rows
  takeMask := fun _ d o => takeMaskP_wipe d o

/-- So is the record of the same seven under its second name (Johnson/Desc/Ground/Record.lean). -/
theorem groundR_wipe : GroundWipe (VerifiableInference.Desc.Ground.groundG : _root_.Desc.Plain.Ground L) where
  newGroup := fun _ d c m => newGroupP_wipe d c m
  recv := fun p d sent => recvP_wipe p.firstTree d sent
  admit := fun _ d o rows => admitP_wipe d o rows
  join := fun _ d g o kept => joinP_wipe d g o kept
  addRow := fun _ d g row => addRowP_wipe d g row
  addRows := fun _ d g rows => addRowsP_wipe d g rows
  takeMask := fun _ d o => takeMaskP_wipe d o

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.guard_map
#print axioms ProofFile.Honest.K10.has_some
#print axioms ProofFile.Honest.K10.has_map_some
#print axioms ProofFile.Honest.K10.wipeSt_codes
#print axioms ProofFile.Honest.K10.wipeSt_gsize
#print axioms ProofFile.Honest.K10.wipeD_st
#print axioms ProofFile.Honest.K10.wipeD_book
#print axioms ProofFile.Honest.K10.wipeD_roots
#print axioms ProofFile.Honest.K10.onSt_wipe
#print axioms ProofFile.Honest.K10.some_st
#print axioms ProofFile.Honest.K10.some_pair
#print axioms ProofFile.Honest.K10.wipeSt_modifyO
#print axioms ProofFile.Honest.K10.wipeSt_modifyG
#print axioms ProofFile.Honest.K10.ledger_at_wipe
#print axioms ProofFile.Honest.K10.pad_at_wipe
#print axioms ProofFile.Honest.K10.mainRows_at_wipe
#print axioms ProofFile.Honest.K10.wipeGr_new
#print axioms ProofFile.Honest.K10.wipeOr_new
#print axioms ProofFile.Honest.K10.withGroup_wipe
#print axioms ProofFile.Honest.K10.sent_wipe
#print axioms ProofFile.Honest.K10.stSent_wipe
#print axioms ProofFile.Honest.K10.admitted_wipe
#print axioms ProofFile.Honest.K10.joinO
#print axioms ProofFile.Honest.K10.joinG
#print axioms ProofFile.Honest.K10.joined_wipe
#print axioms ProofFile.Honest.K10.pushRow
#print axioms ProofFile.Honest.K10.pushRow_wipe
#print axioms ProofFile.Honest.K10.withRow_wipe
#print axioms ProofFile.Honest.K10.newGroupL_wipe
#print axioms ProofFile.Honest.K10.recvL_wipe
#print axioms ProofFile.Honest.K10.admitL_wipe
#print axioms ProofFile.Honest.K10.joinL_wipe
#print axioms ProofFile.Honest.K10.placeFits_wipe
#print axioms ProofFile.Honest.K10.rowL_wipe
#print axioms ProofFile.Honest.K10.rowL_rel
#print axioms ProofFile.Honest.K10.rowsL_wipe
#print axioms ProofFile.Honest.K10.takeMaskL_wipe
#print axioms ProofFile.Honest.K10.closeLedgerL_wipe
#print axioms ProofFile.Honest.K10.spendAsMaskL_wipe
#print axioms ProofFile.Honest.K10.newGroupP_wipe
#print axioms ProofFile.Honest.K10.recvP_wipe
#print axioms ProofFile.Honest.K10.admitP_wipe
#print axioms ProofFile.Honest.K10.joinP_wipe
#print axioms ProofFile.Honest.K10.addRowP_wipe
#print axioms ProofFile.Honest.K10.addRowsFrom_wipe
#print axioms ProofFile.Honest.K10.addRowsP_wipe
#print axioms ProofFile.Honest.K10.takeMaskP_wipe
#print axioms ProofFile.Honest.K10.takeMasksInto_wipe
#print axioms ProofFile.Honest.K10.takeMasksP_wipe
#print axioms ProofFile.Honest.K10.closeLedgerP_wipe
#print axioms ProofFile.Honest.K10.spendAsMaskP_wipe
#print axioms ProofFile.Honest.K10.wipeRun
#print axioms ProofFile.Honest.K10.beginRunP_wipeD
#print axioms ProofFile.Honest.K10.newGroupP_rel
#print axioms ProofFile.Honest.K10.recvP_rel
#print axioms ProofFile.Honest.K10.admitP_rel
#print axioms ProofFile.Honest.K10.joinP_rel
#print axioms ProofFile.Honest.K10.addRowP_rel
#print axioms ProofFile.Honest.K10.addRowsFrom_rel
#print axioms ProofFile.Honest.K10.addRowsP_rel
#print axioms ProofFile.Honest.K10.takeMaskP_rel
#print axioms ProofFile.Honest.K10.takeMasksInto_rel
#print axioms ProofFile.Honest.K10.takeMasksP_rel
#print axioms ProofFile.Honest.K10.closeLedgerP_rel
#print axioms ProofFile.Honest.K10.spendAsMaskP_rel
#print axioms ProofFile.Honest.K10.beginRunP_rel
#print axioms ProofFile.Honest.K10.GroundWipe
#print axioms ProofFile.Honest.K10.groundG_wipe
#print axioms ProofFile.Honest.K10.groundR_wipe
