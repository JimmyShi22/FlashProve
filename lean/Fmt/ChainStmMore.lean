-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ChainStmMore.lean: three byte strings, as this library writes them after the file format,
determine, under the hypotheses counted below, the values from which they are written. The hash is a
parameter h, any ordinary function of five arguments ("h under n": n is the first); no theorem here
names a fixed hash function. A chain is the non-interactive form of one protocol; its statement is
one part of `firstBytes`, the string that is hashed for its first value.
(a) A table's name (`recordStm`): a root, a digest (an argument) and the six numbers of the tables'
    shape. The library draws the seeds of a table's record from a chain with this statement.
(b) `EntryStm.bytes`: two tables, each a root and a list of answers. By its definition's comment it
    is the statement of an entry file's chain.
(c) `idString`: a digest, a name, the table's answers and two lists that are arguments. The
    library's commitment ID is h under 179 on it.
States, with smaller theorems around these:
(1) `rdRecordStm_iff`, `EntryStm.read_iff` (0 hypotheses): the reader (parser) of (a), and of (b),
    returns a value exactly on the bytes written from it, and exactly where it is well formed and,
    for (b), the bytes are fewer than 2 ^ 64.
(2) `firstBytes_record_inj` (8), `firstBytes_entry_inj` (5): two `firstBytes` with the same bytes,
    whose statements are (a), or (b), of well-formed values, have equal values and equal other
    parts.
(3) `idString_inj` (10): two (c) with the same bytes, of values with the forms under (i), are
    written from the same digest, shape, table and two lists. `Declared.idString_closed_inj` (7):
    from the same digest, shape and table, at the string on which `KeyParsed.idOkW`, the test of a
    caller's ID against a key file's table, calls h under 179.
Under (the counts leave out the equation of bytes; each theorem lists its own at its statement):
(i) Forms of the values. Roots and digests have 32 bytes. The shape's six numbers are below 2 ^ 64
    (`TableShape.wordsFit`). `TableSt.ok`: a root of 32 bytes; `TableShape.count` answers, that is 2
    ^ logRows times the shape's number `answers`; each canonical. `seedsOk`, `toldOk`: the forms of
    (c)'s two lists. "Well formed" is, for (a), the first two; for (b), `TableSt.ok` of both tables.
    In (b) and (c) both sides are under one field; in (b) also under one shape (in (2): one
    `Declared`, the library's record of what is public) with `TableShape.fitsWord`: the statement is
    shorter than 2 ^ 64 bytes.
(ii) `First.Rest` on both sides of (2): three conditions on the lengths of the other parts.
    `startChainW_rest` proves it, at the empty record, of what the library's start of a chain
    returns, if the parameters' digest has 32 bytes and (iii).
(iii) On the hash: h under 169 and under 160 returns 32 bytes (`Declared.idString_closed_inj`); h
    under 172 returns 32 bytes (`startChainW_rest`).
Does not show:
(1) No theorem of the library on a verifier uses these theorems, and that a verifier or the programs
    hash these strings is not shown here.
(2) The format page was not read for this file; rule numbers (R…) come from other files' comments.
(3) No reader is a verifier, and no verifier calls one. Nothing on soundness follows.
(4) A name fixes the root, the configuration's digest and the shape, not the answers: they are not
    in it. No theorem here relates a table's answers to its root.
(5) Of `Declared` `recordStm` reads the tables' shape alone: of the rest nothing follows. Its digest
    is an argument; nothing here says that it is the digest of `Declared`'s files.
(6) A name has no word for a length: where the root ends and the digest begins is not in the bytes.
(7) A word is written modulo 2 ^ 64: a shape without `TableShape.wordsFit` has the name of another
    shape (a test).
(8) `TableShape.wordsFit` does not give `TableShape.fitsWord` (a test).
(9) Nothing says that the two tables of (b) differ, nor where the first table comes from.
(10) Nothing about the hash: no statement here says that two calls with the same answer hash the
    same bytes. Nothing about which chain a call belongs to: a chain's label is in the call's place,
    not in these bytes. No theorem here compares a name, as a string, with a statement made of
    items.
(11) `idString_inj` speaks of the string that is hashed under 179, not of the ID. That two tables
    with one ID are one table does not follow here. Under a random oracle two different strings get
    one answer only with small probability; no bound on it is proved here.
(12) There is no reader of (c) here, and no theorem "exactly where".
(13) `KeyParsed.idOkW` does not test three things that `idString_inj` asks: that the files' digest
    has 32 bytes; `TableShape.wordsFit`; and that both sides are under one field, which a test on
    one `Declared` cannot ask.
(14) That `idString` is the format page's string is checked by tests, not by a theorem.
    `KeyParsed.idOkW` is checked at none of the page's known answers.
(15) Where the drawing of the seeds refuses, `KeyParsed.idOkW` goes on with no seeds, and
    `idString_inj` says nothing of such a string.
(16) Of `startChainW` at an h whose answers under 172 have another length nothing is said here.
Notes in full, with every limit at length, stand at the end of this file.

-/
import Fmt.ChainStmJoin
import Fmt.RecordSeedsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-! ## 1. A word as a number; a shape's six words -/

/-- One word (eight bytes, the lowest first), as a number: the library's `rdEnum` where every number
is a member. What it gives is below 2 ^ 64. -/
def rdNum : Rd Nat := rdEnum some

/-- It undoes `u64n` on the numbers below 2 ^ 64. -/
theorem undoes_num : Undoes rdNum u64n fun x => x < 2 ^ 64 :=
  fun x hx => undoes_enum id some x ⟨hx, rfl⟩

/-- What it accepts is the word of the number that it gives, and that number is below 2 ^ 64. -/
theorem cuts_num : Cuts rdNum u64n fun x => x < 2 ^ 64 :=
  cuts_of (cuts_of_only (only_enum id some fun _ _ h => (Option.some.inj h).symm)) (fun _ _ => rfl)
    (fun _ h => h.1)

/-- Each of the shape's six numbers (`TableShape.words`) is below 2 ^ 64, so that a table's name
holds it as it is and not modulo 2 ^ 64. (Another thing than `TableShape.fitsWord`,
Fmt/ChainStm.lean, which bounds the length of a statement of two tables.) -/
def TableShape.wordsFit (s : TableShape) : Bool := s.words.all fun x => decide (x < 2 ^ 64)

/-- `TableShape.wordsFit` as six inequalities. -/
theorem TableShape.wordsFit_iff (s : TableShape) :
    s.wordsFit = true ↔
      s.a < 2 ^ 64 ∧ s.message < 2 ^ 64 ∧ s.tail < 2 ^ 64 ∧ s.logRows < 2 ^ 64 ∧
        s.answers < 2 ^ 64 ∧ s.saltBytes < 2 ^ 64 := by
  simp only [TableShape.wordsFit, TableShape.words, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq]

/-- A shape within the ranges of `TableShape.ok` has `TableShape.wordsFit`: by them a is at most 60,
message and tail together at most 2 ^ 32, logRows at most 40, three times the answers less than
the message, the salt at most 64 bytes. (`Declared.settingOk`, Fmt/Parsed.lean, asks `TableShape.ok`
of the declared shape.) -/
theorem TableShape.wordsFit_of_ok (s : TableShape) (h : s.ok = true) : s.wordsFit = true := by
  simp only [TableShape.ok, saltLenOK, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [TableShape.wordsFit_iff]
  omega

/-- The six words one after the other, in the order of `TableShape.words`: 48 bytes. It is here as
the spelling in the laws of `rdShape`; that a table's name ends with these bytes:
`TableShape.name_pair`. -/
def TableShape.wordsBytes (s : TableShape) : ByteArray := cat (s.words.map u64n)

/-- Six words, as a shape, in the order of `TableShape.words`. No range is tested. -/
def rdShape : Rd TableShape :=
  rdMap (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩)
    (rdPair rdNum (rdPair rdNum (rdPair rdNum (rdPair rdNum (rdPair rdNum rdNum)))))

/-- It undoes the six words of a shape with `TableShape.wordsFit`. -/
theorem undoes_shape : Undoes rdShape TableShape.wordsBytes fun s => s.wordsFit = true :=
  undoes_map (β := TableShape)
    (undoes_pair undoes_num (undoes_pair undoes_num (undoes_pair undoes_num
      (undoes_pair undoes_num (undoes_pair undoes_num undoes_num)))))
    (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩)
    (fun s => (s.a, s.message, s.tail, s.logRows, s.answers, s.saltBytes)) (fun _ _ => rfl)
    (fun s _ => by
      simp only [TableShape.wordsBytes, TableShape.words, List.map_cons, List.map_nil, cat_cons,
        cat_nil, ByteArray.append_empty, pair])
    (fun s h => (TableShape.wordsFit_iff s).1 h)

/-- What it accepts are the six words of the shape that it gives, and that shape has
`TableShape.wordsFit`. -/
theorem cuts_shape : Cuts rdShape TableShape.wordsBytes fun s => s.wordsFit = true :=
  cuts_map (β := TableShape)
    (cuts_pair cuts_num (cuts_pair cuts_num (cuts_pair cuts_num
      (cuts_pair cuts_num (cuts_pair cuts_num cuts_num)))))
    (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩)
    (fun x _ => by
      simp only [TableShape.wordsBytes, TableShape.words, List.map_cons, List.map_nil, cat_cons,
        cat_nil, ByteArray.append_empty, pair])
    (fun x h => (TableShape.wordsFit_iff _).2 h)

/-! ## 2. The chain of a record's seeds: a table's name -/

/-- The statement of the chain of a record's seeds (R4.8): the reader of `recordStm`, that is, of a
table's name (`TableShape.name`, R4.10). 32 bytes, the root; 32 bytes, the configuration's digest;
six words, the shape; and no byte behind them. What it gives: root, digest, shape, in the bytes'
order. (The test on 2 ^ 64 bytes is made here too; what passes the others has 112 bytes.) -/
def rdRecordStm : ByteArray → Option (ByteArray × ByteArray × TableShape) :=
  wholeStm (rdPair rdDigest (rdPair rdDigest rdShape))

/-- A table's name as a pair of pairs: the root, the digest, the six words. -/
theorem TableShape.name_pair (s : TableShape) (cfg root : ByteArray) :
    s.name cfg root = pair id (pair id TableShape.wordsBytes) (root, cfg, s) := by
  simp only [TableShape.name, tableName, TableShape.wordsBytes, TableShape.words, List.map_cons,
    List.map_nil, cat_cons, cat_nil, ByteArray.append_empty, pair, id, ByteArray.append_assoc]

/-- The length of a table's name: the root's, the digest's, and 48. -/
theorem TableShape.name_size (s : TableShape) (cfg root : ByteArray) :
    (s.name cfg root).size = root.size + cfg.size + 48 := by
  simp only [TableShape.name, tableName, u64n, ByteArray.size_append, size_u64]

/-- The length of the statement of the chain of a record's seeds. -/
theorem recordStm_size (D : Declared) (cfg : ByteArray) (t : TableSt) :
    (recordStm D cfg t).size = t.root.size + cfg.size + 48 :=
  TableShape.name_size D.table cfg t.root

/-- With a root and a digest of 32 bytes it has 112 bytes: fewer than 2 ^ 64. -/
theorem recordStm_size_lt (D : Declared) (cfg : ByteArray) (t : TableSt) (hr : t.root.size = 32)
    (hc : cfg.size = 32) : (recordStm D cfg t).size < 2 ^ 64 := by
  rw [recordStm_size, hr, hc]
  decide

/-- THE CHAIN OF A RECORD's SEEDS. The reader gives root, cfg and s on b exactly where root and cfg
have 32 bytes, s has `TableShape.wordsFit`, and b is the name written of them. (It has 112 bytes
then.) -/
theorem rdRecordStm_iff (b root cfg : ByteArray) (s : TableShape) :
    rdRecordStm b = some (root, cfg, s) ↔
      (root.size = 32 ∧ cfg.size = 32 ∧ s.wordsFit = true) ∧ b = s.name cfg root := by
  have z := TableShape.name_size s cfg root
  rw [TableShape.name_pair] at z ⊢
  have h := wholeStm_both (undoes_pair undoes_digest (undoes_pair undoes_digest undoes_shape))
    (cuts_pair (cuts_of_only only_digest) (cuts_pair (cuts_of_only only_digest) cuts_shape)) b
    (root, cfg, s)
  constructor
  · intro g
    exact ⟨(h.1 g).1.1, (h.1 g).2⟩
  · rintro ⟨⟨a, c, d⟩, e⟩
    exact h.2 ⟨⟨⟨a, c, d⟩, by rw [e, z]; omega⟩, e⟩

/-- No premise. From the statement written of D, cfg and t the reader gives back t's root, cfg and
D's tables' shape exactly where the root and cfg have 32 bytes and the shape has
`TableShape.wordsFit`. -/
theorem recordStm_read (D : Declared) (cfg : ByteArray) (t : TableSt) :
    rdRecordStm (recordStm D cfg t) = some (t.root, cfg, D.table) ↔
      t.root.size = 32 ∧ cfg.size = 32 ∧ D.table.wordsFit = true := by
  rw [rdRecordStm_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/-- Asked: both roots and both digests have 32 bytes; both shapes have `TableShape.wordsFit`. The
same name is the name of the same root, the same digest and the same shape. -/
theorem TableShape.name_inj (s u : TableShape) (cfg cfg' root root' : ByteArray)
    (hr : root.size = 32) (hr' : root'.size = 32) (hc : cfg.size = 32) (hc' : cfg'.size = 32)
    (hs : s.wordsFit = true) (hu : u.wordsFit = true) (e : s.name cfg root = u.name cfg' root') :
    root = root' ∧ cfg = cfg' ∧ s = u := by
  rw [TableShape.name_pair, TableShape.name_pair] at e
  have a := inj_of_undoes (undoes_pair undoes_digest (undoes_pair undoes_digest undoes_shape))
    (root, cfg, s) (root', cfg', u) ⟨hr, hc, hs⟩ ⟨hr', hc', hu⟩ e
  exact ⟨congrArg Prod.fst a, congrArg (fun x => x.2.1) a, congrArg (fun x => x.2.2) a⟩

/-- The same at `recordStm`. Asked: both tables' roots and both digests have 32 bytes; both declared
shapes have `TableShape.wordsFit`. Two such statements that are the same bytes speak of the same
root, the same digest and the same shape. Of the answers, and of the rest of D and D', nothing
follows. -/
theorem recordStm_inj (D D' : Declared) (cfg cfg' : ByteArray) (t t' : TableSt)
    (hr : t.root.size = 32) (hr' : t'.root.size = 32) (hc : cfg.size = 32) (hc' : cfg'.size = 32)
    (hs : D.table.wordsFit = true) (hs' : D'.table.wordsFit = true)
    (e : recordStm D cfg t = recordStm D' cfg' t') :
    t.root = t'.root ∧ cfg = cfg' ∧ D.table = D'.table :=
  TableShape.name_inj D.table D'.table cfg cfg' t.root t'.root hr hr' hc hc' hs hs' e

/-- The statement does not hang on the answers. -/
theorem recordStm_answers (D : Declared) (cfg : ByteArray) (t : TableSt) (l : List Ext) :
    recordStm D cfg { t with answers := l } = recordStm D cfg t := rfl

/-! ## 3. An entry file's link: two tables' items -/

/-- The statement of an entry file's link (R13.5): the reader of `EntryStm.bytes`. The item "the
first table", then the item "the further table", each read as a table's item is (`rdTableItem`,
Fmt/ChainStmRead.lean: refused unless the table has the form `TableSt.ok` under f and s), and no
byte behind them; fewer than 2 ^ 64 bytes. What it gives: the first table, the further table. -/
def EntryStm.read (f : Fld) (s : TableShape) : ByteArray → Option (TableSt × TableSt) :=
  wholeStm (rdPair (rdTableItem "the first table" f s) (rdTableItem "the further table" f s))

/-- `EntryStm.ok` (Fmt/Parsed.lean) as two statements. -/
theorem EntryStm.ok_iff (D : Declared) (x : EntryStm) :
    x.ok D = true ↔
      x.first.ok D.setting.field D.table = true ∧ x.further.ok D.setting.field D.table = true := by
  simp only [EntryStm.ok, Bool.and_eq_true]

/-- AN ENTRY's LINK. The reader gives x's two tables on b exactly where both have the form, b has
fewer than 2 ^ 64 bytes, and b is the statement written of x. (Every pair of tables is that of some
x.) -/
theorem EntryStm.read_iff (f : Fld) (s : TableShape) (b : ByteArray) (x : EntryStm) :
    EntryStm.read f s b = some (x.first, x.further) ↔
      ((x.first.ok f s = true ∧ x.further.ok f s = true) ∧ b.size < 2 ^ 64) ∧ b = x.bytes := by
  have h := wholeStm_both
    (undoes_pair (undoes_tableItem "the first table" (by decide) (by decide) f s)
      (undoes_tableItem "the further table" (by decide) (by decide) f s))
    (cuts_pair (cuts_tableItem "the first table" f s) (cuts_tableItem "the further table" f s)) b
    (x.first, x.further)
  constructor
  · intro g
    obtain ⟨⟨⟨⟨a, -⟩, d, -⟩, c⟩, e⟩ := h.1 g
    exact ⟨⟨⟨a, d⟩, c⟩, e⟩
  · rintro ⟨⟨⟨a, d⟩, c⟩, e⟩
    have z := EntryStm.bytes_size x
    rw [e] at c
    have v : x.first.value.size < 2 ^ 64 := by omega
    have w : x.further.value.size < 2 ^ 64 := by omega
    exact h.2 ⟨⟨⟨⟨a, v⟩, d, w⟩, by rw [e]; exact c⟩, e⟩

/-- Without a premise. From the statement written of x the reader gives x's two tables back exactly
where both have the form `TableSt.ok` and the statement's length, 160 + 48 for each answer of a
table, is below 2 ^ 64: the inequality of `TableShape.fitsWord`. -/
theorem EntryStm.read_bytes_iff (f : Fld) (s : TableShape) (x : EntryStm) :
    EntryStm.read f s x.bytes = some (x.first, x.further) ↔
      (x.first.ok f s = true ∧ x.further.ok f s = true) ∧ 160 + 48 * s.count < 2 ^ 64 := by
  rw [EntryStm.read_iff]
  constructor
  · rintro ⟨⟨a, c⟩, -⟩
    rw [EntryStm.bytes_size_ok f s x a.1 a.2] at c
    exact ⟨a, c⟩
  · rintro ⟨a, c⟩
    exact ⟨⟨a, by rw [EntryStm.bytes_size_ok f s x a.1 a.2]; exact c⟩, rfl⟩

/-- Asked: `TableShape.fitsWord`. From the statement written of x the reader gives x's two tables
back exactly where both have the form `TableSt.ok`. -/
theorem EntryStm.read_bytes (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (x : EntryStm) :
    EntryStm.read f s x.bytes = some (x.first, x.further) ↔
      x.first.ok f s = true ∧ x.further.ok f s = true := by
  rw [EntryStm.read_bytes_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, (TableShape.fitsWord_iff s).1 hs⟩⟩

/-- The same at a declared structure. Asked: `TableShape.fitsWord` of the declared tables' shape.
The reader, told D's field and D's shape, gives x's two tables back exactly where x has the form
`EntryStm.ok`. -/
theorem EntryStm.read_bytes_ok (D : Declared) (hs : D.table.fitsWord = true) (x : EntryStm) :
    EntryStm.read D.setting.field D.table x.bytes = some (x.first, x.further) ↔ x.ok D = true := by
  rw [EntryStm.read_bytes _ _ hs, EntryStm.ok_iff]

/-- Asked: `TableShape.fitsWord` of the declared tables' shape. The statement of an entry's link, of
a value with the form, has fewer than 2 ^ 64 bytes. -/
theorem EntryStm.bytes_size_lt (D : Declared) (hs : D.table.fitsWord = true) (x : EntryStm)
    (hx : x.ok D = true) : x.bytes.size < 2 ^ 64 := by
  obtain ⟨a, c⟩ := (EntryStm.ok_iff D x).1 hx
  rw [EntryStm.bytes_size_ok _ _ x a c]
  exact (TableShape.fitsWord_iff D.table).1 hs

/-- What the reader of an entry's statement gives is what the library's readers of a statement's
items take out of the same string: the two items (`rdItems`, Fmt/ParamsRead.lean; `EntryStm.items`,
Fmt/ParsedLaws.lean) and the roots in item 0 and item 1 (`itemRoot`, Fmt/Rules8X.lean). Over
`EntryStm.bytes_read`, `EntryStm.root0`, `EntryStm.root1`. -/
theorem EntryStm.read_items (f : Fld) (s : TableShape) (b : ByteArray) (x : EntryStm)
    (h : EntryStm.read f s b = some (x.first, x.further)) :
    rdItems b.size b 0 = some (x.items, b.size) ∧ itemRoot b 0 = some x.first.root ∧
      itemRoot b 1 = some x.further.root := by
  obtain ⟨⟨-, c⟩, rfl⟩ := (EntryStm.read_iff f s b x).1 h
  rw [EntryStm.bytes_size] at c
  exact ⟨EntryStm.bytes_read x (by omega) (by omega), EntryStm.root0 x (by omega) (by omega),
    EntryStm.root1 x (by omega) (by omega)⟩

/-- Asked: `TableShape.fitsWord` of the declared tables' shape. Two values with the form
`EntryStm.ok`, under one declared structure, and the same statement are the same: both tables, roots
and answers. -/
theorem EntryStm.bytes_inj (D : Declared) (hs : D.table.fitsWord = true) (x y : EntryStm)
    (hx : x.ok D = true) (hy : y.ok D = true) (e : x.bytes = y.bytes) : x = y := by
  have a := (EntryStm.read_bytes_ok D hs x).2 hx
  rw [e, (EntryStm.read_bytes_ok D hs y).2 hy] at a
  obtain ⟨h0, h1⟩ := Prod.mk.inj (Option.some.inj a)
  exact (congr (congrArg EntryStm.mk h0) h1).symm

/-! ## 4. The first query -/

/-- AN ENTRY's LINK. Asked: `TableShape.fitsWord` of the declared tables' shape; both values have
the form `EntryStm.ok` under one declared structure; the other three parts have a spelling
(`First.Rest`). Two first queries on the same bytes speak of the same two tables, under the same
parameters' digest, record and run's value. -/
theorem firstBytes_entry_inj (D : Declared) (hs : D.table.fitsWord = true) (x y : EntryStm)
    (hx : x.ok D = true) (hy : y.ok D = true) (pd rc pd' rc' : ByteArray)
    (run run' : Option ByteArray) (h : First.Rest pd rc run) (h' : First.Rest pd' rc' run')
    (e : firstBytes pd x.bytes rc run = firstBytes pd' y.bytes rc' run') :
    x = y ∧ pd = pd' ∧ rc = rc' ∧ run = run' := by
  obtain ⟨a, b, c, d⟩ := firstBytes_parts pd x.bytes rc pd' y.bytes rc' run run' h h'
    (EntryStm.bytes_size_lt D hs x hx) (EntryStm.bytes_size_lt D hs y hy) e
  exact ⟨EntryStm.bytes_inj D hs x y hx hy b, a, c, d⟩

/-- THE CHAIN OF A RECORD's SEEDS. Asked: both tables' roots and both digests have 32 bytes; both
declared shapes have `TableShape.wordsFit`; the other three parts have a spelling (`First.Rest`).
Two first queries on the same bytes speak of the same root, the same configuration's digest and
the same shape. Of the answers nothing follows. -/
theorem firstBytes_record_inj (D D' : Declared) (cfg cfg' : ByteArray) (t t' : TableSt)
    (hr : t.root.size = 32) (hr' : t'.root.size = 32) (hc : cfg.size = 32) (hc' : cfg'.size = 32)
    (hs : D.table.wordsFit = true) (hs' : D'.table.wordsFit = true) (pd rc pd' rc' : ByteArray)
    (run run' : Option ByteArray) (h : First.Rest pd rc run) (h' : First.Rest pd' rc' run')
    (e : firstBytes pd (recordStm D cfg t) rc run =
      firstBytes pd' (recordStm D' cfg' t') rc' run') :
    (t.root = t'.root ∧ cfg = cfg' ∧ D.table = D'.table) ∧ pd = pd' ∧ rc = rc' ∧ run = run' := by
  obtain ⟨a, b, c, d⟩ := firstBytes_parts pd (recordStm D cfg t) rc pd' (recordStm D' cfg' t') rc'
    run run' h h' (recordStm_size_lt D cfg t hr hc) (recordStm_size_lt D' cfg' t' hr' hc') e
  exact ⟨recordStm_inj D D' cfg cfg' t t' hr hr' hc hc' hs hs' b, a, c, d⟩

/-- What the library hashes for the first value of a record's chain (`recordFirstW`,
Fmt/Rules4.lean, R4.8): `firstBytes` with 32 zero bytes for the parameters' digest, the name as the
statement, an empty record and no run's value. -/
theorem recordFirstW_hashes {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (name : ByteArray) :
    recordFirstW h name =
      h 160 0 recordLabel zero32 (firstBytes zero32 name ByteArray.empty none) := rfl

/-- These three parts have a spelling. -/
theorem First.rest_record : First.Rest zero32 ByteArray.empty none :=
  ⟨by decide, by rw [ByteArray.size_empty]; decide, fun _ h => absurd h (by simp)⟩

/-- `firstBytes_record_inj` at the string that the library hashes (`recordFirstW_hashes`). Asked:
both tables' roots and both digests have 32 bytes; both declared shapes have `TableShape.wordsFit`.
-/
theorem recordFirst_bytes_inj (D D' : Declared) (cfg cfg' : ByteArray) (t t' : TableSt)
    (hr : t.root.size = 32) (hr' : t'.root.size = 32) (hc : cfg.size = 32) (hc' : cfg'.size = 32)
    (hs : D.table.wordsFit = true) (hs' : D'.table.wordsFit = true)
    (e : firstBytes zero32 (recordStm D cfg t) ByteArray.empty none =
      firstBytes zero32 (recordStm D' cfg' t') ByteArray.empty none) :
    t.root = t'.root ∧ cfg = cfg' ∧ D.table = D'.table :=
  (firstBytes_record_inj D D' cfg cfg' t t' hr hr' hc hc' hs hs' zero32 ByteArray.empty zero32
    ByteArray.empty none none First.rest_record First.rest_record e).1

/-- THE LIBRARY's OWN START OF A CHAIN (`startChainW`, Fmt/Rules4.lean), AT EVERY PLAIN HASH h.
Asked: h's answers under the number 172, under which a run's value is made, have 32 bytes; pd has 32
bytes (the reader of a chain, `readChain`, Fmt/Rules8.lean, hands it the digest of the chain's
parameter bytes, h's answer under 169). Whatever head it gives: the head's first value is h's answer
under 160 on `firstBytes` at pd, the statement, the empty record and the head's own run's value, and
these three parts beside the statement meet `First.Rest`. So the two premises `First.Rest` of the
theorems on the first query are met wherever `startChainW` at such an h gives a head from a digest
of 32 bytes. -/
theorem startChainW_rest (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (hh : ∀ t i s b, (Id.run (h 172 t i s b)).size = 32) (lab : Nat) (pd st : ByteArray)
    (rnd : Option ByteArray) (c : ChainHead) (hp : pd.size = 32)
    (e : Id.run (startChainW h lab pd st rnd) = some c) :
    c.rho0 = Id.run (h 160 0 lab zero32 (firstBytes pd st ByteArray.empty c.run)) ∧
      First.Rest pd ByteArray.empty c.run := by
  have z : ByteArray.empty.size < 2 ^ 64 := by rw [ByteArray.size_empty]; decide
  unfold startChainW at e
  split at e
  · cases rnd with
    | none =>
      have e' : some (⟨none, Id.run (h 160 0 lab zero32 (firstBytes pd st ByteArray.empty none))⟩ :
          ChainHead) = some c := e
      obtain rfl := Option.some.inj e'
      exact ⟨rfl, hp, z, fun _ g => absurd g (by simp)⟩
    | some b =>
      dsimp only at e
      split at e
      · have e' : (if runOk (Id.run (runValueW h lab pd b)) = true then
            some (⟨some (Id.run (runValueW h lab pd b)),
              Id.run (h 160 0 lab zero32
                (firstBytes pd st ByteArray.empty (some (Id.run (runValueW h lab pd b)))))⟩ :
              ChainHead)
            else none) = some c := e
        split at e'
        · obtain rfl := Option.some.inj e'
          exact ⟨rfl, hp, z, fun r g => by
            obtain rfl := Option.some.inj g
            exact hh 0 lab zero32 (pd ++ b)⟩
        · exact absurd e' (by simp)
      · cases e
  · cases e

/-- What the laws of this file ask of their parameter h can be met: the function that answers 32
zero bytes to every call has answers of 32 bytes under every number. -/
theorem sized_const (n t i : Nat) (s b : ByteArray) :
    (Id.run ((fun _ _ _ _ _ => pure zero32 :
      Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) n t i s b)).size = 32 := by
  show zero32.size = 32
  decide

/-! ## 5. The string of the commitment ID -/

/-- Where the string is hashed, OVER EVERY MONAD AND AT EVERY HASH h: the library's commitment ID
(`publishedIDW`, Fmt/Rules4.lean, R4.11) of the digest, the table's name, the seeds' elements, the
answers and the digests at the end is h's answer under 179 on `idString` (Fmt/Parsed.lean). -/
theorem publishedIDW_hashes {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (D : Declared) (cfg : ByteArray)
    (t : TableSt) (seeds : List Ext) (told : List ByteArray) :
    publishedIDW h cfg (D.table.name cfg t.root) seeds t.answers told =
      h 179 0 0 zero32 (idString D cfg t seeds told) := rfl

/-- The string's five parts, bracketed from the right: the digest; the name as a string of bytes;
then three lists, each behind the word of its number: the seeds' elements, the answers, the digests.
-/
theorem idString_pair (D : Declared) (cfg : ByteArray) (t : TableSt) (seeds : List Ext)
    (told : List ByteArray) :
    idString D cfg t seeds told =
      cfg ++ (text (D.table.name cfg t.root) ++ ((u64n seeds.length ++ cat (seeds.map ext)) ++
        ((u64n t.answers.length ++ cat (t.answers.map ext)) ++
          (u64n told.length ++ cat (told.map id))))) := by
  simp only [idString, publishedBytes, list, ByteArray.append_assoc]

/-- Digests of 32 bytes, one after the other. -/
theorem size_digests : ∀ l : List ByteArray, (∀ b ∈ l, b.size = 32) →
    (cat (l.map id)).size = 32 * l.length
  | [], _ => by simp [cat_nil]
  | b :: l, h => by
    rw [List.map_cons, cat_cons, ByteArray.size_append,
      size_digests l fun c hc => h c (List.mem_cons_of_mem _ hc), List.length_cons]
    have a : (id b).size = 32 := h b (List.mem_cons_self ..)
    omega

/-- Its length: four words, the name's 48 bytes of words, the digest twice, the root, 24 for each
element of a seed and for each answer, and the digests. -/
theorem idString_size (D : Declared) (cfg : ByteArray) (t : TableSt) (seeds : List Ext)
    (told : List ByteArray) :
    (idString D cfg t seeds told).size = 80 + 2 * cfg.size + t.root.size + 24 * seeds.length +
      24 * t.answers.length + (cat (told.map id)).size := by
  simp only [idString, publishedBytes, list, text, u64n, ByteArray.size_append, size_u64,
    size_exts, TableShape.name_size]
  omega

/-- `seedsOk` as two statements. -/
theorem seedsOk_iff (f : Fld) (s : TableShape) (seeds : List Ext) :
    seedsOk f s seeds = true ↔
      seeds.length = s.answers * (s.cube + 1) ∧ ∀ e ∈ seeds, f.okE e = true := by
  simp only [seedsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]

/-- `toldOk` as a statement. -/
theorem toldOk_iff (told : List ByteArray) : toldOk told = true ↔ ∀ b ∈ told, b.size = 32 := by
  simp only [toldOk, List.all_eq_true, beq_iff_eq]

/-- Two lists of canonical elements, of one length, with one spelling, are one list. -/
theorem exts_inj (f : Fld) (l l' : List Ext) (n : l'.length = l.length)
    (k : ∀ e ∈ l, f.okE e = true) (k' : ∀ e ∈ l', f.okE e = true)
    (e : cat (l.map ext) = cat (l'.map ext)) : l = l' :=
  inj_of_undoes (undoes_count (undoes_ext f) l.length) l l'
    ⟨rfl, fun x hx => lt_of_okE f x (k x hx)⟩ ⟨n, fun x hx => lt_of_okE f x (k' x hx)⟩ e

/-- Two lists of digests of 32 bytes with one spelling are one list. -/
theorem digests_inj (l l' : List ByteArray) (k : ∀ b ∈ l, b.size = 32)
    (k' : ∀ b ∈ l', b.size = 32) (e : cat (l.map id) = cat (l'.map id)) : l = l' := by
  have n : l'.length = l.length := by
    have z := congrArg ByteArray.size e
    rw [size_digests l k, size_digests l' k'] at z
    omega
  exact inj_of_undoes (undoes_count undoes_digest l.length) l l' ⟨rfl, k⟩ ⟨n, k'⟩ e

/-- WHERE THE DRAWING OF A RECORD's SEEDS ANSWERS, AT EVERY PLAIN HASH h: exactly where h's answer
to the one call for the first value of the record's chain (`recordFirstW`) has 32 bytes. The field,
the two numbers and the name's form do not enter: of what the chain's step asks (`askOK`,
Fmt/Rules5.lean) all else is fixed at this call, and there is no work to test. -/
theorem recordSeedsW_some_iff (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (f : Fld) (name : ByteArray) (v a : Nat) :
    (∃ l, Id.run (recordSeedsW h f name v a) = some l) ↔
      (Id.run (recordFirstW h name)).size = 32 := by
  -- by the named equation `recordSeedsW_run`, not by unfolding
  rw [recordSeedsW_run]
  generalize Id.run (recordFirstW h name) = rho
  by_cases k : rho.size = 32
  · have ok : askOK recordLabel rho (0 + 1) ByteArray.empty .seeds 0 0 = true := by
      simp [askOK, recordLabel, k]
    have s : ∃ x, Id.run ((⟨recordLabel, rho, 0⟩ : Chain).queryW h ByteArray.empty .seeds 0 0
        (blocksFor (a * (v * 18 + 36)))) = some x := by
      unfold Chain.queryW
      rw [if_pos ok]
      exact ⟨_, rfl⟩
    obtain ⟨x, s⟩ := s
    rw [s]
    exact ⟨fun _ => k, fun _ => ⟨_, rfl⟩⟩
  · have no : ¬ askOK recordLabel rho (0 + 1) ByteArray.empty .seeds 0 0 = true := by
      simp [askOK, k]
    have s : Id.run ((⟨recordLabel, rho, 0⟩ : Chain).queryW h ByteArray.empty .seeds 0 0
        (blocksFor (a * (v * 18 + 36)))) = none := by
      unfold Chain.queryW
      rw [if_neg no]
      rfl
    rw [s]
    exact ⟨fun ⟨_, e⟩ => (nomatch e), fun e => absurd e k⟩

/-- WHAT `Declared.seedsW` DRAWS HAS THE FORM `seedsOk`, AT EVERY PLAIN HASH h. Asked: the drawing
answers. (Where it refuses, the list is empty and the shape says otherwise.) So the string on which the closed form of the test on the ID calls the hash
(`KeyParsed.idOkW_iff`, Fmt/ChainStmJoin.lean) meets that one premise of `idString_inj`; all of
them: `Declared.idString_closed_inj`. -/
theorem Declared.seedsW_ok (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (D : Declared) (cfg : ByteArray) (t : TableSt)
    (hd : ∃ l, Id.run (recordSeedsW h D.setting.field (recordStm D cfg t)
      D.table.cube D.table.answers) = some l) :
    seedsOk D.setting.field D.table (Id.run (D.seedsW h cfg t)) = true := by
  -- by named equations, not by unfolding
  rw [seedsOk_iff, Declared.seedsW]
  obtain ⟨l, hl⟩ := hd
  have e : Id.run (do
      let l ← recordSeedsW h D.setting.field (recordStm D cfg t) D.table.cube D.table.answers
      pure (flatSeeds (l.getD []))) = flatSeeds l := by
    rw [idRunBind, hl]
    rfl
  rw [e]
  exact flatSeeds_ok _ _ _ l (recordSeedsW_shaped h _ _ _ _ l hl)

/-- The same, with "the drawing answers" replaced by a condition on h, AT EVERY PLAIN HASH h. Asked:
h's answer to the call for the first value of the record's chain has 32 bytes. -/
theorem Declared.seedsW_ok_of_size (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (D : Declared) (cfg : ByteArray) (t : TableSt)
    (hd : (Id.run (recordFirstW h (recordStm D cfg t))).size = 32) :
    seedsOk D.setting.field D.table (Id.run (D.seedsW h cfg t)) = true :=
  Declared.seedsW_ok h D cfg t ((recordSeedsW_some_iff h _ _ _ _).2 hd)

/-- ONE STRING: ONE DIGEST, ONE SHAPE, ONE TABLE, ONE LIST OF SEEDS' ELEMENTS, ONE LIST OF DIGESTS.
Asked: both digests at the front have 32 bytes; both tables have the form `TableSt.ok` and both
lists of seeds' elements the form `seedsOk`, in one field, each under its own declared shape; both
shapes have `TableShape.wordsFit`; the digests at the end have 32 bytes each (`toldOk`).
`TableShape.fitsWord` is not asked. How: the digest and the name, which have one length on both
sides, come off first, and the name gives one shape; under one shape the forms give both lists of
seeds' elements one length, and both lists of answers; what is left has one length, and is cut into
32s. Of the rest of D and D' nothing follows. -/
theorem idString_inj (f : Fld) (D D' : Declared) (cfg cfg' : ByteArray) (t t' : TableSt)
    (seeds seeds' : List Ext) (told told' : List ByteArray)
    (hc : cfg.size = 32) (hc' : cfg'.size = 32) (ht : t.ok f D.table = true)
    (ht' : t'.ok f D'.table = true) (hs : D.table.wordsFit = true)
    (hs' : D'.table.wordsFit = true) (hq : seedsOk f D.table seeds = true)
    (hq' : seedsOk f D'.table seeds' = true) (hd : toldOk told = true)
    (hd' : toldOk told' = true)
    (e : idString D cfg t seeds told = idString D' cfg' t' seeds' told') :
    cfg = cfg' ∧ D.table = D'.table ∧ t = t' ∧ seeds = seeds' ∧ told = told' := by
  obtain ⟨r, c, k⟩ := (TableSt.ok_iff f D.table t).1 ht
  obtain ⟨r', c', k'⟩ := (TableSt.ok_iff f D'.table t').1 ht'
  obtain ⟨m, j⟩ := (seedsOk_iff f D.table seeds).1 hq
  obtain ⟨m', j'⟩ := (seedsOk_iff f D'.table seeds').1 hq'
  rw [idString_pair, idString_pair] at e
  -- the digest
  obtain ⟨b2, e1⟩ := append_cancel _ _ _ _ (hc.trans hc'.symm) e
  -- the name
  have q : (D.table.name cfg t.root).size < 2 ^ 64 := by rw [TableShape.name_size]; omega
  have q' : (D'.table.name cfg' t'.root).size < 2 ^ 64 := by rw [TableShape.name_size]; omega
  have z1 : (text (D.table.name cfg t.root)).size = (text (D'.table.name cfg' t'.root)).size := by
    rw [size_text, size_text, TableShape.name_size, TableShape.name_size, r, r', hc, hc']
  obtain ⟨a0, e2⟩ := append_cancel _ _ _ _ z1 e1
  have a1 : D.table.name cfg t.root = D'.table.name cfg' t'.root :=
    inj_of_undoes undoes_text _ _ q q' a0
  obtain ⟨b1, -, b3⟩ :=
    TableShape.name_inj D.table D'.table cfg cfg' t.root t'.root r r' hc hc' hs hs' a1
  -- the seeds' elements: one length, by the one shape
  have n1 : seeds'.length = seeds.length := by rw [m, m', b3]
  have z2 : (u64n seeds.length ++ cat (seeds.map ext)).size =
      (u64n seeds'.length ++ cat (seeds'.map ext)).size := by
    simp only [u64n, ByteArray.size_append, size_u64, size_exts, n1]
  obtain ⟨a2, e3⟩ := append_cancel _ _ _ _ z2 e2
  have a3 := (append_cancel _ _ _ _ (by simp only [u64n, size_u64]) a2).2
  have s1 : seeds = seeds' := exts_inj f seeds seeds' n1 j j' a3
  -- the answers: one length, by the one shape
  have n2 : t'.answers.length = t.answers.length := by rw [c, c', b3]
  have z3 : (u64n t.answers.length ++ cat (t.answers.map ext)).size =
      (u64n t'.answers.length ++ cat (t'.answers.map ext)).size := by
    simp only [u64n, ByteArray.size_append, size_u64, size_exts, n2]
  obtain ⟨a4, e4⟩ := append_cancel _ _ _ _ z3 e3
  have a5 := (append_cancel _ _ _ _ (by simp only [u64n, size_u64]) a4).2
  have s2 : t.answers = t'.answers := exts_inj f t.answers t'.answers n2 k k' a5
  -- the digests at the end
  have a6 := (append_cancel _ _ _ _ (by simp only [u64n, size_u64]) e4).2
  have s3 : told = told' :=
    digests_inj told told' ((toldOk_iff told).1 hd) ((toldOk_iff told').1 hd') a6
  exact ⟨b2, b3, congr (congrArg TableSt.mk b1) s2, s1, s3⟩

/-- `idString_inj` AT THE STRING ON WHICH THE CLOSED FORM OF THE TEST ON THE ID CALLS THE HASH
(`KeyParsed.idOkW_iff`, Fmt/ChainStmJoin.lean: the declared files' digest by h, the seeds drawn by
h, no digest at the end), AT EVERY PLAIN HASH h: one string: one digest, one shape, one table.
Asked: h's answers under the numbers 169 (the files' digest) and 160 (a chain's first value) have 32
bytes; one field; both tables have the form `TableSt.ok` (the closed test asks it); BOTH SHAPES HAVE
`TableShape.wordsFit`, WHICH THE CLOSED TEST DOES NOT ASK. The premise is on the strings: from two
equal IDs nothing follows here. -/
theorem Declared.idString_closed_inj (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (hc : ∀ t i s b, (Id.run (h 169 t i s b)).size = 32)
    (hr : ∀ t i s b, (Id.run (h 160 t i s b)).size = 32) (D D' : Declared)
    (hf : D'.setting.field = D.setting.field) (t t' : TableSt)
    (ht : t.ok D.setting.field D.table = true) (ht' : t'.ok D'.setting.field D'.table = true)
    (hs : D.table.wordsFit = true) (hs' : D'.table.wordsFit = true)
    (e : idString D (Id.run (D.cfgW h)) t (Id.run (D.seedsW h (Id.run (D.cfgW h)) t)) [] =
      idString D' (Id.run (D'.cfgW h)) t' (Id.run (D'.seedsW h (Id.run (D'.cfgW h)) t')) []) :
    Id.run (D.cfgW h) = Id.run (D'.cfgW h) ∧ D.table = D'.table ∧ t = t' := by
  have q := Declared.seedsW_ok_of_size h D (Id.run (D.cfgW h)) t (hr _ _ _ _)
  have q' := Declared.seedsW_ok_of_size h D' (Id.run (D'.cfgW h)) t' (hr _ _ _ _)
  rw [hf] at ht' q'
  obtain ⟨a, b, c, -, -⟩ := idString_inj D.setting.field D D' _ _ t t' _ _ [] [] (hc _ _ _ _)
    (hc _ _ _ _) ht ht' hs hs' q q' rfl rfl e
  exact ⟨a, b, c⟩

end Fmt

#print axioms Fmt.undoes_num
#print axioms Fmt.cuts_num
#print axioms Fmt.TableShape.wordsFit_iff
#print axioms Fmt.TableShape.wordsFit_of_ok
#print axioms Fmt.undoes_shape
#print axioms Fmt.cuts_shape
#print axioms Fmt.TableShape.name_pair
#print axioms Fmt.TableShape.name_size
#print axioms Fmt.recordStm_size
#print axioms Fmt.recordStm_size_lt
#print axioms Fmt.rdRecordStm_iff
#print axioms Fmt.recordStm_read
#print axioms Fmt.TableShape.name_inj
#print axioms Fmt.recordStm_inj
#print axioms Fmt.recordStm_answers
#print axioms Fmt.EntryStm.ok_iff
#print axioms Fmt.EntryStm.read_iff
#print axioms Fmt.EntryStm.read_bytes_iff
#print axioms Fmt.EntryStm.read_bytes
#print axioms Fmt.EntryStm.read_bytes_ok
#print axioms Fmt.EntryStm.bytes_size_lt
#print axioms Fmt.EntryStm.read_items
#print axioms Fmt.EntryStm.bytes_inj
#print axioms Fmt.firstBytes_entry_inj
#print axioms Fmt.firstBytes_record_inj
#print axioms Fmt.recordFirstW_hashes
#print axioms Fmt.First.rest_record
#print axioms Fmt.recordFirst_bytes_inj
#print axioms Fmt.startChainW_rest
#print axioms Fmt.sized_const
#print axioms Fmt.publishedIDW_hashes
#print axioms Fmt.idString_pair
#print axioms Fmt.size_digests
#print axioms Fmt.idString_size
#print axioms Fmt.seedsOk_iff
#print axioms Fmt.toldOk_iff
#print axioms Fmt.exts_inj
#print axioms Fmt.digests_inj
#print axioms Fmt.recordSeedsW_some_iff
#print axioms Fmt.Declared.seedsW_ok
#print axioms Fmt.Declared.seedsW_ok_of_size
#print axioms Fmt.idString_inj
#print axioms Fmt.Declared.idString_closed_inj

/-
Notes in full (other files' comments call these notes "the head of" this file).

Fmt/ChainStmMore.lean: readers and laws for two more statements: that of the chain of a record's
seeds (a table's name) and that of an entry file's link (two tables' items). For each: the reader
gives a value exactly on the bytes that the writer writes of that value, and exactly where the value
has its form (for an entry's link: and the statement has fewer than 2 ^ 64 bytes); so the bytes fix
the values that have the form; and so does the string of a chain's first query. Then two things
beside: the library's own start of a chain from a digest of 32 bytes meets what the laws on the
first query ask of the call's other parts, at every hash whose answers under the number 172 have 32
bytes; and the string of which the commitment ID is the hash fixes the digest, the shape, the table
and the two lists beside it, among those that have their forms in one field.

What kind of laws. Laws on the format's spellings, as Fmt/Rules4.lean and Fmt/Parsed.lean write
them. No theorem of the library on a verifier uses them, and that a verifier or the programs hash
these strings is not shown here. NO FIXED HASH FUNCTION IS NAMED IN A LAW OF THIS FILE: a hash is a
letter h, "a plain hash": any function of the hash's five arguments with values in the monad Id (an
ordinary function); what a law asks of it stands among that law's premises (they can be met:
`sized_const` here; Fmt/TestChainStm.lean, part E). (The neighbours have, for some forms with a W, a
flat name at one fixed hash function; no law here names one.)

The writers are not written again: `recordStm` (Fmt/ChainStm.lean), which is `TableShape.name`
(Fmt/Parsed.lean) over `tableName` (Fmt/Rules4.lean, R4.10); `EntryStm.bytes`, `idString`
(Fmt/Parsed.lean, R13.5, R4.11). The proofs go as in Fmt/ChainStmLaws.lean and
Fmt/ChainStmJoin.lean. No Mathlib, neither directly nor through the imports. Rule numbers (R…) are
taken from the comments of the files named; the format page was not read for this file.

1. Definitions. `rdNum`, `TableShape.wordsFit`, `TableShape.wordsBytes`, `rdShape`, `rdRecordStm`,
`EntryStm.read`.

2. What is checked when the file compiles. The proofs; the axioms of every theorem are printed.
Tests: Fmt/TestChainStm.lean.

3. Theorems.
    The parts: `undoes_num`, `cuts_num`, `TableShape.wordsFit_iff`, `TableShape.wordsFit_of_ok`,
      `undoes_shape`, `cuts_shape`; `TableShape.name_pair`, `TableShape.name_size`,
      `recordStm_size`, `recordStm_size_lt`, `EntryStm.ok_iff`, `EntryStm.bytes_size_lt`.
    The reader answers exactly where ..., without a premise: `rdRecordStm_iff`, `EntryStm.read_iff`,
      `recordStm_read`, `EntryStm.read_bytes_iff`; under `TableShape.fitsWord`:
      `EntryStm.read_bytes`, `EntryStm.read_bytes_ok`. `EntryStm.read_items`.
    One-to-one on what has the form: `TableShape.name_inj`, `recordStm_inj`, `EntryStm.bytes_inj`
      (asked: `TableShape.fitsWord`). `recordStm_answers`: the name does not hang on the answers.
    The first query: `firstBytes_entry_inj` (asked: `TableShape.fitsWord`), `firstBytes_record_inj`;
      `recordFirstW_hashes`, `First.rest_record`, `recordFirst_bytes_inj`; `startChainW_rest`;
      `sized_const`.
    The string of the commitment ID: `publishedIDW_hashes`, `idString_pair`, `size_digests`,
      `idString_size`, `seedsOk_iff`, `toldOk_iff`, `exts_inj`, `digests_inj`;
      `recordSeedsW_some_iff`, `Declared.seedsW_ok`, `Declared.seedsW_ok_of_size`; `idString_inj`:
      one-to-one on what has the form, in one field, without `TableShape.fitsWord`;
      `Declared.idString_closed_inj`: that law at the string on which the closed form of the test on
      the ID calls the hash.

4. What is not claimed. ("A test": one of Fmt/TestChainStm.lean.)
   "Form" means here, for a name: the root and the digest have 32 bytes each, and the shape has
   `TableShape.wordsFit`; for an entry's statement: `EntryStm.ok`, that is, `TableSt.ok` of both
   tables. No reader is a verifier, and no verifier calls one. Nothing on soundness follows.
   A NAME FIXES THE ROOT, THE CONFIGURATION's DIGEST AND THE SHAPE, NOT THE ANSWERS: they are not in
   it (`recordStm_answers`). No theorem here ties a table's answers to its root.
   `recordStm` reads of the declared structure the tables' shape alone: of the rest of D nothing
   follows. Its digest is an argument; nothing here says that it is the digest of D's files.
   A name has no word for a length: where the root ends and the digest begins is not in the bytes.
   "32 bytes each" is a clause of the form, and a premise of the one-to-one laws; a root of 33 bytes
   with a digest of 31 is read as another root and another digest (a test).
   A word is written modulo 2 ^ 64 (`u64n`): a shape without `TableShape.wordsFit` has the name of
   another shape (a test). `rdShape` tests no range: it gives whatever six words stand there, within
   `TableShape.ok` or not (a test).
   `TableShape.wordsFit` and `TableShape.fitsWord` (Fmt/ChainStm.lean) are two things. The first:
   each of the shape's six numbers is a word. The second: a statement of two tables of the shape has
   a length that is a word. The first does not give the second (a test). `TableShape.ok` gives the
   first (`TableShape.wordsFit_of_ok`) and the second (`TableShape.fitsWord_of_ok`,
   Fmt/ChainStmLaws.lean: it is its last clause).
   Of an entry's statement: both tables are held to one field and one shape. Nothing says that the
   two tables differ (a test: one table twice is read back), nor whence the first table comes. The
   premise `TableShape.fitsWord` stands in five theorems here. For an entry's statement it is exact:
   its number is the statement's length (`EntryStm.bytes_size_ok`, `EntryStm.read_bytes_iff`).
   Nothing about the hash: no statement here says that two calls with the same ANSWER hash the same
   bytes. Nothing about which chain a call belongs to: a chain's label stands in the call's place,
   not in these bytes. No theorem here holds a name, as a string, against a statement made of items.
   OF THE COMMITMENT ID: `idString_inj` speaks of the string that is hashed under 179, not of the
   ID. That two tables with one ID are one table does not follow here. Under a random oracle two
   different strings get one answer only with small probability; no bound on it is proved here.
   There is no reader of that string here, and no law "exactly where". The three words in that
   string that count a list's members are taken modulo 2 ^ 64 by the spelling; `idString_inj` never
   reads them: the forms fix the first two lists' lengths by the shape, and the third's follows from
   the string's length. The format closes the string with one word 0, an empty list of which this
   version defines no element (R4.11); that this library types that list as a list of digests, and
   has it as an argument, is the library's own choice. That the seeds in the string are those drawn
   from the name is no matter of the string: `Declared.seedsW` (Fmt/ChainStm.lean) draws them.
   WHO PAYS THE PREMISES OF `idString_inj` AT THE CLOSED FORM OF THE TEST ON THE ID
   (`KeyParsed.idOkW`, Fmt/ChainStm.lean). The table's form: the test asks it. The digests at the
   end: the empty list has the form. The seeds' form: it holds where h's answer to the call for the
   first value of the record's chain has 32 bytes (`Declared.seedsW_ok_of_size`). THREE ARE ASKED
   BY NOBODY THERE: that the files' digest has 32 bytes, which holds where h's answers under 169
   have; `TableShape.wordsFit`: two declared shapes whose words agree modulo 2 ^ 64 give one string
   (a test); and that both declared structures have one field, which a test on one structure cannot
   ask. `Declared.idString_closed_inj` has all three among its premises.
   THAT `idString` IS THE FORMAT PAGE's STRING (R4.11) IS HELD BY TESTS, NOT BY A LAW:
   Fmt/TestChainStm.lean, part B, block 3, holds `KeyStm.idOkW` against the page's three known
   answers for the ID (docs/format/format-vectors.txt, lines 140 to 142), which Fmt/Rules4.lean
   holds as guards too. The closed form `KeyParsed.idOkW` is held at none of them (the tests' head
   says why).
   ON A REFUSAL of the record's chain's step the closed form of the test on the ID goes on with no
   seeds, as the Lean port of the programs' verifier (lean/OnBytes/) does in its form for this
   string: that list has not the form `seedsOk`, and `idString_inj` says nothing of such a string.
   The step refuses exactly where h's answer to the call for that chain's first value has not 32
   bytes (`recordSeedsW_some_iff`).
   Of `startChainW` at an h whose answers under 172 have another length nothing is said here.
-/
