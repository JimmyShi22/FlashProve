-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/SeedRec.lean: a stored table's record in plain data (its seeds and its answers), as a
function of the table, and the key that the program's blocks read as a function of that record. For
proofs only; the program does not import this file.

The program `verify-on-bytes` hands its blocks a `TableKey` (OnBytes/Iop/Foldeq.lean), which
`tableKey` (OnBytes/Entry/Table.lean) makes of a table's root and answers. A typed verifier with
records takes a record: a seed and an answer. Here both meet in one plain value.

Main definitions.
 `PlainRec`            the seeds, each a point and a factor; the answers.
 `plainRec f cfg s t`  the record of the table t: the seeds at the table's name (`seedsAtName`,
                       OnBytes/K/SeedBytes.lean), and t's answers.
 `PlainRec.key r item`  the key with the record's answers and seeds.
 `PlainRec.Fits r s`   the sizes that `TableKey.fits` asks: s.rows * s.answers answers; s.answers
                       seeds, each point of s.cubeBits coordinates.
Main theorems.
 `tableKey_plainRec`   a key that `tableKey` returns is `(plainRec f cfg s t).key item`,
                       and the record fits the shape.
 `RecReading Sd An`    one pair of readings between plain and typed records, with its laws at the
                       records that it calls good; `recOf`, `plain`, `keyOf`, `stmR`; `keyOf_recOf`,
                       `stmR_recOf`.
 `checks_block`        where the checks of the key file and the entry file say yes under chains with
                       one digest and one shape: the block that `Tie.entrySpec` gives for the two
                       tables is `linkVerify` at the keys of the two tables' records.
                       `block_recOf`: the same at typed records.

What is not claimed. Nothing on how seeds are distributed; nothing on soundness.


-/
import OnBytes.K.SeedBytes
import OnBytes.Tie.SameChains
import OnBytes.Tie.LeafCall
import OnBytes.Hash.HEq

set_option autoImplicit false

namespace OnBytes.K

/-- A stored table's record, in plain data. -/
structure PlainRec where
  /-- the seeds: each a point and a factor -/
  seeds : List (List E × E)
  /-- the answers -/
  answers : List E

/-- The record of a table: the seeds at its name; its answers. -/
def plainRec (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape) (t : Params.TableName) :
    PlainRec :=
  ⟨seedsAtName f (Key.nameOf s cfg t) s.cubeBits s.answers, t.answers⟩

/-- The key with the record's answers and seeds. -/
def PlainRec.key (r : PlainRec) (item : ℕ) : TableKey :=
  { item := item, record := r.answers.toArray, seeds := r.seeds.map fun x => ⟨x.1, x.2⟩ }

/-- The record's sizes fit the shape: `TableKey.fits` of its key, as a proposition. -/
def PlainRec.Fits (r : PlainRec) (s : Params.IndexShape) : Prop :=
  r.answers.length = s.rows * s.answers ∧ r.seeds.length = s.answers ∧
    ∀ x ∈ r.seeds, x.1.length = s.cubeBits

/-- The key at another item's number. -/
theorem PlainRec.key_item (r : PlainRec) (i j : ℕ) : { r.key i with item := j } = r.key j := rfl

/-- **A key that `tableKey` returns is the key of the table's record**, and the record fits the
shape. The bound keeps the first string of the seeds' chain within the hash's domain. -/
theorem tableKey_plainRec (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (t : Params.TableName) (item : ℕ) (k : TableKey) (h : tableKey f cfg s t item = some k)
    (hn : (Key.nameOf s cfg t).size + 56 ≤ 2 ^ 32 - 144) :
    k = (plainRec f cfg s t).key item ∧ (plainRec f cfg s t).Fits s := by
  have hk : k = (plainRec f cfg s t).key item ∧ k.fits s = true := by
    unfold tableKey at h
    rw [show Fmt.tableName t.root cfg s.code.logN s.code.ell s.code.r s.v s.answers s.saltBytes =
        Key.nameOf s cfg t from rfl, recordSeeds_blocks _ _ _ _ hn] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i hf
      injection h with h
      subst h
      exact ⟨rfl, hf⟩
    · cases h
  refine ⟨hk.1, ?_⟩
  have hf := hk.2
  rw [hk.1] at hf
  unfold TableKey.fits PlainRec.key at hf
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_map, List.all_map, List.all_eq_true,
    Function.comp] at hf
  exact ⟨by simpa using hf.1.1, hf.1.2, fun x hx => hf.2 x hx⟩

/-! ## One pair of readings between plain and typed records -/

/-- One pair of readings between a record in plain data and a typed record (a seed of the type Sd
and an answer of the type An). `Good` says of which plain records the laws speak. -/
structure RecReading (Sd An : Type) where
  /-- the plain records of which the laws speak -/
  Good : PlainRec → Prop
  /-- the program's seeds, typed -/
  toSeed : List (List E × E) → Sd
  /-- a typed seed, as the program's seeds -/
  ofSeed : Sd → List (List E × E)
  /-- a table's answers, typed -/
  toAns : List E → Option An
  /-- a typed answer, as a table's answers -/
  ofAns : An → List E
  /-- the seeds of a good record are read back -/
  seed_back : ∀ r : PlainRec, Good r → ofSeed (toSeed r.seeds) = r.seeds
  /-- the answers of a good record are typed -/
  ans_some : ∀ r : PlainRec, Good r → ∃ a, toAns r.answers = some a
  /-- the typed answers of a good record are read back -/
  ans_back : ∀ r : PlainRec, Good r → ∀ a, toAns r.answers = some a → ofAns a = r.answers

namespace RecReading
variable {Sd An : Type} (R : RecReading Sd An)

/-- A plain record as a typed one. -/
def recOf (r : PlainRec) : Option (Sd × An) :=
  (R.toAns r.answers).map fun a => (R.toSeed r.seeds, a)

/-- A typed record as a plain one. -/
def plain (r : Sd × An) : PlainRec := ⟨R.ofSeed r.1, R.ofAns r.2⟩

/-- The key of a typed record. -/
def keyOf (r : Sd × An) (item : ℕ) : TableKey := (R.plain r).key item

/-- The item's number is laid over. -/
theorem keyOf_item (r : Sd × An) (i j : ℕ) : { R.keyOf r i with item := j } = R.keyOf r j := rfl

/-- The statement of an entry's chain at a pair of typed records, as a function of the two roots. -/
def stmR (rr : (Sd × An) × (Sd × An)) (r0 r1 : ByteArray) : ByteArray :=
  Params.Link.statement ⟨r0, (R.plain rr.1).answers⟩ ⟨r1, (R.plain rr.2).answers⟩

/-- A good plain record is read. -/
theorem recOf_some (r : PlainRec) (h : R.Good r) : ∃ t, R.recOf r = some t := by
  obtain ⟨a, ha⟩ := R.ans_some r h
  exact ⟨(R.toSeed r.seeds, a), by unfold recOf; rw [ha]; rfl⟩

/-- The way back gives it. -/
theorem plain_recOf (r : PlainRec) (h : R.Good r) (t : Sd × An) (ht : R.recOf r = some t) :
    R.plain t = r := by
  unfold recOf at ht
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 ht
  show (⟨R.ofSeed (R.toSeed r.seeds), R.ofAns a⟩ : PlainRec) = r
  rw [R.seed_back r h, R.ans_back r h a ha]

/-- The key of the typed record is the plain record's. -/
theorem keyOf_recOf (r : PlainRec) (h : R.Good r) (t : Sd × An) (ht : R.recOf r = some t)
    (item : ℕ) : R.keyOf t item = r.key item := by
  unfold keyOf
  rw [R.plain_recOf r h t ht]

/-- The statement at the typed records of two tables is the statement of an entry's chain at these
tables (`Tie.entryStatement`). -/
theorem stmR_recOf (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (t u : Params.TableName) (ht : R.Good (plainRec f cfg s t)) (hu : R.Good (plainRec f cfg s u))
    (a b : Sd × An) (ha : R.recOf (plainRec f cfg s t) = some a)
    (hb : R.recOf (plainRec f cfg s u) = some b) :
    R.stmR (a, b) = Tie.entryStatement t u := by
  funext r0 r1
  unfold stmR
  rw [R.plain_recOf _ ht a ha, R.plain_recOf _ hu b hb]
  rfl

end RecReading

/-- The digest of the public files has 32 bytes. -/
theorem size_configurationDigest (files : List ByteArray) :
    (Params.configurationDigest files).size = 32 := by
  unfold Params.configurationDigest Fmt.configDigestW
  rw [formatHashFastForm_eq_formatHash]
  exact Fmt.size_H _ _ _ _ _

/-- **Where the checks of the key file and of the entry file say yes** under chains with one digest,
that of public files, and one shape of the tables: `tableKey`, at the link's field, the planner's
digest and the planner's shape, returns the keys of the two tables' records. -/
theorem checks_keys (p : Model.Verify.Planned) (files : List ByteArray) (key ent : ByteArray)
    (table further : Params.TableName) (hk : Key.check p.chains.key key = .ok table)
    (he : Entry.check (p.chains.bytes .link) table ent = .ok further)
    (hsame : Tie.SameChains p (Params.configurationDigest files)) :
    tableKey p.chains.link.given.plan.field p.cfg p.chains.tableShape table 0 =
        some ((plainRec p.chains.link.given.plan.field p.cfg p.chains.tableShape table).key 0) ∧
      tableKey p.chains.link.given.plan.field p.cfg p.chains.tableShape further 1 =
        some ((plainRec p.chains.link.given.plan.field p.cfg p.chains.tableShape further).key
          1) := by
  obtain ⟨⟨c0, -, -, -, c4, -, -, -⟩, ⟨s1, -, -, -⟩, hread⟩ := hsame
  obtain ⟨j, rounds, dry, S1, r1, s', hrt, -⟩ := Tie.key_check_oneTime _ _ _ hk
  have h0 : table.root.size = 32 := Tie.keyTable_root hrt
  have h1 := entry_check_root _ _ _ _ he
  have hc : p.cfg.size = 32 := by rw [c0]; exact size_configurationDigest _
  obtain ⟨q, k0, k1, S, hq, e0, e1, hS⟩ := entry_check_keys _ _ _ _ he
  obtain rfl : p.chains.link = q := Option.some.inj (hread.symm.trans hq)
  have ecfg : p.chains.link.given.cfg = p.cfg := c4.trans c0.symm
  have esh : p.chains.link.link.table = p.chains.tableShape := s1.symm
  rw [ecfg, esh] at e0 e1
  have a0 := (tableKey_plainRec _ _ _ _ _ _ e0 (by rw [size_nameOf, h0, hc]; decide)).1
  have a1 := (tableKey_plainRec _ _ _ _ _ _ e1 (by rw [size_nameOf, h1, hc]; decide)).1
  exact ⟨a0 ▸ e0, a1 ▸ e1⟩

/-- **Where the checks of the key file and of the entry file say yes** under chains with one digest,
that of public files, and one shape of the tables: both roots and the digest have 32 bytes; the
block that `Tie.entrySpec` (OnBytes/Tie/EntryFile.lean) gives for the two tables is `linkVerify` at
the keys of the two tables' records, at the link's field, the planner's digest and the planner's
shape; and both records fit the shape. That the check read or judged under that block is no part of
this statement. -/
theorem checks_block (p : Model.Verify.Planned) (files : List ByteArray) (key ent : ByteArray)
    (table further : Params.TableName) (hk : Key.check p.chains.key key = .ok table)
    (he : Entry.check (p.chains.bytes .link) table ent = .ok further)
    (hsame : Tie.SameChains p (Params.configurationDigest files)) :
    table.root.size = 32 ∧ further.root.size = 32 ∧ p.cfg.size = 32 ∧
      (plainRec p.chains.link.given.plan.field p.cfg p.chains.tableShape table).Fits
        p.chains.tableShape ∧
      (plainRec p.chains.link.given.plan.field p.cfg p.chains.tableShape further).Fits
        p.chains.tableShape ∧
      ∃ S : Fmt.SpecX, Tie.entrySpec p.chains.link table further =
        some (linkVerify p.chains.link.link
          ((plainRec p.chains.link.given.plan.field p.cfg p.chains.tableShape table).key 0)
          ((plainRec p.chains.link.given.plan.field p.cfg p.chains.tableShape further).key 1),
          S) := by
  obtain ⟨⟨c0, -, -, -, c4, -, -, -⟩, ⟨s1, -, -, -⟩, hread⟩ := hsame
  obtain ⟨j, rounds, dry, S1, r1, s', hrt, -⟩ := Tie.key_check_oneTime _ _ _ hk
  have h0 : table.root.size = 32 := Tie.keyTable_root hrt
  have h1 := entry_check_root _ _ _ _ he
  have hc : p.cfg.size = 32 := by rw [c0]; exact size_configurationDigest _
  obtain ⟨q, k0, k1, S, hq, e0, e1, hS⟩ := entry_check_keys _ _ _ _ he
  obtain rfl : p.chains.link = q := Option.some.inj (hread.symm.trans hq)
  have ecfg : p.chains.link.given.cfg = p.cfg := c4.trans c0.symm
  have esh : p.chains.link.link.table = p.chains.tableShape := s1.symm
  rw [ecfg, esh] at e0 e1
  obtain ⟨rfl, f0⟩ := tableKey_plainRec _ _ _ _ _ _ e0 (by rw [size_nameOf, h0, hc]; decide)
  obtain ⟨rfl, f1⟩ := tableKey_plainRec _ _ _ _ _ _ e1 (by rw [size_nameOf, h1, hc]; decide)
  exact ⟨h0, h1, hc, f0, f1, S, hS⟩

/-- **The same at typed records**: if the two tables' records are good for a pair of readings R,
they are read as typed records a and b; the block that `Tie.entrySpec` gives is `linkVerify` at the
keys of a and b; and the chain's statement is `stmR` at them. -/
theorem block_recOf {Sd An : Type} (R : RecReading Sd An) (p : Model.Verify.Planned)
    (files : List ByteArray) (key ent : ByteArray) (table further : Params.TableName)
    (hk : Key.check p.chains.key key = .ok table)
    (he : Entry.check (p.chains.bytes .link) table ent = .ok further)
    (hsame : Tie.SameChains p (Params.configurationDigest files))
    (g0 : R.Good (plainRec p.chains.link.given.plan.field p.cfg p.chains.tableShape table))
    (g1 : R.Good (plainRec p.chains.link.given.plan.field p.cfg p.chains.tableShape further)) :
    ∃ (a b : Sd × An) (S : Fmt.SpecX),
      R.recOf (plainRec p.chains.link.given.plan.field p.cfg p.chains.tableShape table) = some a ∧
      R.recOf (plainRec p.chains.link.given.plan.field p.cfg p.chains.tableShape further) =
        some b ∧
      Tie.entrySpec p.chains.link table further =
        some (linkVerify p.chains.link.link (R.keyOf a 0) (R.keyOf b 1), S) ∧
      R.stmR (a, b) = Tie.entryStatement table further := by
  obtain ⟨-, -, -, -, -, S, hS⟩ := checks_block p files key ent table further hk he hsame
  obtain ⟨a, ha⟩ := R.recOf_some _ g0
  obtain ⟨b, hb⟩ := R.recOf_some _ g1
  refine ⟨a, b, S, ha, hb, ?_, R.stmR_recOf _ _ _ _ _ g0 g1 a b ha hb⟩
  rw [R.keyOf_recOf _ g0 a ha, R.keyOf_recOf _ g1 b hb]
  exact hS

end OnBytes.K
