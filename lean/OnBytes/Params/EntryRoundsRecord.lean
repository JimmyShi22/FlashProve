-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryRoundsRecord.lean: the description of an entry's chain does not depend on the
tables but for its statement, if the rounds that the dry run of a link's
block states depend on the tables' keys through their sizes and items alone.

OnBytes/Params/EntryRounds.lean proves, at `answers = 0`, that the two tables enter the
description of an entry's chain through its statement alone. There a table's key is its item's
number. In general the key also holds the record's answers and its seeds, which are a hash of the
format's name of the table, so the block is made of them. This file states like laws
for any tables, under one hypothesis, `LinkDryBySizes`: the dry run of the
block of a link, from any start, states the same rounds, with the same stored openings, or none, at
any two pairs of keys that fit the tables' shape and name the same items.
OnBytes/Params/EntryDescRecord.lean takes that hypothesis away, by a law of
OnBytes/Iop/DrySizes.lean. A key that `tableKey` returns fits the shape, names its item and has the
table's answers as its record (`tableKey_parts`, `tableKey_fits`, `tableKey_record`). `zeroKey` is a
key of the sizes that a shape says, made of zeros, with the factor one in its seeds; it fits
(`zeroKey_fits`). `entryRoundsAny` is
the dry run's rounds at two such keys: a function of the parameter bytes.
Then: if `Tie.entrySpec` gives a
block and a description, the block is the link's block at the two tables' own keys, and the
description is made of `entryRoundsAny` and of the statement (`entrySpec_eq_any`); its rounds,
stored openings, plan and statement (`entrySpec_rounds_any`); at two other tables the description is
the same but for its statement (`entrySpec_at_any`). Where it gives one, each table has as many
answers as the shape says, rows times answers (`entrySpec_answers`; this one needs no hypothesis).

Main definitions: `LinkDryBySizes`, `zeroKey`, `entryRoundsAny`.
Main theorems: `tableKey_parts`, `tableKey_fits`, `tableKey_record`, `zeroKey_fits`,
`entrySpec_eq_any`, `entrySpec_answers`,
`entrySpec_rounds_any`, `entrySpec_at_any`.
What is not claimed: `LinkDryBySizes` of any shape: it is a hypothesis here, and no file that this
one imports proves it. That the block is a function of the
parameter bytes: it is made of the tables' answers and seeds, and the clause `block =
entryBlock p` of OnBytes/Params/EntryRounds.lean has no like here; so nothing
here serves where the block's decision must be fixed before the tables are known. Nothing on the
seeds' values. That `Tie.entrySpec` gives a description. For proofs only; the program, that is the
Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.EntryRounds

set_option autoImplicit false

namespace OnBytes.Params

/-- The dry run of the block of a link of the shape S, from any start, states the same rounds, with
the same stored openings, or none, at any two pairs of keys that fit the tables' shape and name the
same items. -/
def LinkDryBySizes (S : LinkShape) : Prop :=
  ∀ (st : Start) (k0 k0' k1 k1' : TableKey), k0.fits S.table = true → k0'.fits S.table = true →
    k1.fits S.table = true → k1'.fits S.table = true → k0.item = k0'.item → k1.item = k1'.item →
    (linkVerify S k0 k1).rounds st = (linkVerify S k0' k1').rounds st

/-- What `tableKey` returns, whatever the seeds are: a key that fits the shape, names the item and
has the table's answers as its record. -/
theorem tableKey_parts {f : Fmt.Fld} {cfg : ByteArray} {s : IndexShape} {t : TableName} {item : Nat}
    {k : TableKey} (h : tableKey f cfg s t item = some k) :
    k.fits s = true ∧ k.item = item ∧ k.record = t.answers.toArray := by
  have key : ∀ o : Option (List (List E × E)),
      (o.bind fun y =>
        if ({ item := item, record := t.answers.toArray,
              seeds := y.map fun x => ⟨x.1, x.2⟩ } : TableKey).fits s then
          some ({ item := item, record := t.answers.toArray,
                  seeds := y.map fun x => ⟨x.1, x.2⟩ } : TableKey)
        else none) = some k →
      k.fits s = true ∧ k.item = item ∧ k.record = t.answers.toArray := by
    intro o ho
    obtain ⟨y, _, hy⟩ := Option.bind_eq_some_iff.mp ho
    split at hy
    · rename_i hfit
      cases hy
      exact ⟨hfit, rfl, rfl⟩
    · cases hy
  unfold tableKey at h
  dsimp only at h
  exact key _ h

/-- A key that `tableKey` returns fits the shape and names the item. -/
theorem tableKey_fits {f : Fmt.Fld} {cfg : ByteArray} {s : IndexShape} {t : TableName} {item : Nat}
    {k : TableKey} (h : tableKey f cfg s t item = some k) : k.fits s = true ∧ k.item = item :=
  ⟨(tableKey_parts h).1, (tableKey_parts h).2.1⟩

/-- The record of a key that `tableKey` returns is the table's answers. -/
theorem tableKey_record {f : Fmt.Fld} {cfg : ByteArray} {s : IndexShape} {t : TableName}
    {item : Nat} {k : TableKey} (h : tableKey f cfg s t item = some k) :
    k.record = t.answers.toArray := (tableKey_parts h).2.2

/-- A key of the sizes that the shape s says: a record of zeros, and seeds with points of zeros and
the factor one. -/
def zeroKey (s : IndexShape) (item : Nat) : TableKey :=
  { item := item, record := Array.replicate (s.rows * s.answers) zeroE,
    seeds := List.replicate s.answers ⟨List.replicate s.cubeBits zeroE, oneE⟩ }

/-- It fits the shape. -/
theorem zeroKey_fits (s : IndexShape) (item : Nat) : (zeroKey s item).fits s = true := by
  simp [zeroKey, TableKey.fits]

/-- The rounds that the dry run of a link's block states at keys of zeros, each with the stored
trees that it opens. -/
def entryRoundsAny (p : Link) : Option Rounds :=
  (linkVerify p.link (zeroKey p.link.table 0) (zeroKey p.link.table 1)).rounds (Entry.start p)

section
variable {p : Link} {first further : TableName} {block : Blk Unit} {S : Fmt.SpecX}

/-- If `Tie.entrySpec` gives a block and a description: the block is
the link's block at the two tables' own keys, and the description is made of the rounds at keys of
zeros and of the statement. -/
theorem entrySpec_eq_any (H : LinkDryBySizes p.link)
    (h : Tie.entrySpec p first further = some (block, S)) :
    (∃ k0 k1, tableKey p.given.plan.field p.given.cfg p.link.table first 0 = some k0 ∧
      tableKey p.given.plan.field p.given.cfg p.link.table further 1 = some k1 ∧
      block = linkVerify p.link k0 k1) ∧
      ∃ r, entryRoundsAny p = some r ∧ S = entrySpecOf p r (Link.statement first further) := by
  unfold Tie.entrySpec at h
  split at h
  · rename_i k0 k1 h0 h1
    have e : (linkVerify p.link k0 k1).rounds (Entry.start p) = entryRoundsAny p :=
      H _ _ _ _ _ (tableKey_fits h0).1 (zeroKey_fits _ _) (tableKey_fits h1).1 (zeroKey_fits _ _)
        (tableKey_fits h0).2 (tableKey_fits h1).2
    rw [e] at h
    cases hr : entryRoundsAny p with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hd : p.describe first further r with
      | none => rw [hd] at h; cases h
      | some S' =>
        rw [hd] at h
        have e' := Option.some.inj h
        have e1 : linkVerify p.link k0 k1 = block := congrArg (·.1) e'
        have e2 : S' = S := congrArg (·.2) e'
        refine ⟨⟨k0, k1, h0, h1, e1.symm⟩, r, rfl, ?_⟩
        rw [← e2]
        exact Given.describe_eq hd
  · cases h

/-- Where `Tie.entrySpec` gives a description, each table has as many answers as the shape says:
the number of rows times the answers of a row. No hypothesis on the dry run. -/
theorem entrySpec_answers (h : Tie.entrySpec p first further = some (block, S)) :
    first.answers.length = p.link.table.rows * p.link.table.answers ∧
      further.answers.length = p.link.table.rows * p.link.table.answers := by
  unfold Tie.entrySpec at h
  split at h
  · rename_i k0 k1 h0 h1
    have f0 := (tableKey_fits h0).1
    have f1 := (tableKey_fits h1).1
    simp only [TableKey.fits, Bool.and_eq_true, beq_iff_eq] at f0 f1
    rw [tableKey_record h0] at f0
    rw [tableKey_record h1] at f1
    exact ⟨by simpa using f0.1.1, by simpa using f1.1.1⟩
  · cases h

/-- For all tables, if `Tie.entrySpec` gives a description and the dry
run at keys of zeros states the rounds r: the description's rounds and stored openings are those of
r, its plan is the parameter bytes' plan, and its statement is the link's statement on the two
tables. -/
theorem entrySpec_rounds_any {r : Rounds} (H : LinkDryBySizes p.link)
    (hr : entryRoundsAny p = some r) (h : Tie.entrySpec p first further = some (block, S)) :
    S.base.rounds = r.map (·.1) ∧ S.stored = r.map (·.2) ∧ S.base.plan = p.given.plan ∧
      S.base.statement = Link.statement first further := by
  obtain ⟨_, r', hr', hS⟩ := entrySpec_eq_any H h
  rw [hr] at hr'
  cases hr'
  rw [hS]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A description that `Tie.entrySpec` gives at two tables is the one that
it gives at two others, but for its statement. Of the two blocks nothing is said: a
block depends on its tables' answers and seeds. -/
theorem entrySpec_at_any {first' further' : TableName} {block' : Blk Unit} {S' : Fmt.SpecX}
    (H : LinkDryBySizes p.link) (h : Tie.entrySpec p first further = some (block, S))
    (h' : Tie.entrySpec p first' further' = some (block', S')) :
    S = { S' with base := { S'.base with statement := Link.statement first further } } := by
  obtain ⟨_, r, hr, hS⟩ := entrySpec_eq_any H h
  obtain ⟨_, r', hr', hS'⟩ := entrySpec_eq_any H h'
  rw [hr] at hr'
  cases hr'
  rw [hS, hS']
  rfl

end

end OnBytes.Params
