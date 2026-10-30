-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryWithRec.lean: `Entry.read` and `Entry.check` written a second time, with the
chain's reader as a parameter rd (`entryPlaceR`, `readWithR`, `checkWithR`).
The function that gives a record's seeds is a second parameter sd, beside the reader rd. At the
program it is `recordSeeds`; at an oracle it would be `recordSeedsW` at the oracle's hash.
Not claimed. Nothing here says who pays for the seeds' calls under an oracle. By their text
`readWithR` and `checkWithR` call no hash but through rd and sd; that is no theorem. Neither is a
part of the program, which runs `Entry.check`. For a general rd nothing here ties the view of what
it returns to its output, or the place where it ended to the bytes.
-/
import OnBytes.Tie.EntryWith

set_option autoImplicit false

namespace OnBytes.Tie

/-- The type of `recordSeeds`. -/
abbrev Seeds : Type := Fmt.Fld → ByteArray → Nat → Nat → Option (List (List E × E))

/-- `tableKey`'s text with the function that gives the seeds as a parameter. By its text it calls no
hash but through sd. -/
def keyWith (sd : Seeds) (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : Params.TableName) (item : Nat) : Option TableKey := do
  let seeds ←
    sd f
      (Fmt.tableName table.root cfg s.code.logN s.code.ell s.code.r s.v s.answers s.saltBytes)
      s.cubeBits s.answers
  let key : TableKey :=
    { item := item, record := table.answers.toArray, seeds := seeds.map fun x => ⟨x.1, x.2⟩ }
  if key.fits s then some key else none

/-- The program's `tableKey` is `keyWith` at the program's `recordSeeds`. -/
theorem tableKey_keyWith (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : Params.TableName) (item : Nat) :
    tableKey f cfg s table item = keyWith recordSeeds f cfg s table item := rfl

/-- A key that `keyWith` returns fits the shape and holds the item's number that was asked, whatever
sd. -/
theorem keyWith_fits {sd : Seeds} {f : Fmt.Fld} {cfg : ByteArray} {s : Params.IndexShape}
    {table : Params.TableName} {item : Nat} {k : TableKey}
    (h : keyWith sd f cfg s table item = some k) : k.fits s = true ∧ k.item = item := by
  unfold keyWith at h
  dsimp only at h
  obtain ⟨seeds, _, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · rename_i hf
    cases h
    exact ⟨hf, rfl⟩
  · cases h

/-- `Entry.read`'s text up to the reading of the chain,
with `keyWith sd` for `tableKey`. -/
def entryPlaceR (sd : Seeds) (p : Params.Link) (first : Params.TableName) (file : ByteArray) :
    Option EntryPlace :=
  let f := p.given.plan.field
  let shape := p.link.table
  match Proof.readHead f .entry file with
  | .error _ => none
  | .ok i =>
    if f != .two || p.given.cfg == Fmt.zero32 then none else
    match readTable f (shape.rows * shape.answers) file i with
    | .error _ => none
    | .ok (further, j) =>
      match keyWith sd f p.given.cfg shape first 0, keyWith sd f p.given.cfg shape further 1 with
      | some k0, some k1 =>
        let block := linkVerify p.link k0 k1
        match (block.rounds (Entry.start p)).bind (p.describe first further) with
        | none => none
        | some spec => some ⟨further, block, spec, j⟩
      | _, _ => none

/-- `Entry.read` at the reader rd, over `entryPlaceR`. -/
def readWithR (rd : Fmt.SpecX → ByteArray → Nat → InSession ChainRead) (sd : Seeds)
    (p : Params.Link) (first : Params.TableName) (file : ByteArray) : Option Entry.EntryRead :=
  match entryPlaceR sd p first file with
  | none => none
  | some P =>
    match (rd P.spec file P.byte).run with
    | none => none
    | some r => if r.next != file.size then none else some ⟨P.further, P.block, r⟩

/-- `Entry.check` at the reader rd, over `readWithR`. -/
def checkWithR (rd : Fmt.SpecX → ByteArray → Nat → InSession ChainRead) (sd : Seeds)
    (params : ByteArray) (first : Params.TableName) (file : ByteArray) :
    Option Params.TableName :=
  match Params.Link.read params with
  | none => none
  | some p =>
    match readWithR rd sd p first file with
    | none => none
    | some r => if r.block.decides (Entry.start p) r.chain.view then some r.further else none

/-! ## Against the program -/

/-! ## At the program's own reader and seeds they are the program -/

/-- **`readWithR` at the program's own reader and seeds returns what `Entry.read` returns, but for
the name of a refusal. NO HYPOTHESIS ON THE RECORD.** -/
theorem readWithR_readIn (p : Params.Link) (first : Params.TableName) (file : ByteArray) :
    readWithR readIn recordSeeds p first file = (Entry.read p first file).toOption := by
  unfold readWithR entryPlaceR Entry.read
  simp only [← tableKey_keyWith]
  generalize Proof.readHead p.given.plan.field .entry file = H
  cases H with
  | error e => rfl
  | ok i =>
    dsimp only
    generalize (p.given.plan.field != .two || p.given.cfg == Fmt.zero32) = c
    cases c with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, if_false]
      generalize readTable p.given.plan.field _ file i = T
      cases T with
      | error e => rfl
      | ok x =>
        obtain ⟨further, j⟩ := x
        dsimp only
        generalize tableKey p.given.plan.field p.given.cfg p.link.table first 0 = K0
        generalize tableKey p.given.plan.field p.given.cfg p.link.table further 1 = K1
        cases K0 with
        | none => rfl
        | some k0 =>
          cases K1 with
          | none => rfl
          | some k1 =>
            dsimp only
            generalize ((linkVerify p.link k0 k1).rounds (Entry.start p)).bind
              (p.describe first further) = D
            cases D with
            | none => rfl
            | some spec =>
              dsimp only
              unfold InSession.run Proof.Reading.fromStart Proof.readNamed
              generalize readIn spec file j Session.start = R
              cases R with
              | none => rfl
              | some y =>
                dsimp only [Option.map, Except.map]
                generalize (y.1.next != file.size) = d
                cases d <;> rfl

/-- **`checkWithR` at the program's own reader and seeds returns what `Entry.check` returns, but for
the name of a refusal. NO HYPOTHESIS AT ALL.** -/
theorem checkWithR_readIn (params : ByteArray) (first : Params.TableName) (file : ByteArray) :
    checkWithR readIn recordSeeds params first file = (Entry.check params first file).toOption := by
  unfold checkWithR Entry.check
  cases hq : Params.Link.read params with
  | none => rfl
  | some q =>
    dsimp only
    rw [readWithR_readIn q first file]
    cases hr : Entry.read q first file with
    | error e => rfl
    | ok r =>
      dsimp only [Except.toOption]
      unfold Proof.judge
      cases hd : r.block.decides (Entry.start q) r.chain.view with
      | true =>
        rw [(Blk.decides_iff_runOn _ _ _).1 hd]
        rfl
      | false =>
        cases hw : r.block.runOn (Entry.start q) r.chain.view with
        | ok u =>
          cases u
          rw [(Blk.decides_iff_runOn _ _ _).2 hw] at hd
          cases hd
        | error f => rfl

end OnBytes.Tie

#print axioms OnBytes.Tie.tableKey_keyWith
#print axioms OnBytes.Tie.keyWith_fits
#print axioms OnBytes.Tie.readWithR_readIn
#print axioms OnBytes.Tie.checkWithR_readIn
