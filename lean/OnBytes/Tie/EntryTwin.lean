-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryTwin.lean: the twin of the port's text over a monad (OnBytes/ChecksWithHashAsArgument/M/), tied to
the plain functions of this folder.

For `LinkE` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean): the typing asks by a twin of the port's own text. The
twin, made by a program over a monad, is tied, at the identity monad and the hash that any function
O induces, to the plain functions (`seedsAt O`, `keyWith`, `readInAt O`, `readWithR`, `checkAskR
O`). So the twin's `Entry.check`, asking, has at every oracle f the value `checkAskR (Run.oB f)`,
but for the name of a refusal; and from main, at the oracle on bit strings made from the format's
hash, it returns the table that `Entry.check` returned.

How far the twin is the port's text: by the program that made it and a diff of three files
(Entry/File, Entry/Table, Proof/Reading); Chain/Reader, Session, Engine and Why are undiffed. At one
place it is not: the round's step. The port runs its engine at queryH := the library's fast step
`Fmt.Chain.queryF` (OnBytes/Hash/Query.lean:28), which hashes what a round's calls share once and is
not written through the hash; the twin has `Fmt.Chain.queryW h` there; tied in values alone, at the
port's hash alone (`step_port`, OnBytes/ChecksWithHashAsArgument/M/AtPort/Chain.lean, which this file does not
import).

Not claimed. That the twin asks the strings that the program hashes is stated nowhere, and of a
plain function Lean cannot state it.

That the twin is the port's text rests on the program that made it, and on a diff, alone. The
equations under OnBytes/ChecksWithHashAsArgument/M/AtPort/ are of values at one hash: the library's reader meets them
too; they say nothing of what is asked.

Values alone: no law here speaks of a log; no count (and on a no the twin asks a second pass, to
name the refusal). A call of the format's hash inside a plain step (Link.read, describe, rounds,
judge, viewOf, readHead, readTable) would stand on both sides of `twin_check`: the law cannot see
it.

For the entry's check alone; at the unpatched oracle; by the entry's own road: no congruence that
the key's or the proof's check could use. No part; nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryAskRec
import OnBytes.ChecksWithHashAsArgument.M.Entry.RoadLands
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineAtId

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.TwoPort

/-! ## The seeds and the keys -/

/-- At the identity monad "first x, then g" is g at x. For letters x and g: nothing is computed. -/
theorem idBind {α β : Type} (x : Id α) (g : α → Id β) : x >>= g = g x := rfl

/-- The twin's `recordSeeds` at the identity monad is `Slice.recordSeedsW` there, at every hash: two
spellings of one text. -/
theorem twin_recordSeeds (h : M.HashM Id) (f : Fmt.Fld) (name : ByteArray) (bits count : Nat) :
    M.recordSeeds (m := Id) h f name bits count =
      Slice.recordSeedsW (m := Id) h f name bits count := by
  rw [Slice.recordSeedsW_pure, M.recordSeeds, idBind, idBind]
  generalize Fmt.Chain.queryW (m := Id) _ _ _ _ _ _ _ = q
  cases q with
  | none => rfl
  | some p =>
    cases p
    rfl

/-- The twin's `tableKey` at the identity monad and the hash that O induces is `keyWith` at the
seeds at O. -/
theorem twin_tableKey (O : ByteArray → ByteArray) (f : Fmt.Fld) (cfg : ByteArray)
    (s : Params.IndexShape) (table : Params.TableName) (item : Nat) :
    M.tableKey (m := Id) (Fmt.HO O) f cfg s table item = keyWith (seedsAt O) f cfg s
        table item := by
  unfold M.tableKey keyWith seedsAt
  simp only [twin_recordSeeds]
  rfl

/-! ## The reader -/

/-- The twin's reading step of a session, at the identity monad and the hash that O induces, is
`readInAt O`: by `EngineAtId.readChain_id` (the program's reader over m, at the identity monad, is
the library's strict reader, at every hash). -/
theorem twin_readIn (O : ByteArray → ByteArray) (S : Fmt.SpecX) (b : ByteArray) (i : Nat)
    (s : Session) : (M.readIn (m := Id) (Fmt.HO O) S b i s).run = readInAt O S b i s := by
  unfold M.readIn readInAt
  show (match M.readChain (m := Id) (Fmt.HO O) S s.seen b i with
    | none => _
    | some (o, j) => _) = _
  rw [M.EngineAtId.readChain_id]
  cases Fmt.readChainX (m := Id) (Fmt.HO O) S s.seen b i <;> rfl

/-- So the twin's named reading from the start is, but for the name of a refusal, `readInAt O`'s
run. -/
theorem twin_readNamed (O : ByteArray → ByteArray) (front : String) (S : Fmt.SpecX)
    (b : ByteArray) (i : Nat) :
    (M.Proof.Reading.fromStart (M.Proof.readNamed (m := Id) (Fmt.HO O) front S b i)).toOption =
      (readInAt O S b i).run := by
  unfold M.Proof.Reading.fromStart M.Proof.readNamed InSession.run
  rw [twin_readIn]
  cases readInAt O S b i Session.start <;> rfl

/-! ## Reading and check -/

/-- The twin's `Entry.read`, at the identity monad and the hash that O induces, is, but for the
name of a refusal, `readWithR` at the strict reader and the seeds at O. NO
HYPOTHESIS. -/
theorem twin_read (O : ByteArray → ByteArray) (p : Params.Link) (first : Params.TableName)
    (file : ByteArray) :
    (M.Entry.read (m := Id) (Fmt.HO O) p first file).toOption =
      readWithR (readInAt O) (seedsAt O) p first file := by
  unfold M.Entry.read readWithR entryPlaceR
  dsimp only
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
        show (Except.toOption (match
            M.tableKey (m := Id) (Fmt.HO O) p.given.plan.field p.given.cfg p.link.table first 0,
            M.tableKey (m := Id) (Fmt.HO O) p.given.plan.field p.given.cfg p.link.table further 1
          with
          | some k0, some k1 => _
          | _, _ => _)) = _
        rw [twin_tableKey, twin_tableKey]
        generalize keyWith (seedsAt O) p.given.plan.field p.given.cfg p.link.table first 0 = K0
        generalize keyWith (seedsAt O) p.given.plan.field p.given.cfg p.link.table further 1 = K1
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
              have e := twin_readNamed O "" spec file j
              show (Except.toOption (match M.Proof.Reading.fromStart
                  (M.Proof.readNamed (m := Id) (Fmt.HO O) "" spec file j) with
                | .error e => _
                | .ok r => _)) = _
              rw [← e]
              cases M.Proof.Reading.fromStart
                  (M.Proof.readNamed (m := Id) (Fmt.HO O) "" spec file j) with
              | error e => rfl
              | ok r =>
                dsimp only [Except.toOption]
                generalize (r.next != file.size) = d
                cases d <;> rfl

/-- The twin's `Entry.check`, at the identity monad and the hash that O induces, is, but for the
name of a refusal, `checkAskR O`. AT EVERY `answers`, 0 TOO; NO HYPOTHESIS. -/
theorem twin_check (O : ByteArray → ByteArray) (params : ByteArray) (first : Params.TableName)
    (file : ByteArray) :
    (M.Entry.check (m := Id) (Fmt.HO O) params first file).toOption =
      checkAskR O params first file := by
  unfold M.Entry.check checkAskR checkWithR
  cases hq : Params.Link.read params with
  | none => rfl
  | some q =>
    dsimp only
    rw [← twin_read O q first file]
    show (Except.toOption (match M.Entry.read (m := Id) (Fmt.HO O) q first file with
      | .error e => _
      | .ok r => _)) = _
    cases hr : M.Entry.read (m := Id) (Fmt.HO O) q first file with
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

/-! ## The twin, asking -/

/-- THE TWIN's `Entry.check`, OVER THE MONAD OF TREES OF QUERIES, AT THE HASH THAT ASKS THE ONE
ORACLE: run at f it is, but for the name of a refusal, `checkAskR` at the function that f induces.
AT EVERY `answers`, 0 TOO; NO HYPOTHESIS. By `RoadLands.check_det` and `twin_check`. An equation of
VALUES: of what it asks no law speaks. -/
theorem twin_check_det (f : ZKCP.Oracle 256) (params : ByteArray) (first : Params.TableName)
    (file : ByteArray) :
    ((M.Entry.check (Fmt.HM Run.askB) params first file).det f).toOption =
      checkAskR (Run.oB f) params first file := by
  rw [M.RoadLands.check_det]
  exact twin_check (Run.oB f) params first file

/-- FROM THE ENTRY FUNCTION. Under `ZeroFacts` and `SaysRecordLines`, at c := the digest of the
three configuration files as read: THE TWIN's `Entry.check`, ASKING, run at the oracle on bit
strings that is made from the format's hash, on `recordBytesAt c`, the table that `Key.check`
returned and the entry file's bytes, returns the table that `Entry.check` returned. One fixed
oracle; at Run.oBits, not at the patched hash of (b) in OnBytes/TypedOracleCompiler/Slice/Shapes.lean. c is a
constant in the parameter bytes, BLAKE2b's. It tosses no coin (`RoadLands.check_noCoin`).
`SaysRecordLines` is proved of no file; no file is shown a yes. -/
theorem zero_twin_asks {args : List String} {s s' : OnBytes.Shell.World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) (hs : SaysRecordLines w.r.pol) :
    (M.Entry.check (Fmt.HM Run.askB)
      (recordBytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])) w.table w.ent).det
        (Run.oBits ()) = .ok w.further := by
  have e := (twin_check_det (Run.oBits ()) _ w.table w.ent).trans (zero_record_ask h hs)
  cases hx : (M.Entry.check (Fmt.HM Run.askB)
      (recordBytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])) w.table w.ent).det
        (Run.oBits ()) with
  | error r =>
    rw [hx] at e
    cases e
  | ok t =>
    rw [hx] at e
    exact congrArg Except.ok (Option.some.inj e)

end OnBytes.Tie
