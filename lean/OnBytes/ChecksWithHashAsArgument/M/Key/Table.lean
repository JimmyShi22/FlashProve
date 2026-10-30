-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Key/Table.lean: the definitions of OnBytes/Key/Table.lean that hash, or hand a
hash on (`seedsOf`, `commitmentIdAt`, `commitmentId`), written once more over a monad m in which the
hash is asked. All three are typed by hand, by this project's authors, after that file's text. What
does not hash is that file's own.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Key.Table
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Entry.Table

namespace OnBytes.TwoPort.M.Key

open OnBytes.Key

open OnBytes.Params (TableName IndexShape)

/-- The seeds of the table's record (R4.8). s is the tables' shape, cfg the digest of the public
files, t the table. The seeds are drawn from the table's name. Returns nothing if the drawing
fails. -/
def seedsOf {m : Type → Type} [Monad m] (hh : HashM m) (s : IndexShape) (cfg : ByteArray)
    (t : TableName) : m (Option (List (List E × E))) :=
  TwoPort.M.recordSeeds hh .two (nameOf s cfg t) s.cubeBits s.answers

/-- The commitment ID (R4.11) at given seeds: 32 bytes. told is the closing list: the format leaves
it empty, and `commitmentId` passes the empty list. The seeds enter as one flat list: seed by seed,
the coordinates of its point and then its factor. One call of the hash; no seed is drawn here. -/
def commitmentIdAt {m : Type → Type} [Monad m] (hh : HashM m) (s : IndexShape) (cfg : ByteArray)
    (told : List ByteArray) (t : TableName) (seeds : List (List E × E)) : m ByteArray :=
  Fmt.publishedIDW hh cfg (nameOf s cfg t) ((seeds.flatMap fun y => y.1 ++ [y.2]).map E.triple)
    (t.answers.map E.triple) told

/-- The commitment ID: 32 bytes. It draws the record's seeds itself (`seedsOf`), then makes the one
call, with the empty closing list: the string ends in the word 0. If `seedsOf` returns nothing, the
empty list stands in the seeds' place, as in the port. -/
def commitmentId {m : Type → Type} [Monad m] (hh : HashM m) (s : IndexShape) (cfg : ByteArray)
    (t : TableName) : m ByteArray := do
  let seeds ← TwoPort.M.Key.seedsOf hh s cfg t
  TwoPort.M.Key.commitmentIdAt hh s cfg [] t (seeds.getD [])

end OnBytes.TwoPort.M.Key
