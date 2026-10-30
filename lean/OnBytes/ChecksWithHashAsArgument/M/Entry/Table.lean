-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Entry/Table.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the program
chooses the declarations that differ from the port's and turns names; it does not make the turn over
m. The definitions of OnBytes/Entry/Table.lean that hash, or hand a hash on, written once more
over a monad m in which the hash is asked. The port's own file is untouched. What does not hash is
the port's own. The text written by hand is this project's authors' own rewriting of the port's
file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Entry.Table
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM

namespace OnBytes.TwoPort.M

/-- The seeds of a stored table's record (R4.8): `count` seeds, each a point of `bits` coordinates
and a factor that is not 0. They are drawn from a chain of their own, which starts from the table's
name (R4.10) and nothing else and has one round, in which the prover says nothing. A seed uses at
most 18 words of that round's answer for each coordinate and 36 for its factor (R6.11). The seeds
are drawn by the loop `timesT`, which draws what `Fmt.Dr.times` draws (`timesT_eq`). -/
def recordSeeds {m : Type → Type} [Monad m] (hh : HashM m) (f : Fmt.Fld) (name : ByteArray)
    (bits count : Nat) : m (Option (List (List E × E))) := do
  let first ← Fmt.recordFirstW hh name
  match ← Fmt.Chain.queryW hh ⟨Fmt.recordLabel, first, 0⟩ ByteArray.empty .seeds 0 0
      (Fmt.blocksFor (count * (bits * 18 + 36))) with
  | none => pure none
  | some (_, vb) =>
    pure (some ((timesT (Fmt.drawSeed f bits) count (Fmt.rowOf vb) 0).1.map fun x =>
      (x.1.map E.ofTriple, E.ofTriple x.2)))

/-- The table as the protocol's blocks read it (`TableKey`, OnBytes/Iop/Foldeq.lean; no key file),
from a table's root and answers. `item` is the number of the statement's item that holds the table.
The seeds of the table's record are a function of the table's name (R4.8, R4.10), which takes in the
root, the digest of the public files and the tables' shape. Returns nothing if the number of answers
is not the one that the shape says. -/
def tableKey {m : Type → Type} [Monad m] (hh : HashM m) (f : Fmt.Fld) (cfg : ByteArray)
    (s : Params.IndexShape) (table : Params.TableName) (item : Nat) : m (Option TableKey) := do
  let seeds ←
    recordSeeds hh f
      (Fmt.tableName table.root cfg s.code.logN s.code.ell s.code.r s.v s.answers s.saltBytes)
      s.cubeBits s.answers
  pure (seeds.bind fun seeds =>
    let key : TableKey :=
      { item := item, record := table.answers.toArray, seeds := seeds.map fun x => ⟨x.1, x.2⟩ }
    if key.fits s then some key else none)

end OnBytes.TwoPort.M
