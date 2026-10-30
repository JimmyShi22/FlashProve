-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Key/File.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the program
chooses the declarations that differ from the port's and turns names; it does not make the turn over
m. The definitions of OnBytes/Key/File.lean that hash, or hand a hash on, written once more
over a monad m in which the hash is asked. The port's own file is untouched. What does not hash is
the port's own. The text written by hand is this project's authors' own rewriting of the port's
file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Key.File
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader
import OnBytes.ChecksWithHashAsArgument.M.Chain.Session
import OnBytes.ChecksWithHashAsArgument.M.Chain.Why
import OnBytes.ChecksWithHashAsArgument.M.Entry.Table
import OnBytes.ChecksWithHashAsArgument.M.Key.Table
import OnBytes.ChecksWithHashAsArgument.M.Proof.Place
import OnBytes.ChecksWithHashAsArgument.M.Proof.Reading
import OnBytes.ChecksWithHashAsArgument.M.Proof.Tail

namespace OnBytes.TwoPort.M.Key

open OnBytes.Key

open OnBytes.Params (KeyChains TableName)
open OnBytes.Proof (TailPublic TailRead judge tailRefusal)
open OnBytes.TwoPort.M.Proof (Reading need readNamed readTail)

/-- Reads the three chains of a key file. j is the place of the first byte after the record's
answers. The names of the refusals say which part of the file was refused and, where the strict
reader refused, at which kind of check. -/
def readKey {m : Type → Type} [Monad m] (hh : HashM m) (k : KeyChains) (table : TableName)
    (file : ByteArray) (j : Nat) : Reading m TailRead := do
  let p := k.oneTime
  let (rounds, dry) ← need "one-time-chain-parameters" ((oneTime p).dryRun (startOf p))
  let spec ← need "one-time-chain-parameters" (p.describe table rounds)
  let first ← readNamed hh "one-time-chain-" spec file j
  let r ← readTail hh (tailPublic k table) dry first file
  if r.next != file.size then throw "bytes-left-over"
  pure r

/-- Checks the key file `file` under the parameter bytes of its three chains. Returns what a reader
keeps of the table, for every later entry and proof, or the first check that failed. A key file is
read under a record of tree vertices of its own. -/
def check {m : Type → Type} [Monad m] (hh : HashM m) (k : KeyChains) (file : ByteArray) :
    m (Except Refusal TableName) :=
  let p := k.oneTime
  if p.given.plan.field != .two then pure (.error ⟨.configuration, "key-field"⟩)
  else if !admitted p then pure (.error ⟨.configuration, "key-values"⟩)
  else
    match OnBytes.Key.readTable p.lin.fold.index p.given.cfg file with
    | .error e => pure (.error e)
    | .ok (table, j) => do
      match ← (readKey hh k table file j).fromStart with
      | .error why => pure (no why)
      | .ok r =>
        match keyRefusal k table r with
        | some why => pure (no why)
        | none => pure (.ok table)

end OnBytes.TwoPort.M.Key
