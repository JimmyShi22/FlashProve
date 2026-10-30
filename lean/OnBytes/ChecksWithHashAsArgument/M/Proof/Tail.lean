-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Proof/Tail.lean: the definition of OnBytes/Proof/Tail.lean that hands a hash on
(`readTail`), written once more over a monad m in which the hash is asked, by this project's
authors, after that file's text. What does not hash is that file's own.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Proof.Tail
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader
import OnBytes.ChecksWithHashAsArgument.M.Chain.Session
import OnBytes.ChecksWithHashAsArgument.M.Chain.Why
import OnBytes.ChecksWithHashAsArgument.M.Entry.Table
import OnBytes.ChecksWithHashAsArgument.M.Proof.Place
import OnBytes.ChecksWithHashAsArgument.M.Proof.Reading

namespace OnBytes.TwoPort.M.Proof

open OnBytes.Proof

open Params (LinShape)

/-- Reads a tail in b after the first chain. `dry` is what the dry run of the first chain's block
has returned. The names of the refusals say which part of the file was refused. -/
def readTail {m : Type → Type} [Monad m] (hh : HashM m) (p : TailPublic) (dry : FirstEnd)
    (first : ChainRead) (b : ByteArray) : Reading m TailRead := do
  let g := p.shared.given
  let seal1 ← need "first-chain-seal" first.seal
  let place ← needM "place" (readPlace hh p.binding g.cfg seal1 b first.next)
  let key ← needM "table-record" (tableKey hh g.plan.field g.cfg p.lin.fold.index p.table 0)
  let (rounds2, end2) ← need "shared-chain-parameters"
    ((sharedBlock p.lin key).dryRun (sharedStart p))
  let spec2 ← need "shared-chain-parameters" (p.shared.describe p.lab₂ p.table place.root rounds2)
  let shared ← readNamed hh "shared-chain-" spec2 b place.next
  let seal2 ← need "shared-chain-seal" shared.seal
  let rounds3 ← need "second-chain-parameters"
    ((secondBlock p.lin dry.lin (end2.goesOn shared)).rounds (secondStart p dry first))
  let spec3 ← need "second-chain-parameters"
    (p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree first))
  let second ← readNamed hh "second-chain-" spec3 b shared.next
  pure ⟨first, place, key, shared, second⟩

end OnBytes.TwoPort.M.Proof
