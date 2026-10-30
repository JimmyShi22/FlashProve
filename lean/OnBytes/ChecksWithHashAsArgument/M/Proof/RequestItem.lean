-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Proof/RequestItem.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the
program chooses the declarations that differ from the port's and turns names; it does not make the
turn over m. The definitions of OnBytes/Proof/RequestItem.lean that hash, or hand a hash on, written
once more over a monad m in which the hash is asked. The port's own file is untouched. What does not
hash is the port's own. The text written by hand is this project's authors' own rewriting of the
port's file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Proof.RequestItem

namespace OnBytes.TwoPort.M.Proof

open OnBytes.Proof

/-- The value of the item `request`: 177 words, 708 bytes (R15.1, R15.5). The word of the reply is 0
(R15.7). Returns nothing if a line is missing or misspelled, or if a file does not have the form
that 12.3 covers. Call it on an admitted parameter file: lt is not bounded here. -/
def requestItemOf (parameterFile scaleFile requestFile : ByteArray) (digest : Option ByteArray) :
    Option ByteArray := do
  let L := ParamLines.read parameterFile
  let version ← (L.values "version").bind (·.head?)
  let prof ← L.value "prof"
  let ne ← L.value "NE"
  let lt ← L.value "lt"
  if version.length != 4 || prof != 20 || ne == 0 || requestFile.size != 4 * (2 ^ lt + 2) then none
  let w := Fmt.cat [
    word32 0x4D363100, ⟨version.toArray⟩, ← L.words names2, ← L.calls "call",
    ← L.words names37,
    ← L.eight "tsilu", ← L.eight "tsig", ← L.eight "trope", ← secondHashFunctionTree scaleFile,
    ← L.words names103, ← L.eight "texp", ← L.calls "callA", ← L.words names130,
    ← L.calls "callH" (some callHIfNone), ← digest, word32 0, ← L.lastWords]
  if w.size == 708 then some w else none

/-- The value of the item `request`, the request file's digest being asked of `hr`. -/
def requestItem {m : Type → Type} [Monad m] (hr : ByteArray → m (Option ByteArray))
    (parameterFile scaleFile requestFile : ByteArray) : m (Option ByteArray) := do
  let d ← hr requestFile
  pure (requestItemOf parameterFile scaleFile requestFile d)

end OnBytes.TwoPort.M.Proof
