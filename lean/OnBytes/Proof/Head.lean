-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Proof/Head.lean: the heads of the three kinds of file, and a proof file's third word.

Every file of the programs begins with four bytes that say what kind of file it is and four bytes
that name the format's version (docs/format/FORMAT.md, R13.1). The version is four characters:
'H', the format's number, the field's number, the hash's number. A proof file has four more bytes:
the number of the stored copy of the table on which the proof was made (R14.2). The C++ counterparts
are read_head (blocks/frame/heads.h) and version_refusal (blocks/frame/version.h).

Main definitions: `FileKind`, `versionRefusal`, `readHead`, `readProofHead`, `headNames`.

What is not claimed: that the number belongs to the table that a caller holds. The caller compares.
-/
import OnBytes.Base

namespace OnBytes.Proof

/-- The three kinds of file that begin with a head. -/
inductive FileKind where
  /-- comes with a commitment and holds the first table's root -/
  | key
  /-- comes with a further stored copy of the table -/
  | entry
  /-- goes to one client and is about one request -/
  | proof
  deriving DecidableEq, Repr, Inhabited

/-- The first four bytes of a file of this kind. -/
def FileKind.tag : FileKind → ByteArray
  | .key => Fmt.ascii "CPIK"
  | .entry => Fmt.ascii "CPEN"
  | .proof => Fmt.ascii "CPPF"

/-- The four bytes that name the format's version for a field. -/
def versionOf (f : Fmt.Fld) : ByteArray := (Fmt.versionValue f).extract 0 4

/-- Why four bytes are not the version that this program reads for the field f, in the words of the
C++ reader (version_refusal): a format whose number, the second character, is 'G' or '7'; this
format for another field; this format for another hash; or nothing that is known. Call it only on
bytes that differ from the version that is read: on that version itself it answers
"version-of-another-hash", where the C++ routine answers that nothing is wrong. -/
def versionRefusal (f : Fmt.Fld) (w : ByteArray) : String :=
  let served := versionOf f
  let at' := fun (i : Nat) => Fmt.byteAt w i
  if at' 0 == 0x48 && (at' 1 == 0x47 || at' 1 == 0x37) then "version-of-an-earlier-format"
  else if at' 0 == 0x48 && at' 1 == Fmt.byteAt served 1 && at' 2 != Fmt.byteAt served 2 then
    "version-of-another-field"
  else if at' 0 == 0x48 && at' 1 == Fmt.byteAt served 1 then "version-of-another-hash"
  else "version-unknown"

/-- Reads the eight bytes of a head at the start of b. Returns the place after them, or the name
of the test that failed. The tests are made in the order of the C++ reader (read_head). -/
def readHead (f : Fmt.Fld) (k : FileKind) (b : ByteArray) : Except String Nat :=
  if b.size < 8 then .error "file-too-short"
  else if b.extract 0 4 != k.tag then .error "file-of-another-kind"
  else if b.extract 4 8 != versionOf f then .error (versionRefusal f (b.extract 4 8))
  else .ok 8

/-- A number of four bytes, the lowest byte first, at the place i of b. Bytes beyond the end of b
count as 0: test the length first. -/
def word32At (b : ByteArray) (i : Nat) : Nat := Fmt.leNat b i 4

/-- Reads the twelve bytes of a proof file's head. Returns the number of the stored copy and the
place after the head, or the name of the test that failed. -/
def readProofHead (f : Fmt.Fld) (b : ByteArray) : Except String (Nat × Nat) :=
  match readHead f .proof b with
  | .error e => .error e
  | .ok i => if b.size < i + 4 then .error "file-too-short" else .ok (word32At b i, i + 4)

/-- The names under which the readers of this file refuse. -/
def headNames : List String :=
  ["file-too-short", "file-of-another-kind", "version-of-an-earlier-format",
   "version-of-another-field", "version-of-another-hash", "version-unknown"]

end OnBytes.Proof
