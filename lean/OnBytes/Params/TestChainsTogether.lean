-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestChainsTogether.lean: tests of the two readers that take the parameter bytes of
all chains of one file, KeyChains.read and ProofChains.read (OnBytes/Params/Chains.lean): what they
refuse. And one test of Fmt.headOf at the toy's two files.

1. A key's three chains, at the parameter bytes of the toy key that the programs wrote
   (OnBytes/Entry/RecordToyFiles.lean). The three strings are read, each alone and together. Read
   and spelled again they are the programs' bytes. Then one thing is changed in one string, which is
   spelled again (13 changes), or a whole string stands in another's place (two). KeyChains.read
   refuses each. At 12 of the 15 each string alone is still read, so it is a test on the chains
   together that refuses.
2. A proof's three chains, at made-up parameter bytes: read alone and together; nine changes,
   refused. Among them the case of FORMAT.md 18, "Three items that two chains of one file both
   hold": the items "the test on the table" tell the matrix 22 rows in the first chain and 21 in the
   shared chain.
3. A limit, held by a test: KeyChains.read does not ask that the one-time chain's plan has the entry
   RECORD, which R13.15 asks of it.
4. The first eight bytes of the toy's key file and entry file are the head that Fmt.headOf writes.

Where the expected values come from. By R13.5 and R14.9 a verifier compares "codes" and "the test on
the table" between the first and the shared chain and rejects if one differs. By R13.15 and R14.3,
of the six chains of a key file and a proof file the key's one-time chain alone has the entry
RECORD. By FORMAT.md 18, "One setting", the first seven words are the same in all plans, and the
item "configuration" is the digest of the same public files (R4.9). Whether a changed string is read
alone follows from the docstrings of Given.read and of the chains' readers; 3 follows from the text
of KeyChains.read. All was worked out by hand.

Every test is checked when the file compiles. The Lean text verify-on-bytes does not import it.

Not claimed. No theorem. The changed strings are made up: no public files give them. No file is read
under them. The readers under test do not hold an item's numbers against each other, and neither do
the tests: some of the made-up and changed items "the test on the table" have more rows of the
matrix than R13.13's last rule admits for their tables. One clause of the test on the setting cannot
refuse: the word on the coefficient that is left out is 1 in every string that is read alone.
Nothing on soundness, completeness or hiding.
-/
import OnBytes.Params.TestItems
import OnBytes.Entry.RecordToyFiles
import Fmt.Parsed

namespace OnBytes.Params.TestChainsTogether
open OnBytes.Entry.RecordToy (oneTimeParameters sharedParameters secondParameters keyFile entryFile)

/-- What parameter bytes hold: the plan, the digest of the public files, the further items. -/
abbrev Held : Type := Fmt.Plan × ByteArray × List (String × ByteArray)

/-- Parameter bytes read, changed by g and spelled again. No byte if they are not read. -/
def again (b : ByteArray) (g : Held → Held := id) : ByteArray :=
  match Given.read b with
  | some x =>
    let y := g (x.plan, x.cfg, x.items)
    Fmt.paramsBytes y.1 y.2.1 y.2.2
  | none => ByteArray.empty

/-- The plan changed. -/
def atPlan (f : Fmt.Plan → Fmt.Plan) : Held → Held := fun h => (f h.1, h.2)

/-- Another digest of the public files. -/
def otherDigest : Held → Held := fun h => (h.1, Fmt.pattern 32, h.2.2)

/-- The value of the item of a name changed. -/
def atItem (name : String) (f : ByteArray → ByteArray) : Held → Held := fun h =>
  (h.1, h.2.1, h.2.2.map fun x => if x.1 == name then (x.1, f x.2) else x)

/-- The entry RECORD for one answer a row and 803 entries of a row's message (R13.15), as at the
toy. The readers under test look at its name alone. -/
def recordE : Fmt.Entry := { name := Fmt.recordName, drawE := 11, drawNZ := 1 }

/-- The entry RECORD laid before the plan's entries. -/
def withRecord : Held → Held := atPlan fun p => { p with entries := recordE :: p.entries }

/-- The plan without its entry RECORD. -/
def withoutRecord : Held → Held :=
  atPlan fun p => { p with entries := p.entries.filter fun e => e.name != Fmt.recordName }

/-- An item "the test on the table" with one row more in the matrix. -/
def oneRowMore (l : ByteArray) : ByteArray :=
  match readLin l with
  | some x => spellLin { x with matrixRows := x.matrixRows + 1 }
  | none => ByteArray.empty

/-- Three strings of parameter bytes, in the file's order. -/
abbrev Three : Type := ByteArray × ByteArray × ByteArray

/-- The toy key's. -/
def toy : Three := (oneTimeParameters, sharedParameters, secondParameters)

/-- The first chain's string changed. -/
def inFirst (g : Held → Held) (x : Three) : Three := (again x.1 g, x.2)
/-- The shared chain's string changed. -/
def inShared (g : Held → Held) (x : Three) : Three := (x.1, again x.2.1 g, x.2.2)
/-- The second chain's string changed. -/
def inSecond (g : Held → Held) (x : Three) : Three := (x.1, x.2.1, again x.2.2 g)

/-- Each of a key's strings is read alone. -/
def keyAlone (x : Three) : Bool :=
  (OneTime.read x.1).isSome && (Shared.read x.2.1).isSome && (Second.read x.2.2).isSome

/-- A key's strings are read together. -/
def keyTogether (x : Three) : Bool := (KeyChains.read x.1 x.2.1 x.2.2).isSome

/-- The toy key's strings with one thing changed, and whether each string alone is still read. -/
def changedKey : List (String × Three × Bool) := [
  ("R13.5: other codes in the shared chain",
    inShared (atItem "codes" fun _ => spellCodes TestItems.codes) toy, true),
  ("R13.5: other codes in the one-time chain",
    inFirst (atItem "codes" fun _ => spellCodes TestItems.codes) toy, true),
  ("R13.5: a row more in the shared chain's test on the table",
    inShared (atItem "the test on the table" oneRowMore) toy, true),
  ("R13.15: the entry RECORD in the shared chain's plan", inShared withRecord toy, true),
  ("R13.15: the entry RECORD in the second chain's plan", inSecond withRecord toy, true),
  ("R4.9: another digest in the shared chain", inShared otherDigest toy, true),
  ("R4.9: another digest in the second chain", inSecond otherDigest toy, true),
  ("One setting: salts of 48 bytes in the shared chain",
    inShared (atPlan fun p => { p with salt := 48 }) toy, true),
  ("One setting: nonces of seven bytes in the second chain",
    inSecond (atPlan fun p => { p with nonce := 7 }) toy, true),
  ("One setting: listed positions of two bytes in the second chain",
    inSecond (atPlan fun p => { p with posB := 2 }) toy, true),
  ("One setting: two answers to a sample in the shared chain",
    inShared (atPlan fun p => { p with samples := 2 }) toy, true),
  ("One setting: the first field in the second chain",
    inSecond (atPlan fun p => { p with field := .one }) toy, true),
  ("R4.3: the word on the coefficient that is left out is 0 in the second chain",
    inSecond (atPlan fun p => { p with saved := 0 }) toy, false),
  ("R13.5: the shared and the second chain in each other's places",
    (toy.1, toy.2.2, toy.2.1), false),
  ("R13.5: the shared chain's string in the one-time chain's place",
    (toy.2.1, toy.2.1, toy.2.2), false) ]

/-! ## A proof's chains, made up -/

open TestItems (lin table req layout plan)

/-- An item "the test on the table" for tables with one stored answer a row and a matrix of the
given number of rows. -/
def linAt (rows : Nat) : LinShape :=
  { lin with matrixRows := rows, fold := { lin.fold with index := { table with answers := 1 } } }

/-- The two items that the first and the shared chain share. -/
def both (rows : Nat) : List (String × ByteArray) :=
  [("codes", spellCodes TestItems.codes), ("the test on the table", spellLin (linAt rows))]

/-- A proof's three strings. a, b: the matrix's rows as the first and the shared chain tell them. -/
def proofAt (a b : Nat) : Three :=
  (Fmt.paramsBytes plan Fmt.zero32 (both a ++
      [("request's shape", spellReq req), ("layout", spellLayout layout),
       ("links' identifiers", spellWords [1, 2]), ("pending rows", spellWord 3),
       ("binding tree", spellBinding ⟨6, 40⟩)]),
   Fmt.paramsBytes plan Fmt.zero32 (both b), Fmt.paramsBytes plan Fmt.zero32 [])

/-- Each of a proof's strings is read alone. -/
def proofAlone (x : Three) : Bool :=
  (First.read x.1).isSome && (Shared.read x.2.1).isSome && (Second.read x.2.2).isSome

/-- A proof's strings are read together. -/
def proofTogether (x : Three) : Bool := (ProofChains.read x.1 x.2.1 x.2.2).isSome

/-- Codes with one code more. -/
def moreCodes : Codes := ⟨#[⟨6, 4, 2⟩, ⟨7, 2, 2⟩, ⟨8, 2, 2⟩], #[⟨6, 16, 2⟩]⟩

/-- The made-up strings with one thing changed, and whether each string alone is still read. -/
def changedProof : List (String × Three × Bool) := [
  ("R14.9: 22 rows of the matrix in the first chain, 21 in the shared chain", proofAt 22 21, true),
  ("R14.9: other codes in the shared chain",
    inShared (atItem "codes" fun _ => spellCodes moreCodes) (proofAt 22 22), true),
  ("R14.3: the entry RECORD in the first chain's plan", inFirst withRecord (proofAt 22 22), false),
  ("R14.3: the entry RECORD in the shared chain's plan", inShared withRecord (proofAt 22 22), true),
  ("R14.3: the entry RECORD in the second chain's plan", inSecond withRecord (proofAt 22 22), true),
  ("R4.9: another digest in the first chain", inFirst otherDigest (proofAt 22 22), true),
  ("R4.9: another digest in the second chain", inSecond otherDigest (proofAt 22 22), true),
  ("One setting: salts of 48 bytes in the shared chain",
    inShared (atPlan fun p => { p with salt := 48 }) (proofAt 22 22), true),
  ("R14.10: an item in the second chain",
    inSecond (fun h => (h.1, h.2.1, both 22)) (proofAt 22 22), false) ]

/-- The names of the rows that are read together, or whose strings are read alone otherwise than the
row says. -/
def amiss (alone together : Three → Bool) (l : List (String × Three × Bool)) : List String :=
  (l.filter fun r => together r.2.1 || alone r.2.1 != r.2.2).map (·.1)

-- 1. the toy key's strings: read alone and together; spelled again they are the programs' bytes
#guard keyAlone toy && keyTogether toy
#guard again toy.1 == toy.1 && again toy.2.1 == toy.2.1 && again toy.2.2 == toy.2.2 &&
  toy.1.size != 0 && toy.2.1.size != 0 && toy.2.2.size != 0
#guard changedKey.length == 15 && (changedKey.filter (·.2.2)).length == 12 &&
  amiss keyAlone keyTogether changedKey == []

-- 2. a proof's strings
#guard proofAlone (proofAt 22 22) && proofTogether (proofAt 22 22)
#guard changedProof.length == 9 && (changedProof.filter (·.2.2)).length == 7 &&
  amiss proofAlone proofTogether changedProof == []

-- 3. the limit: without the entry RECORD in the one-time chain's plan the strings are other bytes,
-- and they are read together
#guard (inFirst withoutRecord toy).1 != toy.1 && keyTogether (inFirst withoutRecord toy)

-- 4. the heads of the toy's two files
#guard Fmt.headOf Fmt.tagKey .two == keyFile.extract 0 8 &&
  Fmt.headOf Fmt.tagEntry .two == entryFile.extract 0 8

end OnBytes.Params.TestChainsTogether
