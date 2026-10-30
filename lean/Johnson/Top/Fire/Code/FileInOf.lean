-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/FileInOf.lean: WHAT THE FAST FORM IS HANDED FOR A WHOLE FILE (the key file;
the proof file), AS ONE DEFINITION WITH CODE,
OUT OF THE PARSED FILE's BYTES: in the manner of `StrictIn.madeOf` for the entry file: an Except
whose error says who refused,
and a list of named tests that are to be JUDGED, not only printed.
  `MadeFile`     k: the carrier as `Carrier.read` returns it · cfg · pF · pJ · p3: the four further
  arguments of `File.toBPrfAt` ·
                 cm: the table's root as a digest · copy · answers · front: the named tests.
  `madeFileOf magic what cfgPub bytes`   the maker. `madeKeyOf` | `madeProofOf`: at the two magic
  words.
  `MadeFile.ok`  every test in front says yes.
  `MadeFile.inD` | `inDS`   the record `FileIn` of the fast form at the full | the small size (two
  records of one text).
  `keyInS` | `proofInS` | `keyInD` | `proofInD` c bytes   the run sheet's shapes: Except String
  FileIn | (FileIn × ℕ): they refuse where the reader
                 refuses AND where a test in front says no.
  `turned`       the same at a changed carrier (a control): the changes `Controls.turnRequest`,
  `turnColumn` and their kin take a
                 carrier to a carrier: the plain parts are made anew of the changed carrier, as they
                 would be of a changed file.
THE MAKE IS THE ASKING TEXTS' OWN: the key's: Johnson/RunOne/AskKey.lean, keyTyped: pF := frontOf
(tableOf k).answers k.copy ·
pJ := ⟨(tableOf k).answers, k.run2⟩ · p3 := k.run3; the proof's: Johnson/RunOne/AskProof.lean,
verifyProofSmall_is: frontC k ·
⟨answersC k, k.run2⟩ · k.run3: ONE TEXT (tableOf's answers are answersC's).
OF THE THREE THINGS CALLED cfg: THE ONE HERE (toBPrfAt's argument) IS PUBLIC: IT IS AN ARGUMENT
cfgPub, TO BE LAID FROM THE READING OF THE
PUBLIC FILES (the key's: the plan's key.oneTime.given.cfg; the proof's: the plan's cfg), NEVER OUT
OF THE PARSED FILE.
LENGTHS: `bytesToDig` and the run values are read at 32 bytes: a read beyond a ByteArray's end is
SILENT in compiled Lean (it gives 0): so the
five lengths are a named test here («file 1»), though `Carrier.read` reads each by rdDig already.
Size: nothing here hangs on a size: the sizes enter with DK | DP, sT | sB, which are the plan's.
Limits. No theorem. The parsed file is the prover's: nothing here holds it against the user's claim.
The record rcd is not made here (its seeds
are drawn over the hash from the root and the public digest). Nothing on soundness.
-/
import Johnson.Top.Fire.Code.VerifyVFastD
import Johnson.Top.Fire.Code.VerifyVFastDS
import Johnson.RunOne.Controls
import OnBytes.Maker.SilentParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LKF.FileInOf
open OnBytes OnBytes.Maker
open _root_.Iop (Dig)
open _root_.Run (bytesToDig)

/-- What a run of a whole file's arm is handed. -/
structure MadeFile where
  k : Carrier.File
  /-- PUBLIC: laid by the caller from the reading of the public files -/
  cfg : ByteArray
  pF : FrontMsg (List OnBytes.E)
  pJ : _root_.Compile.Joined.JoinMsg (List OnBytes.E) ByteArray
  p3 : ByteArray
  /-- the root of the table that the file names, as a digest -/
  cm : Dig 256
  copy : ℕ
  answers : List OnBytes.E
  front : List (String × Bool)

/-- Every test in front says yes. -/
def MadeFile.ok (m : MadeFile) : Bool := m.front.all (·.2)

/-- **Of a carrier.** what: the file's name in the tests' lines. -/
def ofCarrier (what : String) (cfgPub : ByteArray) (k : Carrier.File) : MadeFile :=
  let answers := k.answers.map OnBytes.E.ofTriple
  { k := k, cfg := cfgPub, pF := frontOf answers k.copy, pJ := ⟨answers, k.run2⟩, p3 := k.run3
    cm := bytesToDig k.root, copy := k.copy, answers := answers
    front :=
      [(what ++ " 1: the table's root, the binding root and the three run values have 32 bytes each",
          decide (k.root.size = 32) && decide (k.bindRoot.size = 32) && decide (k.run1.size = 32) &&
            decide (k.run2.size = 32) && decide (k.run3.size = 32)),
        (what ++ " 2: none of the three run values is 32 zero bytes",
          Fmt.runOk k.run1 && Fmt.runOk k.run2 && Fmt.runOk k.run3),
        (what ++ " 3: none of the three chains is without a round",
          !k.rounds1.isEmpty && !k.rounds2.isEmpty && !k.rounds3.isEmpty)] }

/-- **From the parsed file's bytes.** -/
def madeFileOf (magic what : String) (cfgPub bytes : ByteArray) : Except String MadeFile :=
  match Carrier.read magic bytes with
  | .error e => .error (what ++ ": the reader refuses the parsed file: " ++ e)
  | .ok k => .ok (ofCarrier what cfgPub k)

/-- The key file's. -/
def madeKeyOf (cfgPub bytes : ByteArray) : Except String MadeFile :=
  madeFileOf Carrier.magicKey "key file" cfgPub bytes

/-- The proof file's. -/
def madeProofOf (cfgPub bytes : ByteArray) : Except String MadeFile :=
  madeFileOf Carrier.magicProof "proof file" cfgPub bytes

/-- The fast form's record at the full size. -/
def MadeFile.inD (m : MadeFile) : VerifiableInference.OnPublicFiles.SlotsBehindCutD.FileIn :=
  ⟨m.k, m.cfg, m.pF, m.pJ, m.p3⟩

/-- The fast form's record at the small size. -/
def MadeFile.inDS (m : MadeFile) : VerifiableInference.OnPublicFiles.SlotsBehindCutDS.FileIn :=
  ⟨m.k, m.cfg, m.pF, m.pJ, m.p3⟩

/-- The first test in front that says no. -/
def MadeFile.firstNo (m : MadeFile) : Option String := (m.front.find? fun x => !x.2).map (·.1)

/-- Refuses where the reader refuses, and where a test in front says no: the error names it. -/
def judged (r : Except String MadeFile) : Except String MadeFile :=
  match r with
  | .error e => .error e
  | .ok m =>
    match m.firstNo with
    | some t => .error ("a test in front says NO: " ++ t)
    | none => .ok m

/-- THE SHEET's SHAPES, the small size: c: the PUBLIC cfg. -/
def keyInS (c bytes : ByteArray) : Except String VerifiableInference.OnPublicFiles.SlotsBehindCutDS.FileIn :=
  (judged (madeKeyOf c bytes)).map MadeFile.inDS

/-- The ℕ: the carrier's number of the stored copy. -/
def proofInS (c bytes : ByteArray) :
    Except String (VerifiableInference.OnPublicFiles.SlotsBehindCutDS.FileIn × ℕ) :=
  (judged (madeProofOf c bytes)).map fun m => (m.inDS, m.copy)

/-- The same at the full size. -/
def keyInD (c bytes : ByteArray) : Except String VerifiableInference.OnPublicFiles.SlotsBehindCutD.FileIn :=
  (judged (madeKeyOf c bytes)).map MadeFile.inD

def proofInD (c bytes : ByteArray) :
    Except String (VerifiableInference.OnPublicFiles.SlotsBehindCutD.FileIn × ℕ) :=
  (judged (madeProofOf c bytes)).map fun m => (m.inD, m.copy)

/-- **A control**: the same at the carrier that a change makes; none where the change finds no
place. -/
def MadeFile.turned (what : String) (f : Carrier.File → Option Carrier.File) (m : MadeFile) :
    Option MadeFile :=
  (f m.k).map (ofCarrier what m.cfg)

/-- The two changed files an arm that were asked for, by name. -/
def controls : List (String × (Carrier.File → Option Carrier.File)) :=
  [("the slot's salt with one bit turned (Controls.turnRequest)", Johnson.RunOne.Controls.turnRequest),
    ("a word of an opened column turned (Controls.turnColumn)", Johnson.RunOne.Controls.turnColumn)]

end LKF.FileInOf
