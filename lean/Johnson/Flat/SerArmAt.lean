-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/SerArmAt.lean: the three serialisers that the total code behind the escape leaves as
letters, at the carrier of the typed oracles of the object with records `LrG (restSibFull …)` |
`LrG (restSibSmall …)` (Johnson/Flat/RestSib.lean).

`ArmBack.backL2` and `ArmBack.backAlong` (OnBytes/TypedOracleCompiler/Run/ArmBack.lean) make a total code of all
typed points over an interface L2 from serialisers. Three of them were given at no L2: of an
instance of L2; of a plain part of some round under the tag of Test; and the same under the tag of
the session. Here L2 is `typedOracleCarrier L (List Bool) aT aL` (Johnson/TypedOracleCompiler/RecCompile/Carrier.lean) at
L := `LrG (restSibFull A R F P hL)`, and the like at the small size.

 - `serByte`, `serBytes`, `serWord`, `serE3`, `serFront`, `serJoin`: a byte, a string of bytes
   (which is also the seam's plain part), a word, an element of the extension field as three words,
   and the plain parts of the front round and of the joining round of a whole file, for any type of
   answers; at the files below the answers are a list of such elements (`ansL`,
   OnBytes/Flat/FilesAt.lean);
 - `serRecFull`: a record: the seeds (`serSd1`, OnBytes/TypedOracleCompiler/Run/PageESer.lean) and the answers
   (`serOnCube`, OnBytes/TypedOracleCompiler/Run/SerArm.lean);
 - `sxFull sX`: an instance of L2, which is (an instance or none, a record, a record); sX: a
   serialiser of the object's own instances, which stay a letter;
 - `pTFull`, `pOFull`: the plain parts under the two tags, for every F (three files' protocols),
   from serialisers round by round (`SerA`);
 - `pTFilesFull`, `pOFilesFull`: the same at `threeProtocolsFromDryRunAtFullSize A R G` (OnBytes/Flat/FilesAt.lean), with
   Test's annotation the key file's: no serialiser is left as a letter (A, R, G, P, hL and Link's
   annotation aL stay parameters);
 - `backArmFull`: `ArmBack.backAlong` at these three;
 - the like at the small size.

Main definitions: `sxFull`, `pTFull`, `pOFull`, `pTFilesFull`, `pOFilesFull`, `backArmFull`;
`sxSmall`, `pTSmall`, `pOSmall`, `pTFilesSmall`, `pOFilesSmall`, `backArmSmall`.

Not claimed. What the strings are: for an encoding to be one to one, any total one-to-one code
serves behind the escape; the answer that an encoding reads out of an oracle at a query written
there hangs on this code, and of such answers nothing is said here (OnBytes/TypedOracleCompiler/Run/ArmBack.lean's
head). Johnson/Flat/ArmPlain.lean also compares these strings to tell one plain part; that needs one
to one alone. Nothing was evaluated. Nothing on soundness. For proofs only; no program imports this
file.


-/
import Johnson.Flat.RestSib
import Johnson.TypedOracleCompiler.RecCompile.Carrier
import OnBytes.Flat.FilesAt
import OnBytes.TypedOracleCompiler.Run.SerArm
import OnBytes.TypedOracleCompiler.Run.ArmBack

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat

open Hiop Cb Cb.Ood OnBytes.Slice OnBytes.Maker
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms TypedOracleCompiler.Run.SerArm
open TypedOracleCompiler.Run.PageESer (serSd1 serGE)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.RunA (RestR LrG)
open _root_.Run (ckP)

/-! ## The plain parts of the three silent rounds of a whole file -/

/-- A byte, as a number below 256. -/
def serByte : Ser UInt8 :=
  Ser.ofEquiv ⟨UInt8.toFin, UInt8.ofFin, fun _ => rfl, fun _ => rfl⟩ (Ser.fin UInt8.size)

/-- A string of bytes, as the list of its bytes. -/
def serBytes : Ser ByteArray :=
  Ser.ofEquiv (β := List UInt8)
    ⟨fun b => b.data.toList, fun l => ⟨l.toArray⟩, fun _ => rfl, fun _ => rfl⟩ (Ser.list serByte)

/-- A word of 64 bits, as a number below 2 ^ 64. -/
def serWord : Ser UInt64 :=
  Ser.ofEquiv ⟨UInt64.toFin, UInt64.ofFin, fun _ => rfl, fun _ => rfl⟩ (Ser.fin UInt64.size)

/-- An element of the extension field as the program holds it: three words. Every triple of words
has its own string, also two triples that stand for one element of the field. -/
def serE3 : Ser OnBytes.E :=
  Ser.ofEquiv (β := UInt64 × UInt64 × UInt64)
    ⟨OnBytes.E.triple, OnBytes.E.ofTriple, fun _ => rfl, fun _ => rfl⟩
    (Ser.prod serWord (Ser.prod serWord serWord))

/-- The front round's plain part: the answers, and the number of the stored copy. -/
def serFront {α : Type} (S : Ser α) : Ser (FrontMsg α) :=
  Ser.ofEquiv (β := α × ℕ) ⟨fun f => (f.answers, f.copy), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
    fun _ => rfl⟩ (Ser.prod S Ser.nat)

/-- The joining round's plain part: the answers, and the run's value of the second chain. -/
def serJoin {α β : Type} (S : Ser α) (T : Ser β) : Ser (_root_.Compile.Joined.JoinMsg α β) :=
  Ser.ofEquiv (β := α × β) ⟨fun j => (j.answers, j.run), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
    fun _ => rfl⟩ (Ser.prod S T)

/-! ## The full size -/

/-- A record at the full size: the seeds and the answers. -/
def serRecFull : Ser ((Fin 1 → (Fin 29 → GE) × NZ) × ((Fin frS.P.v → Bool) × Fin 1 → GE)) :=
  Ser.prod (serSd1 29 1) (serOnCube serGE frS.P.v 1)

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (hL : Honest linkSibFull ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))

/-- **An instance of the carrier**: an instance of the object or none, and two records. -/
def sxFull (sX : Ser X) : Ser (LrG (restSibFull A R F P hL)).XC :=
  Ser.prod (Ser.option sX) (Ser.prod serRecFull serRecFull)

variable (aT : RoundSplits (LrG (restSibFull A R F P hL)).offline.shape)
  (aL : RoundSplits (LrG (restSibFull A R F P hL)).link.shape)

/-- **A plain part of some round under the tag of Test.** -/
def pTFull (D : SerA (LrG (restSibFull A R F P hL)).offline.shape aT) :
    Ser (PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT aL) .test)
      (annOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT aL) .test)) :=
  serPB _ _ D

/-- **A plain part of some round under the tag of the session.** -/
def pOFull (D : SerA F.proof.shape F.ann) :
    Ser (PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT aL) .onl)
      (annOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT aL) .onl)) :=
  serPB _ _ D

end

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (G : FilesParameters X RecFull) (P : (threeProtocolsFromDryRunAtFullSize A R G).Provers)
  (hL : Honest linkSibFull ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))
  (aL : RoundSplits (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)).link.shape)

/-- Under the tag of Test, at the full-size files, with the key file's annotation. -/
def pTFilesFull :
    Ser (PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
               (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .test)
      (annOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
        (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .test)) :=
  serWhole (ckP .two)
    (WholeD.of frS.P.T.a (dataAt frS.P.T.a
      (dryKey G.k ((OnBytes.Slice.keyOf (fun β : NZ => β.val) : RecFull → TableKey) G.rec₀))))
    (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty (serFront (Ser.list serE3))
    (serJoin (Ser.list serE3) serBytes) serBytes

/-- Under the tag of the session, at the full-size files. -/
def pOFilesFull :
    Ser (PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
               (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .onl)
      (annOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
        (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .onl)) :=
  serWhole (ckP .two)
    (WholeD.of frS.P.T.a (dataAt frS.P.T.a
      (dryProof G.c ((OnBytes.Slice.keyOf (fun β : NZ => β.val) : RecFull → TableKey) G.z₀.2)
        (G.block G.z₀.1))))
    (front₀ G.z₀.2) (join₀ G.z₀.2) ByteArray.empty (serFront (Ser.list serE3))
    (serJoin (Ser.list serE3) serBytes) serBytes

/-- **The total code behind the escape at the full-size files**: `ArmBack.backAlong` at the three
serialisers above. What stays a letter beside the section's A, R, G, P, hL and aL: sX, of the
object's own instances; the number K of digests; and what `backAlong` takes for the bodies and for
Link's plain parts (D, early, e, pbF, bd, B, sg, sb). This `early` is the entry's interface's, on a
type Y of its own: it is not `G.early`. -/
def backArmFull {Y Bd : Type} (D : TypedOracleCompiler.Run.PQ.XD) (early : Y → Y) (e : _root_.Fmt.Entry)
    (pbF : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
                 (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .link)
        (annOf (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL)) (List Bool)
          (threeProtocolsFromDryRunAtFullSize A R G).annT aL) .link) ≃
      PlainPart (shapeOf (TypedOracleCompiler.Run.PageEBack.LE (Bd := Bd) D early e) .link)
        (annOf (TypedOracleCompiler.Run.PageEBack.LE (Bd := Bd) D early e) .link))
    (bd : List Bool ≃ Bd) (sX : Ser X) (B : TypedOracleCompiler.Run.PQ.BodyD Bd)
    (sg : Ser _root_.Run.PQ.SgX) (sb : Ser Bd) (K : ℕ) :
    Rom.StrCode (AllPts 256 K (typedOracleCarrier (LrG (restSibFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL))
      (List Bool) (threeProtocolsFromDryRunAtFullSize A R G).annT aL)) :=
  TypedOracleCompiler.Run.ArmBack.backAlong _ D early e pbF bd
    (sxFull A R (threeProtocolsFromDryRunAtFullSize A R G) P hL sX) B sg sb
    (pTFilesFull A R G P hL aL) (pOFilesFull A R G P hL aL) K

end

/-! ## The small size -/

/-- A record at the small size. -/
def serRecSmall : Ser ((Fin 1 → (Fin 19 → GE) × NZ) × ((Fin srS.P.v → Bool) × Fin 1 → GE)) :=
  Ser.prod (serSd1 19 1) (serOnCube serGE srS.P.v 1)

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (R : (srS.toDecR srZ 524285).RelationsAndEncoding A)
  (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (hL : Honest linkSibSmall ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))

/-- An instance of the carrier. -/
def sxSmall (sX : Ser X) : Ser (LrG (restSibSmall A R F P hL)).XC :=
  Ser.prod (Ser.option sX) (Ser.prod serRecSmall serRecSmall)

variable (aT : RoundSplits (LrG (restSibSmall A R F P hL)).offline.shape)
  (aL : RoundSplits (LrG (restSibSmall A R F P hL)).link.shape)

/-- A plain part of some round under the tag of Test. -/
def pTSmall (D : SerA (LrG (restSibSmall A R F P hL)).offline.shape aT) :
    Ser (PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT aL) .test)
      (annOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT aL) .test)) :=
  serPB _ _ D

/-- A plain part of some round under the tag of the session. -/
def pOSmall (D : SerA F.proof.shape F.ann) :
    Ser (PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT aL) .onl)
      (annOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT aL) .onl)) :=
  serPB _ _ D

end

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (R : (srS.toDecR srZ 524285).RelationsAndEncoding A)
  (G : FilesParameters X RecSmall) (P : (threeProtocolsFromDryRunAtSmallSize A R G).Provers)
  (hL : Honest linkSibSmall ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))
  (aL : RoundSplits (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)).link.shape)

/-- Under the tag of Test, at the small files, with the key file's annotation. -/
def pTFilesSmall :
    Ser (PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
               (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .test)
      (annOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
        (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .test)) :=
  serWhole (ckP .two)
    (WholeD.of srS.P.T.a (dataAt srS.P.T.a
      (dryKey G.k ((OnBytes.Slice.keyOf (fun β : NZ => β.val) : RecSmall → TableKey) G.rec₀))))
    (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty (serFront (Ser.list serE3))
    (serJoin (Ser.list serE3) serBytes) serBytes

/-- Under the tag of the session, at the small files. -/
def pOFilesSmall :
    Ser (PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
               (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .onl)
      (annOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
        (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .onl)) :=
  serWhole (ckP .two)
    (WholeD.of srS.P.T.a (dataAt srS.P.T.a
      (dryProof G.c ((OnBytes.Slice.keyOf (fun β : NZ => β.val) : RecSmall → TableKey) G.z₀.2)
        (G.block G.z₀.1))))
    (front₀ G.z₀.2) (join₀ G.z₀.2) ByteArray.empty (serFront (Ser.list serE3))
    (serJoin (Ser.list serE3) serBytes) serBytes

/-- **The total code behind the escape at the small files**: `ArmBack.backAlong` at the three
serialisers above. What stays a letter beside the section's A, R, G, P, hL and aL: sX, of the
object's own instances; the number K of digests; and what `backAlong` takes for the bodies and for
Link's plain parts (D, early, e, pbF, bd, B, sg, sb). This `early` is the entry's interface's, on a
type Y of its own: it is not `G.early`. -/
def backArmSmall {Y Bd : Type} (D : TypedOracleCompiler.Run.PQ.XD) (early : Y → Y) (e : _root_.Fmt.Entry)
    (pbF : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
                 (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .link)
        (annOf (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL)) (List Bool)
          (threeProtocolsFromDryRunAtSmallSize A R G).annT aL) .link) ≃
      PlainPart (shapeOf (TypedOracleCompiler.Run.PageEBack.LE (Bd := Bd) D early e) .link)
        (annOf (TypedOracleCompiler.Run.PageEBack.LE (Bd := Bd) D early e) .link))
    (bd : List Bool ≃ Bd) (sX : Ser X) (B : TypedOracleCompiler.Run.PQ.BodyD Bd)
    (sg : Ser _root_.Run.PQ.SgX) (sb : Ser Bd) (K : ℕ) :
    Rom.StrCode (AllPts 256 K (typedOracleCarrier (LrG (restSibSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL))
      (List Bool) (threeProtocolsFromDryRunAtSmallSize A R G).annT aL)) :=
  TypedOracleCompiler.Run.ArmBack.backAlong _ D early e pbF bd
    (sxSmall A R (threeProtocolsFromDryRunAtSmallSize A R G) P hL sX) B sg sb
    (pTFilesSmall A R G P hL aL) (pOFilesSmall A R G P hL aL) K

end

end OnBytes.Flat
