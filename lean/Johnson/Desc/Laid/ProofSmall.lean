-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Laid/ProofSmall.lean: THE VALUE for the proof file's place in the verifier's own text,
at the small size: of the three public files alone, and of the second hash function as a letter.
Definitions only: no theorem stands here, and no file with a law on these definitions is imported.

  instOf z            the verifier's instance (a request and the entry's record) as the
                      description's plain record: the request file's bytes, the table's key written
                      of the record, the reply file's bytes
  runPOf F            the proof file's decision at a description F: F's own run at `instOf z`
  laidOfDesc o pol lay KL F
                      what is laid, of a description: its own data and its decision; or a refusal
                      with words: where its tests on the plan say no; where its own road to the data
                      refuses (the makers' tests on the written rounds); where a test of `lawsAsk`
                      says no
  laidPOf o pol lay KL
                      **what is laid**: `laidOfDesc` at the description that `ProofFile.onlineDescription` makes of
                      the three files; where none is made: a refusal with words
  laidOk | laidData | laidRun
                      the same as three total letters: is it laid; the data, and the data of three
                      empty lists where it is not; the decision, and the decision that says no to
                      all where it is not

THE ORDER OF THE THREE FILES HERE IS pol lay KL (the parameter file, the layout file, the scale
file); the planner's own functions take pol KL lay.
The data are the description's own (`FileDescription.data`, Johnson/Desc/BlockSlot.lean): made of the
rounds that its blocks declare, at its own depth of the table. Whether that depth is the frame's,
and whether a list is empty, is asked by whoever lays the value. The laws:
Johnson/Desc/Laid/ProofSmallLaw.lean.

-/
import Johnson.Top.Fire.Code.Vals.FastSmall
import Johnson.Desc.BlockSlot
import Johnson.Desc.Laid.AsksFirst
import Johnson.Desc.Laid.ProofAsks
import Johnson.Desc.ProofFile.OnlineDescription

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD.Small
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Maker OnBytes
open VerifiableInference.Desc (FileDescription)

/-- The verifier's instance as the description's plain record (`instPartsOf`: three
functions). -/
def instOf (z : XS × RecSmall) : ProofFile.Inst :=
  ⟨⟨(instPartsOf z).1, (instPartsOf z).2.1⟩, (instPartsOf z).2.2⟩

/-- The proof file's decision at a description. -/
def runPOf (F : FileDescription ProofFile.Inst) : RunPS := (F.pull instOf).run

/-- **What is laid, of a description**: its rounds' data and its decision, or a refusal. -/
def laidOfDesc (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst) :
    Except String (WholeD × RunPS) :=
  match F.planWord with
  | some w => .error ("the proof file's description: " ++ w)
  | none =>
    match F.data "proof file" with
    | .error e => .error ("the proof file's description: its data: " ++ e)
    | .ok D =>
      match _root_.LPFD.firstNo (_root_.LPFD.lawsAsk o pol lay KL F D) with
      | some t => .error ("the proof file's description: " ++ t.1)
      | none => .ok (D, runPOf F)

/-- **What is laid for the proof file**, of the three public files. -/
def laidPOf (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) : Except String (WholeD × RunPS) :=
  match ProofFile.onlineDescription o pol lay KL with
  | .error e => .error ("the proof file's description is not made: " ++ e)
  | .ok F => laidOfDesc o pol lay KL F

/-- Is it laid. -/
def laidOk (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) : Bool := (laidPOf o pol lay KL).isOk

/-- The laid data; where nothing is laid: the data of three empty lists. -/
def laidData (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) : WholeD :=
  match laidPOf o pol lay KL with
  | .ok x => x.1
  | .error _ => emptyD

/-- The laid decision; where nothing is laid: no, at every instance and all views. -/
def laidRun (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) : RunPS :=
  match laidPOf o pol lay KL with
  | .ok x => x.2
  | .error _ => fun _ _ _ _ => false

end LPFD.Small
