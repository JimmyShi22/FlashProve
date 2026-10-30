-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageEBack.lean: the total code behind the escape, as a term, at the interface of an
entry with instances: serialisers of the plain parts at each of the three tags, of the instance, of
the bodies;
so `backE := backP` with the serialiser of bodies that writes stored symbols as every other page
does (`serTie`).

Why. A page writes whatever the format does not write behind an escape byte, by a total code. The
sibling's `backP` (OnBytes/TypedOracleCompiler/Run/SerThin.lean) wants serialisers as data (`SerP`): of an instance,
of a body, and of a plain part of some round for each of the interface's three protocols. For the
entry's interface `LXE D early (TSE D e)` (OnBytes/TypedOracleCompiler/Slice/EntryX.lean, EntryXJudge.lean) there
was no such term. Two parts read one raw string off a log only if their pages write a leaf query on
a stored symbol as one string, behind the escape too: that asks `back = backP` at `serTie` at one
serialiser of stored symbols (OnBytes/TypedOracleCompiler/Run/SerTie.lean: `backP_stored_two`).

 - `pbE`: a plain part of some round: under the tag of Link: the silent front's two points, then the
 description's written rounds (the sibling's `serPBL`); under the tag of Test: the same at the one
 seeds' round; under the tag of the batch: no round;
 - `serE` : SerP, from a serialiser sx of instances, the bodies' data B, a serialiser sg of stored
 symbols and any serialiser sb of bodies; `backE` : StrCode (AllPts 256 (D.K + 1) (LXE …));
   `bdE_is`: its serialiser of bodies is `serTie B sg sb`, by unfolding;
 - `serT3`, `serAns2`, `serX2`: serialisers of a triple of words; of two lists of answers; of an
 instance (two lists of answers) × Sd, from one of Sd;
 - `serFinite`: a serialiser of any finite type (it computes nothing: it takes an enumeration by
 choice): for seeds;
 - `backE2`: `backE` at bodies := strings of bits and instances (List T3 × List T3) × Sd.

Main definitions: `pbE`, `serE`, `backE`, `serX2`, `serFinite`, `backE2`.
Main theorem: `bdE_is`.

What is not said. B, sg and the serialiser of Sd are parameters. What the strings behind the escape
are is of no weight: any total code serves. `serFinite` cannot be evaluated. Nothing on soundness.
The sibling is a second version of the library's soundness road, under OnBytes/TypedOracleCompiler/.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryXJudge
import OnBytes.TypedOracleCompiler.Run.PageXFit
import OnBytes.TypedOracleCompiler.Run.SerTie
import OnBytes.TypedOracleCompiler.Run.FirstAnswers

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PageEBack
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.FirstAnswers
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run.PQ

variable {X Bd : Type} (D : PQ.XD) (early : X → X) (e : _root_.Fmt.Entry)

/-- The entry's interface, at the seeds' protocol. -/
abbrev LE : BatchProtocolWithLeafBody Unit X := LXE (Bd := Bd) D early (TSE D e)

/-- A plain part of some round, for the three protocols of the interface. -/
def pbE : ∀ t : Tag, Ser (PlainPart (shapeOf (LE (Bd := Bd) D early e) t)
    (annOf (LE (Bd := Bd) D early e) t))
  | .link => Ser.sum (Ser.sum Ser.unit Ser.unit) (serPBL D.C D.ds)
  | .test => Ser.sum (Ser.sum Ser.unit Ser.unit) (serPBL D.C [dSeed e])
  | .onl => Ser.empty

variable (sx : Ser X) (B : PQ.BodyD Bd) (sg : Ser SgX) (sb : Ser Bd)

/-- The serialisers: of instances; of bodies, with stored symbols written as every page writes them;
of plain parts. -/
def serE : SerP (fun _ : Unit => LE (Bd := Bd) D early e) :=
  ⟨sx, serTie B sg sb, pbE D early e⟩

/-- The total code behind the escape, at the entry's interface. -/
def backE : StrCode (AllPts 256 (D.K + 1) (LE (Bd := Bd) D early e)) :=
  backP (fun _ : Unit => LE (Bd := Bd) D early e) (serE D early e sx B sg sb) (D.K + 1)

/-- Its serialiser of bodies is `serTie` at B, sg and sb. -/
theorem bdE_is : (serE D early e sx B sg sb).bd = serTie B sg sb := rfl

/-! ## Instances -/

/-- A serialiser of a triple of words. -/
def serT3 : Ser T3 := Ser.prod serW (Ser.prod serW serW)

/-- Of two lists of answers. -/
def serAns2 : Ser (List T3 × List T3) := Ser.prod (Ser.list serT3) (Ser.list serT3)

/-- Of an instance: two lists of answers, and what stands in the seeds' place. -/
def serX2 {Sd : Type} (ss : Ser Sd) : Ser ((List T3 × List T3) × Sd) := Ser.prod serAns2 ss

/-- A serialiser of any finite type, by an enumeration taken by choice. -/
noncomputable def serFinite (α : Type) [Fintype α] : Ser α :=
  Ser.ofEquiv (Fintype.equivFin α) (Ser.fin (Fintype.card α))

/-- The total code at bodies := strings of bits and instances (List T3 × List T3) × Sd. -/
def backE2 {Sd : Type} (D : PQ.XD) (early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd)
    (e : _root_.Fmt.Entry) (ss : Ser Sd) (B : PQ.BodyD (List Bool)) (sg : Ser SgX) :
    StrCode (AllPts 256 (D.K + 1) (LXE (Bd := List Bool) D early (TSE D e))) :=
  backE D early e (serX2 ss) B sg serBits

/-! ## Two annotations -/

/-- The plain parts of written local rounds under the two names of "all local": one type. -/
theorem pbl_is (C : CK) : ∀ ds : List PQ.RD,
    PBL C ds = PlainPart (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds))
  | [] => rfl
  | _ :: ds => congrArg (fun T => _ ⊕ T) (pbl_is C ds)

end TypedOracleCompiler.Run.PageEBack
