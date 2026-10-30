-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageRun.lean: the typed oracle functions that a page-made encoding reads out of one
hash function, at every oracle but the spare one, written as a program. Definitions alone; the laws
are in OnBytes/TypedOracleCompiler/Run/PageRunLaws.lean.

Why. An encoding made of a page (`implG`, OnBytes/TypedOracleCompiler/Run/PageG.lean; `implOf`,
OnBytes/TypedOracleCompiler/Run/PageOf.lean) holds a parser, and `implOf`'s parser is taken by choice: so Lean makes
no code for that encoding, nor for an algorithm run through it (`OComp.overOne`, Rom/Family.lean).
But a run reads of an encoding how a typed point is WRITTEN, into how many blocks an answer is cut
and how the blocks make the answer (`code`, `blocks`, `rng`: `OComp.overOne`'s text; the last two
are the same at every page: OnBytes/TypedOracleCompiler/Run/CodingImpl.lean), and never the parser. At every oracle
other than the spare one that string is made of two functions alone: `put`, which writes some typed
points, and `bk`, which writes every point. Here these strings are a plain function of `put` and
`bk`.

  `strR Lf put bk a`    the string of a real point a: what `put` writes there; where it writes
                        nothing, the byte 2 and then what `bk` writes.
  `strG Lf bk a`        the string of a ghost point: the byte 2 and then what `bk` writes.
  `codeRun Lf put bk`   the string of block j of the answer of the oracle o at the query q.
  `famRun Lf put bk g`  the typed oracle functions: block j of an answer is g's answer at that
                        string.

AT THE SPARE ORACLE `OracleName.other` `codeRun` RETURNS THE QUERY ITSELF. THAT IS NOT THE ENCODING's STRING
in general: the encoding moves a spare string aside where room had to be made for a point's string,
and to know where it asks the parser. So `famRun` is the family that the encoding reads out at every
oracle BUT that one. The compiled verifiers never ask it (OnBytes/TypedOracleCompiler/Compile/Batch/NoOther.lean);
the laws ask that of the algorithm as a premise. It is shown of algorithms of this library, among
them the arms with the lax and with the strict Link, Test and session
(Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublicArm.lean, KeyAnsPublic.lean, ProofAnsPublic.lean) and the run
of the one judge for three files (OnBytes/TypedOracleCompiler/Slice/JudgeNoOther.lean); one law is applied to the
verifier `VRAV` (`det_congr_asksIn` at `tmAtVRAV`, Johnson/Top/Fire/Code/TmProof.lean).

THE INTERFACE STANDS BEHIND A FUNCTION OF Unit (`Lf`), as in OnBytes/TypedOracleCompiler/Run/ThinDefs.lean, whose
head says why: compiled Lean builds whatever is handed over as a value, and an interface holds its
protocols' rounds, each with the list of all its verifier messages. `Lf` is handed on and never
called. The laws are stated at `fun _ => L`. That helps only where L has code at all: Lean compiles
the body of `fun _ => L` even if nobody calls it.

What a caller must bring as code: `put`, and `bk` too, even for a run that never meets a point at
which `put` writes nothing; the hash function g; and the body of `Lf` (see above).

This module imports the file of the encodings' types (OnBytes/TypedOracleCompiler/Run/CodingImpl.lean) and the bits
of a byte, and no file on pages, on arms or on their laws.

This file holds no statement.

ON COST: THIS FORM IS FOR THE EQUATIONS, NOT FOR A LONG RUN. Strings are lists of bits. The K + 1
blocks of a chain query's answer are handed over as a function of the block's number, so a block
that nobody reads is not hashed. But a digest is itself a function of its 256 places, and g is a
function into such functions: a hash that is handed on so can be run anew at every bit that is read
(the head of Run/CodingFnThin.lean says how that comes about). The form for a run, which hashes
bytes and keeps each answer as data, is OnBytes/TypedOracleCompiler/Run/PageRunFast.lean; its equation to this one
is `famRunFast_eq`, OnBytes/TypedOracleCompiler/Run/PageRunFastLaws.lean.

-/
import OnBytes.TypedOracleCompiler.Run.CodingImpl
import Run.CodingBits

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PageRun
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bitsOfByte)

variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) {K : ℕ}
  (put : RealPts 256 K (Lf ()) → Option (List Bool)) (bk : AllPts 256 K (Lf ()) → List Bool)

/-- The string of a real point. -/
def strR (a : RealPts 256 K (Lf ())) : List Bool :=
  match put a with
  | some s => s
  | none => bitsOfByte 2 ++ bk (.inl a)

/-- The string of a ghost point. -/
def strG (a : GhostPts 256 K (Lf ())) : List Bool := bitsOfByte 2 ++ bk (.inr a)

/-- The string of block j of the answer of the oracle o at the query q. At the spare oracle: the
query itself, which is not the encoding's string in general. -/
def codeRun : (o : OracleName) → domOf 256 (Lf ()) o → Fin (blk K o) → List Bool
  | .leaf, q, _ => strR Lf put bk (.inl q)
  | .node, q, _ => strR Lf put bk (.inr (.inl q))
  | .rleaf, q, _ => strR Lf put bk (.inr (.inr (.inl q)))
  | .rnode, q, _ => strR Lf put bk (.inr (.inr (.inr (.inl q))))
  | .fb t, q, j => strR Lf put bk (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩)))))
  | .g t, q, _ => strR Lf put bk (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩)))))
  | .ann, _, j => j.elim0
  | .other, s, _ => s
  | .fbw t k, q, j => strG Lf bk ⟨t, k, q, j⟩

/-- **The typed oracle functions out of one hash function g.** -/
def famRun (g : Fam (rom 256)) : Fam (typedOracleFamily 256 K (Lf ())) :=
  fun o q => (rngEquiv 256 K o).symm fun j => g () (codeRun Lf put bk o q j)

end TypedOracleCompiler.Run.PageRun
