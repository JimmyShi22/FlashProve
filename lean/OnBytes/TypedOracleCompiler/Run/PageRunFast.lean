-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageRunFast.lean: the program of OnBytes/TypedOracleCompiler/Run/PageRun.lean in a form for a run:
the hash is a function O from bytes to bytes, and every answer is made as data first. Definitions
alone; the law is in OnBytes/TypedOracleCompiler/Run/PageRunFastLaws.lean.

Why. `famRun Lf put bk g` takes g : `Fam (rom 256)`, whose answers are functions of a digest's 256
places, and a hash that is handed on so can be run anew at every bit that is read. The head of
Run/CodingFnThin.lean says how that comes about and what helps: the answer first as data, whose type
is no function's; computed in a function in which the oracle's name is a variable, so that the
compiler cannot see that the result is a function; and only then decoded. This file follows it.

  `gOf O`                  O as one hash function on bit strings: the string is laid into bytes
                           (`Run.toBytes`, Run/OracleBits.lean), hashed by O, and read as 256 bits.
                           `gOf Fmt.oracle` is `Run.oBits` by definition.
  `thunksOf n f`, `getT`   n delayed byte strings; the bytes behind the i-th.
  `famRunB Lf put bk O`    the answer to a typed query as data. One block: its bytes, computed at
                           once. K + 1 blocks: one delayed value a block, so within one answer a
                           block is hashed when it is first read, and once (so it is meant; no
                           theorem says it). All K + 1 delayed values are laid at every such
                           query, read or not. A query that is asked twice is answered twice.
  `decRun K o`             the data as a typed answer (`Run.digS`, Run/CodingFnThin.lean).
  `famRunFast Lf put bk O` the typed oracle functions.

The strings are `codeRun`'s: still lists of bits, which are laid back into bytes: one pass over each
string. At the spare oracle `OracleName.other` the string is the query itself, as in `codeRun`: not the
encoding's in general.

This file holds no statement. What a compiler computes how often is a fact about that compiler and
no theorem; no time is written down here.

-/
import OnBytes.TypedOracleCompiler.Run.PageRun
import Run.OracleBits
import Run.CodingFnThin

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PageRun
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig toBytes digS)

/-- A function from bytes to bytes as one hash function on bit strings. -/
def gOf (O : ByteArray → ByteArray) : Fam (rom 256) := fun _ s => bytesToDig (O (toBytes s))

/-- n byte strings, each delayed. -/
def thunksOf (n : ℕ) (f : Fin n → ByteArray) : Array (Thunk ByteArray) :=
  Array.ofFn fun j : Fin n => Thunk.mk fun _ => f j

/-- The bytes behind the i-th delayed value; no byte where there is none. -/
def getT (th : Array (Thunk ByteArray)) (i : ℕ) : ByteArray :=
  match th[i]? with
  | some x => x.get
  | none => ByteArray.empty

variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) {K : ℕ}
  (put : RealPts 256 K (Lf ()) → Option (List Bool)) (bk : AllPts 256 K (Lf ()) → List Bool)
  (O : ByteArray → ByteArray)

/-- **The answer to a typed query as data.** -/
def famRunB : (o : OracleName) → domOf 256 (Lf ()) o → Array (Thunk ByteArray)
  | .leaf, q => #[Thunk.pure (O (toBytes (codeRun Lf put bk .leaf q (0 : Fin 1))))]
  | .node, q => #[Thunk.pure (O (toBytes (codeRun Lf put bk .node q (0 : Fin 1))))]
  | .rleaf, q => #[Thunk.pure (O (toBytes (codeRun Lf put bk .rleaf q (0 : Fin 1))))]
  | .rnode, q => #[Thunk.pure (O (toBytes (codeRun Lf put bk .rnode q (0 : Fin 1))))]
  | .fb t, q => thunksOf (K + 1) fun j => O (toBytes (codeRun Lf put bk (.fb t) q j))
  | .g t, q => #[Thunk.pure (O (toBytes (codeRun Lf put bk (.g t) q (0 : Fin 1))))]
  | .ann, _ => #[]
  | .other, q => #[Thunk.pure (O (toBytes (codeRun Lf put bk .other q (0 : Fin 1))))]
  | .fbw t k, q => thunksOf (K + 1) fun j => O (toBytes (codeRun Lf put bk (.fbw t k) q j))

/-- The data as a typed answer. -/
def decRun (K : ℕ) : (o : OracleName) → Array (Thunk ByteArray) → rngOf 256 K o
  | .leaf, a => digS (getT a 0)
  | .node, a => digS (getT a 0)
  | .rleaf, a => digS (getT a 0)
  | .rnode, a => digS (getT a 0)
  | .fb _, a => (fun k => digS (getT a k.val), digS (getT a K))
  | .g _, a => digS (getT a 0)
  | .ann, _ => ()
  | .other, a => digS (getT a 0)
  | .fbw _ _, a => (fun k => digS (getT a k.val), digS (getT a K))

/-- **The typed oracle functions out of O, for a run.** -/
def famRunFast : Fam (typedOracleFamily 256 K (Lf ())) :=
  fun o q => decRun K o (famRunB Lf put bk O o q)

end TypedOracleCompiler.Run.PageRun
