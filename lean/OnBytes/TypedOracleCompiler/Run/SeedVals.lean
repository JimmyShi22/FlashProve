-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/SeedVals.lean: the typed pieces of the two queries from which the seeds of a stored
table's record are drawn, as values: one file of definitions, for the wire of the record and for an
encoding of its queries to take the same terms from.

The first query of a seed is typed as (round 1; the first format with the list root :: cfg, no
instance and some bits; no root of the round's own; a plain part), the second as (round 2; the
second format with the chain value; a plain part), both under one tag
(OnBytes/TypedOracleCompiler/Run/SeedPoints.lean, `q0`, `q1`). The programs hash a table's
name: its root, the digest of the three public files, and six words of the tables' shape
(`Fmt.tableName`,
Fmt/Rules4.lean).

Main names.
  `tag`: the tag of Test.
  `cfgL c`: the digest c of the public files, as the one digest behind the root.
  `shapeBytes`, `shapeBits`: the six words of the tables' shape, as bytes and as bits.
  `restOf_eq`: what stands behind the root in a table's name (`FirstName.restOf`) is the digest and
    then `shapeBytes`. `rest_size`, `rest_small`: its length is the digest's and 48; with a digest
    of 32 bytes it is below 2^32.
  `plainFirst r s a A`: a plain part of a list of rounds that begins with r: the slot's component of
    that round's fixed message.

Limits: definitions and three equations on bytes. The typed pieces are constants of the typed form:
no theorem here ties them to a string that is hashed. That no round of Test sends `plainFirst` is
not said, and is false where Test's first round sends its fixed message.

-/
import OnBytes.TypedOracleCompiler.Run.FirstName
import Fmt.Rules23Laws

set_option autoImplicit false

namespace TypedOracleCompiler.Run.SeedVals
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- The tag of the seeds' two queries: Test's. -/
abbrev tag : Tag := .test

/-- The digest of the three public files, as the one digest behind the root. -/
def cfgL (c : ByteArray) : List (Dig 256) := [bytesToDig c]

/-- The six words of the tables' shape, as a table's name has them. -/
def shapeBytes (a message tail logRows answers saltBytes : ℕ) : ByteArray :=
  Fmt.u64n a ++ Fmt.u64n message ++ Fmt.u64n tail ++ Fmt.u64n logRows ++ Fmt.u64n answers ++
    Fmt.u64n saltBytes

/-- The same as bits. -/
def shapeBits (a message tail logRows answers saltBytes : ℕ) : Bits :=
  bytesToBits (shapeBytes a message tail logRows answers saltBytes)

/-- What stands behind the root in a table's name is the digest, then the six words. -/
theorem restOf_eq (cfg : ByteArray) (a message tail logRows answers saltBytes : ℕ) :
    FirstName.restOf cfg a message tail logRows answers saltBytes =
      cfg ++ shapeBytes a message tail logRows answers saltBytes := by
  unfold FirstName.restOf shapeBytes
  simp only [ByteArray.append_assoc]

/-- Its length. -/
theorem rest_size (cfg : ByteArray) (a message tail logRows answers saltBytes : ℕ) :
    (FirstName.restOf cfg a message tail logRows answers saltBytes).size = cfg.size + 48 := by
  unfold FirstName.restOf
  simp only [ByteArray.size_append, Fmt.size_u64n]

/-- With a digest of 32 bytes it is below 2^32. -/
theorem rest_small (cfg : ByteArray) (hc : cfg.size = 32)
    (a message tail logRows answers saltBytes : ℕ) :
    (FirstName.restOf cfg a message tail logRows answers saltBytes).size < 2 ^ 32 := by
  rw [rest_size, hc]
  decide

/-- A plain part of a list of rounds that begins with r: the slot's component of that round's fixed
message. -/
def plainFirst (r : Round) (s : Shape) (a : RAnn r) (A : RoundSplits s) : PlainPart (r :: s) (a, A) :=
  .inl (.inr (a.plain r.dPlain).2)

end TypedOracleCompiler.Run.SeedVals
