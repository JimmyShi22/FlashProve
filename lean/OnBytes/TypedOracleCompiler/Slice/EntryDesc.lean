-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryDesc.lean: the description D : XD of the entry's chain as a function of a
ground (OnBytes/Tie/EntryGround.lean: the constants of a setting as one record) and of the digest c
of the public files, which a table holds.

No number of a model's size stands in a definition.

What the frame of OnBytes/TypedOracleCompiler/Slice/EntryX.lean reads of the description (rounds' data, stored
openings, depth, blocks, field) does not hang on c: so not on the tables. c stands in `base.cfg` and
in `base.params` alone.

The statement holds both tables' answers: it is no function of two roots.
`base.statement` is not read (XD's own word), and `stm` here is the statement at empty lists of
answers. Whoever spells the first call (the page) takes the statement from the instance:
`entryStatementOf` below.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryGrounds
import OnBytes.TypedOracleCompiler.Slice.EntryX
import OnBytes.TypedOracleCompiler.Run.AllRoots

set_option autoImplicit false

namespace TypedOracleCompiler.Slice

open OnBytes.Tie (EntryGround linkAtCfg)
open TypedOracleCompiler.Run.PQ (XD)

/-- The description of the entry's chain at a ground and a digest. Base: the port's own
description (`Params.entrySpecOf`) at the ground's parameters with c for the digest, the ground's
rounds, an empty statement. -/
def entryXD (G : EntryGround) (c : ByteArray) : XD :=
  ⟨(OnBytes.Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty).base,
    fun r0 r1 => OnBytes.Params.Link.statement ⟨r0, []⟩ ⟨r1, []⟩, G.rs.map (·.2)⟩

/-- The statement that the port's description holds at two tables: roots AND answers. -/
def entryStatementOf (first further : OnBytes.Params.TableName) : ByteArray :=
  OnBytes.Params.Link.statement first further

/-- The port's description at two tables is D's base with that statement, and D's stored
openings. -/
theorem entryXD_spec (G : EntryGround) (c : ByteArray) (first further : OnBytes.Params.TableName) :
    OnBytes.Params.entrySpecOf (linkAtCfg G.q c) G.rs (OnBytes.Params.Link.statement first further) =
      ⟨{ (entryXD G c).base with statement := entryStatementOf first further },
        (entryXD G c).stored⟩ := rfl

/-! ## What does not hang on the digest -/

theorem entryXD_stored (G : EntryGround) (c c' : ByteArray) :
    (entryXD G c).stored = (entryXD G c').stored := rfl

theorem entryXD_a (G : EntryGround) (c c' : ByteArray) : (entryXD G c).a = (entryXD G c').a := rfl

theorem entryXD_xs (G : EntryGround) (c c' : ByteArray) :
    (entryXD G c).xs = (entryXD G c').xs := rfl

theorem entryXD_plan (G : EntryGround) (c : ByteArray) :
    (entryXD G c).base.plan = G.q.given.plan := rfl

theorem entryXD_rounds (G : EntryGround) (c : ByteArray) :
    (entryXD G c).base.rounds = G.rs.map (·.1) := rfl

theorem entryXD_cfg (G : EntryGround) (c : ByteArray) : (entryXD G c).base.cfg = c := rfl

theorem entryXD_params (G : EntryGround) (c : ByteArray) :
    (entryXD G c).base.params = G.bytesAt c := rfl

theorem entryXD_ds (G : EntryGround) (c c' : ByteArray) :
    (entryXD G c).ds = (entryXD G c').ds :=
  TypedOracleCompiler.Run.PQ.rds_congr _ _ rfl rfl

theorem entryXD_K (G : EntryGround) (c c' : ByteArray) : (entryXD G c).K = (entryXD G c').K :=
  TypedOracleCompiler.Run.PQ.kOf_congr _ _ rfl rfl rfl

end TypedOracleCompiler.Slice
