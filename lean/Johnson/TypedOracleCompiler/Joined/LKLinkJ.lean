-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Joined/LKLinkJ.lean: a bare block that is a link of a batch with keys
(Johnson/TypedOracleCompiler/Joined/LKShared.lean) is a link over its reduction (OnBytes/TypedOracleCompiler/Joined/LinkJ.lean); and
a typed list whose blocks have their property is knowledge sound for one statement.

Rules alone. No clause of any block is shown here.


The row of three chains (`sndBKT_of_links`, OnBytes/TypedOracleCompiler/Joined/LinkJ.lean) and the step through
maps onto written rounds take, for the second chain, a `LinkJ` over a reduction, and for the first
and the third the clause `Know` for one statement. This file hands both over from typed lists.

Main names:
  `KObj.BK.LinkB.linkJ`: the two fields, as they are: `KnowJ` at an IOR's reduction is the library's
    `KnowB` (CompileK/Joined/BatchMid.lean). The output relation is the block's, enlarged by the
    statements outside the output joint's condition (`Reduction.orOff`).
  `KObj.LK.linkJ_blk`: a list of links, as one `LinkJ` over the reduction of `l.blk d`.
  `KObj.LK.know_blk`: `Know` of that reduction for one statement, if every block has its property.

Limits: those of Johnson/TypedOracleCompiler/Joined/LKShared.lean.

Terms: lean/GLOSSARY.md.
-/
import Johnson.TypedOracleCompiler.Joined.LKShared
import OnBytes.TypedOracleCompiler.Joined.LinkJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob IOR TypedOracleCompiler.Joined

/-- A block that is a link of a batch is a link over its reduction. -/
theorem BK.LinkB.linkJ {A B : JK} {b : BK A B} {An : RoundSplits b.R.shape} {N : ℕ} {kA : KK A} {kB : KK B}
    (h : b.LinkB An N kA kB) :
    LinkJ b.R.red An N kA.key kB.key A.on A.relR (Reduction.orOff B.on B.relR) b.ext b.err :=
  ⟨h.know, h.adm⟩

/-- **A typed list of links, as one link over the reduction of the list's one block.** -/
theorem LK.linkJ_blk {A B : JK} {N : ℕ} (l : LK A B) (d : A.W) (kA : KK A) (kB : KK B)
    (h : l.KeyedSh N kA kB) :
    LinkJ (l.blk d).R.red (shAn (l.blk d).R.shape) N kA.key kB.key A.on A.relR
      (Reduction.orOff B.on B.relR) (l.blk d).ext (l.blk d).err :=
  (LK.linkSh_blk l d kA kB h).linkJ

/-- A typed list whose blocks have their property: the clause for one statement. -/
theorem LK.know_blk {A B : JK} (l : LK A B) (d : A.W) (h : l.Each PG) :
    (l.blk d).R.red.Know A.on A.relR (Reduction.orOff B.on B.relR) (l.blk d).ext (l.blk d).err :=
  (LK.good l d h).know

end KObj
