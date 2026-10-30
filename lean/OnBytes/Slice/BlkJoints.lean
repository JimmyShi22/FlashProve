-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkJoints.lean: what is known between two blocks of the program's run on a link's
chain.

OnBytes/Slice/BlkChain.lean follows a property from block to block along a run of the program's
link; there the joints, what is known between two blocks, are parameters. This file writes the
joints down. A joint says of the run that it is a run on a given view (OnBytes/Slice/BlkSeat.lean:
`OnView`), which rounds are not yet closed, which codes the statement has and how many roots have
been received. It says that the claim that the program holds, read in the field
(OnBytes/Slice/BlkRead.lean), is a given claim. How the columns that a later block will read are
tied to the written oracles is a parameter (`Tie`). The joint before the base case is in
OnBytes/Slice/BlkJointLast.lean.

Main definitions.
 `StageCodes`   the codes and the numbers of row variables that a stage of the program names are
                those of a stage of the proximity test.
 `RunAt`        what every joint says of the run.
 `GroupAt`      the joint before a fold.
 `SingleAt`     the joint after a fold.

Not claimed. No theorem is in this file.
-/
import OnBytes.Slice.BlkChain
import OnBytes.Slice.BlkFoldVec
import OnBytes.Slice.BlkSeat
import OnBytes.Slice.ProgCodes

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (IoppStage)

/-- The codes and the numbers of row variables that the program's stage cur names are those of
the stage s. -/
structure StageCodes (s : Sg) (cur : IoppStage) (codes : Codes) : Prop where
  /-- the main code -/
  base : ∃ cd, codes.base[cur.code]? = some cd ∧ codeOf cd = s.C
  /-- the mask code -/
  mask : codeOf (codes.mask.getD cur.maskCode default) = s.Z
  /-- the row variables of the main table -/
  k : cur.k = s.h + s.g
  /-- the row variables of the mask table -/
  h : cur.h = s.h

/-- What every joint says of the run. It is a run on the view V. The rounds that are not yet
closed are rest. The statement's codes are K. The number of roots received is roots. A sample has
one answer. -/
structure RunAt (V : Fmt.View) (K : Codes) (roots : Nat) (rest : List Fmt.RoundView) (answers : Nat)
    (c : Ctx) : Prop where
  /-- the run is a run on the view -/
  onView : OnView V c
  /-- the rounds that are not yet closed -/
  pending : c.ch.pending = rest
  /-- the statement's codes -/
  codes : c.st.codes = K
  /-- the number of roots received -/
  roots : c.ch.roots = roots
  /-- a sample has one answer -/
  answers : answers = 1

/-- The joint before a fold at the stage s. q: the claim. Tie: what ties the columns of the
group's members and of the fresh mask to the written oracles, and what else is public of the row
and the layout. -/
structure GroupAt (V : Fmt.View) (K : Codes) (roots : Nat) (s : Sg) (q : GE × (s.cIn.J → GE))
    (rest : List Fmt.RoundView) (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop) (answers : Nat)
    (c : Ctx) (row : GroupRow) (L : GroupLayout) (mask : Option Nat) : Prop where
  /-- what every joint says of the run -/
  run : RunAt V K roots rest answers c
  /-- the program's row on the group, read in the field, is the claim -/
  claim : stmG s row = q
  /-- no tensor of the row's form has a written-out factor -/
  plain : PlainForm row.c
  /-- the fold's fresh mask has come, and the tie holds of it -/
  mask : ∃ o, mask = some o ∧ Tie c row L o

/-- The joint after a fold at the stage s. q: the claim on the three folded rows. -/
structure SingleAt (V : Fmt.View) (K : Codes) (roots : Nat) (s : Sg) (q : GE × (s.cMid.J → GE))
    (rest : List Fmt.RoundView) (Tie : Ctx → SingleRows → Prop) (answers : Nat) (c : Ctx)
    (rows : SingleRows) : Prop where
  /-- what every joint says of the run -/
  run : RunAt V K roots rest answers c
  /-- the program's claim on the three folded rows, read in the field, is the claim -/
  claim : stmS s rows = q
  /-- the tie -/
  tie : Tie c rows

end OnBytes.Slice
