-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/TailQuiet.lean: the named hypothesis `TailQuiet` of OnBytes/K/Kc/QuietLink.lean holds:
the four routines of the smallness test that the head's walk and the check's own tests call
(`objectsF`, `selfTest`, `coefficients`, `rkSelfTest`, OnBytes/Model/Tail.lean) do not touch the
channel and do not depend on the context.

Why here: a hypothesis that is not shown to hold could be false, and a law under a false
hypothesis says nothing. The proofs go along each routine's text by the rules of
OnBytes/K/Kc/Quiet.lean. Nothing else is said of the smallness test.

Main theorems: `tailQuiet`; `lawWalk_plain`, `lawSelfTests_plain`: the two laws of
OnBytes/K/Kc/QuietLink.lean without a hypothesis.

Not claimed. Nothing on the dry run. Nothing on soundness. The program does not import this file.
-/
import OnBytes.K.Kc.QuietLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM LinkCtx)

/-- A claim on long runs. -/
instance quiet_t2Lin (a : Model.Aff) (runs : Array Model.Run2) :
    Quiet (Model.t2Lin a runs) := by
  unfold Model.t2Lin
  infer_instance

/-- A virtual row's weights. -/
instance quiet_rowWeights (X : Model.HTree) (r : Model.HRow) :
    Quiet (Model.rowWeights X r) := by
  unfold Model.rowWeights
  infer_instance

/-- The equation's terms on one array. -/
instance quiet_doorTerms (born : Nat) (array : String) (X : Model.HTree) :
    Quiet (Model.doorTerms born array X) := by
  unfold Model.doorTerms
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInS _ ?_ _ _
    | refine quiet_forInA _ ?_ _ _
    | refine quiet_foldlM _ ?_ _ _
    | refine quiet_forMA _ ?_ _
    | refine quiet_forML _ ?_ _
    | refine quiet_mapMA _ ?_ _
    | split

/-- HTailF2.linJoin9 is quiet. -/
instance quiet_linJoin9 (tl : Model.HTailF2) :
    Quiet (tl.linJoin9) := by
  unfold Model.HTailF2.linJoin9
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInS _ ?_ _ _
    | refine quiet_forInA _ ?_ _ _
    | refine quiet_foldlM _ ?_ _ _
    | refine quiet_forMA _ ?_ _
    | refine quiet_forML _ ?_ _
    | refine quiet_mapMA _ ?_ _
    | split
    | dsimp only

/-- HTailF2.linBits9 is quiet. -/
instance quiet_linBits9 (tl : Model.HTailF2) :
    Quiet (tl.linBits9) := by
  unfold Model.HTailF2.linBits9
  infer_instance

/-- HTailF2.linTie is quiet. -/
instance quiet_linTie (tl : Model.HTailF2) (mu : Nat) :
    Quiet (tl.linTie mu) := by
  unfold Model.HTailF2.linTie
  infer_instance

/-- HTailF2.linRead is quiet. -/
instance quiet_linRead (tl : Model.HTailF2) (Fn : Model.HFun) (sg laid : Nat) (sums : E) :
    Quiet (tl.linRead Fn sg laid sums) := by
  unfold Model.HTailF2.linRead
  infer_instance

/-- HTailF2.weightsF is quiet. -/
instance quiet_weightsF (tl : Model.HTailF2) :
    Quiet (tl.weightsF) := by
  unfold Model.HTailF2.weightsF
  infer_instance

/-- HTailF2.objectsF is quiet. -/
instance quiet_objectsF (tl : Model.HTailF2) (funs : Array Model.HFun) :
    Quiet (tl.objectsF funs) := by
  unfold Model.HTailF2.objectsF
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _
    | refine quiet_forInS _ ?_ _ _
    | refine quiet_forInA _ ?_ _ _
    | refine quiet_foldlM _ ?_ _ _
    | refine quiet_forMA _ ?_ _
    | refine quiet_forML _ ?_ _
    | refine quiet_mapMA _ ?_ _
    | split

/-- HTailF2.selfTestF is quiet. -/
instance quiet_selfTestF (tl : Model.HTailF2) (nU : Array Nat) :
    Quiet (tl.selfTestF nU) := by
  unfold Model.HTailF2.selfTestF
  infer_instance

/-- HTailF2.selfTest is quiet. -/
instance quiet_selfTest (tl : Model.HTailF2) (nU : Array Nat) :
    Quiet (tl.selfTest nU) := by
  unfold Model.HTailF2.selfTest
  infer_instance

/-- HTailF2.coefficientsF is quiet. -/
instance quiet_coefficientsF (tl : Model.HTailF2) :
    Quiet (tl.coefficientsF) := by
  unfold Model.HTailF2.coefficientsF
  infer_instance

/-- HTailF2.coefficients is quiet. -/
instance quiet_coefficients (tl : Model.HTailF2) :
    Quiet (tl.coefficients) := by
  unfold Model.HTailF2.coefficients
  infer_instance

/-- HTailF2.tileSelfTestF is quiet. -/
instance quiet_tileSelfTestF (tl : Model.HTailF2) :
    Quiet (tl.tileSelfTestF) := by
  unfold Model.HTailF2.tileSelfTestF
  repeat' first
    | infer_instance
    | refine qbS ?_ ?_
    | intro _

/-- HTailF2.rkSelfTest is quiet. -/
instance quiet_rkSelfTest (tl : Model.HTailF2) :
    Quiet (tl.rkSelfTest) := by
  unfold Model.HTailF2.rkSelfTest
  infer_instance

/-- **The named hypothesis holds.** -/
theorem tailQuiet : TailQuiet :=
  ⟨fun tl funs => quiet_objectsF tl funs, fun tl nU => quiet_selfTest tl nU,
    fun tl => quiet_coefficients tl, fun tl => quiet_rkSelfTest tl⟩

/-- **The walk**, without a hypothesis. -/
theorem lawWalk_plain (R : Model.Head.Run) (tl : Model.HTailF2) (wo : Model.WsForkOut)
    (L : LinkCtx) : LawStill (Model.Head.walk R tl wo L) (flatWalk R tl wo L) :=
  lawWalk tailQuiet R tl wo L

/-- **The check's own tests**, without a hypothesis. -/
theorem lawSelfTests_plain (R : Model.Head.Run) (tl : Model.HTailF2) (wo : Model.WsForkOut)
    (L : LinkCtx) : LawStill (Model.Head.selfTests R tl wo L) (flatSelfTests R tl wo L) :=
  lawSelfTests tailQuiet R tl wo L

end OnBytes.K.Kc

#print axioms OnBytes.K.Kc.tailQuiet
#print axioms OnBytes.K.Kc.lawWalk_plain
#print axioms OnBytes.K.Kc.lawSelfTests_plain
