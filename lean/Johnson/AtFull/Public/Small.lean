-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/Small.lean: publicOfO's SMALL STEPS P3 · P6 · P8 · P8' · P9 · P10 AND FIVE
  NUMBERS, AT THE WRITTEN VALUES, each asked whole of
Lean's kernel: seven closed facts and one negative test, over ONE withY | withS.
This file's text is made by program. The recursion limit is raised in this file (maxRecDepth
  1000000).
Nothing on soundness.
-/
import Johnson.AtFull.Public.Twins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace OnBytes.Road.K4.Trial.Small
open OnBytes OnBytes.Model OnBytes.Model.Layer

/-- The strict scan's WRITTEN value at the stored free numbers. -/
def PW : PolScan := VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines

/-- The layers' shape at that value. -/
def hW : Layer.Shape := Verify.layerShape PW

/-- A test at the value of the layers' layout's first half (false where it does not return). group
  reads
none of the three fields that the second half sets (cl, fo, kbm). -/
def withY (f : Lay → Bool) : Bool :=
  match baseNoFill hW VerifierAndGoals.Lines.callsRef with
  | .ok y => f y
  | .error _ => false

/-- A test at the scales, off the WRITTEN list of the scale file's words (false where scalesOf
  refuses). -/
def withS (f : Layer.Scales → Bool) : Bool :=
  match Layer.scalesOf hW Tie.Pv.Plan.scalesF.toArray with
  | .ok s => f s
  | .error _ => false

/-- A test at the lines callA as read (false where readLines refuses). -/
def withLines (f : List Attention.Line → Bool) : Bool :=
  match Attention.readLines PW.polCallsA with
  | .ok l => f l
  | .error _ => false

/-- A test at the configuration of the attention sub-protocol of group g (false where fill refuses).
  -/
def withCf (g : Nat) (f : Attention.Cfg → Bool) : Bool :=
  withY fun y => withS fun s => withLines fun l =>
    match Attention.fill PW y s l g with
    | .ok cf => f cf
    | .error _ => false


/-- `Layer.scalesHeld` returns at the layout's first half (`withY`) and the written scales. -/
theorem scalesHeld_W : withY (fun y => withS fun s => (Layer.scalesHeld y.h s).toOption.isSome) =
    true := by decide +kernel

/-- `Layer.noWrap` returns at the layout's first half (`withY`) and the written scales. -/
theorem noWrap_W : withY (fun y => withS fun s => (Layer.noWrap y.h s y.dq).toOption.isSome) = true
    := by decide +kernel

/-- `Layer.weightWidthsHeld` returns at the layout's first half (`withY`). -/
theorem widths_W : withY (fun y => (Layer.weightWidthsHeld y.h y.kinds).toOption.isSome) = true :=
    by decide +kernel

/-- `Head.vocabulary` returns at the head's shape of the layout's first half (`withY`). -/
theorem vocabulary_W : withY (fun y => (Head.vocabulary (Verify.headShape PW y)).toOption.isSome) =
    true := by decide +kernel

/-- `wsLayOf` returns at the weights' shape of the layout's first half (`withY`). -/
theorem wsLay_W : withY (fun y => (wsLayOf (Verify.weightShape PW y) y.h.p3 PW.lkW).toOption.isSome)
    = true := by decide +kernel

/-- `Layer.ropeOf` returns at the layout's first half (`withY`). -/
theorem rope_W : withY (fun y => (Layer.ropeOf y.h).toOption.isSome) = true := by decide +kernel

/-- At the layout's first half (`withY`): dq is 5120, p4 and p3 are set, NGr is 12, Lam is 4. -/
theorem numbers : withY (fun y => y.dq == 5120 && y.h.p4 && y.h.p3 && y.NGr == 12 && y.Lam == 4) =
    true := by
  decide +kernel
/-- A negative test, stated positively. -/
theorem numbers_no : withY (fun y => y.dq == 5121) = false := by decide +kernel
end OnBytes.Road.K4.Trial.Small

#print axioms OnBytes.Road.K4.Trial.Small.scalesHeld_W
#print axioms OnBytes.Road.K4.Trial.Small.noWrap_W
#print axioms OnBytes.Road.K4.Trial.Small.widths_W
#print axioms OnBytes.Road.K4.Trial.Small.vocabulary_W
#print axioms OnBytes.Road.K4.Trial.Small.wsLay_W
#print axioms OnBytes.Road.K4.Trial.Small.rope_W
#print axioms OnBytes.Road.K4.Trial.Small.numbers
#print axioms OnBytes.Road.K4.Trial.Small.numbers_no
