-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/PlanK6Door.lean: the cheap public test for the output head's own rounds
(Johnson/Desc/Kinds/PlanK6Test.lean: planK6V), at a View that is built from plain public arguments.
Definitions with code only. No Mathlib. Meant for an entry of the verifier's list of public tests
(lawsAsk, Johnson/Desc/Laid/ProofAsks.lean).

The arguments.
  cs, layout   the codes; the request's layout.
  NM, NHf, ns  how many matrices the output head's list has; two numbers of the head's sizes.
  labs a   the label of matrix number a of that list.
  num l m  the number of message m of segment l among the statement's oracle messages.
  arr j t  the number of the oracle message at tree j, tenant t (its Merkle tree's number, and its
          position among the messages that share that tree's leaves).
  group    the sampled oracle messages of the head's segment, each as (tree, tenant). sent0: those
          sent in the segment's first sending.
  mems     every sampled oracle message of the request's own rounds: its shape and its (tree,
          tenant).
  n, rb    the number of the message that holds the mask row; the logarithm of the number of mask
          rows over which its entries are spread.

Main names.
  ownerP lab   the segment that owns the array with this label, and the array's name in the layout.
  arrV, memP   what the test reads of an array and of an oracle message.
  viewPlain    the View.
  planK6Door   THE TEST.

Not claimed here. No theorem. What acceptance implies: Law/PlanK6View.lean (planK6_of_door). Which
terms are passed for the arguments is not said here. Nothing on soundness.

-/
import Johnson.Desc.Kinds.PlanK6Test
import Johnson.Desc.Kinds.Law.LaidOffPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (ReqArray ReqLayout)

/-- The segment that owns the array with this label, and the array's name in the layout. -/
def ownerP (lab : Nat) : Nat × String :=
  (if lab / 256 = 13 then 24 else if lab / 256 < 13 then 2 * (lab / 256 - 1)
    else 2 * (lab / 256 - 14) + 1, "M" ++ toString (lab % 256))

/-- What the test reads of an array of segment k. -/
def arrV (num : Nat → Nat → Nat) (k : Nat) (A : ReqArray) : ArrV :=
  { num := num k A.message, ends := A.blocks.map fun b => (lastRowOf b, lastPlaceOf b) }

/-- What it reads of a sampled oracle message. -/
def memP (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (group sent0 : List (Nat × Nat))
    (y : OnBytes.OracleShape × (Nat × Nat)) : MemV :=
  { inGroup := group.contains y.2
    atZero := sent0.contains y.2
    num := arr y.2.1 y.2.2
    mainRows := y.1.mainRows
    maskRows := y.1.maskRows
    ellMain := (cs.base.getD y.1.code default).ell
    ellMask := (cs.mask.getD y.1.maskCode default).ell }

/-- The View. -/
def viewPlain (cs : OnBytes.Codes) (layout : ReqLayout) (NM NHf ns : Nat) (labs : Nat → Nat)
    (num arr : Nat → Nat → Nat) (group sent0 : List (Nat × Nat))
    (mems : List (OnBytes.OracleShape × (Nat × Nat))) : View :=
  { NHf := NHf
    ns := ns
    arrs := (List.range NM).map fun a =>
      (a, (VerifiableInference.Desc.arrayOf layout (ownerP (labs a)).1 (ownerP (labs a)).2).map
        (arrV num (ownerP (labs a)).1))
    groupNums := group.map fun x => arr x.1 x.2
    mems := mems.map (memP cs arr group sent0) }

/-- **The test.** -/
def planK6Door (cs : OnBytes.Codes) (layout : ReqLayout) (NM NHf ns : Nat) (labs : Nat → Nat)
    (num arr : Nat → Nat → Nat) (group sent0 : List (Nat × Nat))
    (mems : List (OnBytes.OracleShape × (Nat × Nat))) (n rb : Nat) : Bool :=
  planK6V (viewPlain cs layout NM NHf ns labs num arr group sent0 mems) n rb

end VerifiableInference.Desc.Kinds.Head.Law.OffPad
