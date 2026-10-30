-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/PublicAt.lean: the public part of a stage (`publicOf`,
OnBytes/Model/VerifyPublic.lean) and the planner's text with the digest of the public files as an
argument (`plannedAt`, OnBytes/Tie/ChainsAtCfg.lean), each with the second hash function as a
further argument.

Ten definitions of the library name the second hash function (`secondHashFunction`, OnBytes/Hash/SecondHashFunction.lean) on
the way of `publicOf`: `tableDigest`, `tableHeld`, `textTH`, `parDigests`, `hParOf`, `hPar`
(OnBytes/Model/Config.lean); `callsDigest`, `config` (OnBytes/Model/AttentionConfig.lean);
`callsDigest`, `publicOf` (OnBytes/Model/VerifyPublic.lean). Each has a twin here: its name with an
O behind it, and a first argument o of the type Nat → ByteArray → ByteArray. A twin's body is the
library's, line for line, with o for `secondHashFunction`, the twin at o for each of the ten names, and
`Fmt.olderTK o` (Fmt/RequestItem.lean) for `secondHashFunctionTree`: that file already has the tree hash over an
argument. Nothing is dropped: every test, on values and on digests, stands, in its order and under
its name, and the record keeps its three digests of the lists of lookup calls, made by
o. Every other routine on the way is called as it is. An eleventh twin, `plannedAtO`, is `plannedAt`
over `publicOfO o`; the chains and the links are made as they are.

This file holds definitions and no theorem. They are tools: no description of the protocol is named.
It imports two files by name. OnBytes/Model/Verify.lean states no theorem. Fmt/RequestItem.lean
states theorems on tests of its own, which are not used here. The twins were made by a program from
the library's text.

What of OnBytes/Model/ is used: all that `publicOf` and `plannedAt` call.

Limits. The twins are a copy. What ties each to the library's text is one equation, at `secondHashFunction`
(Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean). At another o nothing says that `publicOfO` returns
a value. The imported files still define the second hash function: whether the terms here reach a
hash by name is a matter of a walk through the constants that they use, which is not made here.
Nothing on soundness.
-/
import OnBytes.Model.Verify
import Fmt.RequestItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

section
open OnBytes OnBytes.Model OnBytes.Model.Config
variable (o : Nat → ByteArray → ByteArray)

/-- `tableDigest` (OnBytes/Model/Config.lean) with the second hash function as the argument o. -/
def tableDigestO (words : ByteArray) : ByteArray := o tableHashNumber words

/-- `tableHeld` (OnBytes/Model/Config.lean) with the second hash function as the argument o. -/
def tableHeldO (P : PolScan) (t : PublicTable) (table : Array Nat) : Except String Unit :=
  let mine := tableDigestO o (table.foldl (fun b x => b ++ word32 x) ByteArray.empty)
  refuseIf ((P.tableExpected t).any fun d => d != mine) t.refusal

/-- `textTH` (OnBytes/Model/Config.lean) with the second hash function as the argument o. -/
def textTHO (text : ByteArray) : Except String (ByteArray × Nat) := do
  refuseIf (decide (2 ^ 32 ≤ text.size)) "close-list-long"
  let w := word32 text.size ++ OnBytes.textWords text ++ Fmt.zeroBytes 28
  match Fmt.olderTK o w with
  | some d => pure (d, w.size / 4)
  | none => .error "internal-th"

/-- `parDigests` (OnBytes/Model/Config.lean) with the second hash function as the argument o. -/
def parDigestsO (pol KL : ByteArray) (layout : Option ByteArray) : Except String ParDigests := do
  let p ← textTHO o pol
  klHeld KL
  let k ←
    match Fmt.olderTK o KL with
    | some d => pure d
    | none => .error "KL-length"
  let l ←
    match layout with
    | some t => textTHO o t
    | none => pure (Fmt.zeroBytes 32, 0)
  pure { pol := p.1, polW := p.2, kl := k, klW := klWords KL, lay := l.1, layW := l.2 }

/-- `hParOf` (OnBytes/Model/Config.lean) with the second hash function as the argument o. -/
def hParOfO (d : ParDigests) : Except String ByteArray :=
  match Fmt.olderTK o (d.pol ++ word32 d.polW ++ d.kl ++ word32 d.klW ++ d.lay ++ word32 d.layW)
      with
  | some x => pure x
  | none => .error "internal-th"

/-- `hPar` (OnBytes/Model/Config.lean) with the second hash function as the argument o. -/
def hParO (pol KL : ByteArray) (layout : Option ByteArray) : Except String ByteArray := do
  hParOfO o (← parDigestsO o pol KL layout)

end

namespace Attention
open OnBytes OnBytes.Attention
open OnBytes.Model (refuseIf)
variable (o : Nat → ByteArray → ByteArray)

/-- `callsDigest` (OnBytes/Model/AttentionConfig.lean) with the second hash function as o. -/
def callsDigestO (lines : List Line) : ByteArray :=
  o 73 (textWords (String.join (lines.map Line.text)).toUTF8)

/-- `config` (OnBytes/Model/AttentionConfig.lean) with the second hash function as o. -/
def configO (P : Model.PolScan) (y : Model.Layer.Lay) (s : Model.Layer.Scales) (midQ : Nat → Nat) :
    Except String Config := do
  let h := P.h
  let lines ← readLines P.polCallsA
  refuseIf (h.Gk &&& (h.Gk - 1) != 0) "af-shape-heads"
  refuseIf (h.lmh < h.lt || h.lmh > 24 || h.lmo < h.lt || h.lmo > 24 || h.lmbA > 24 ||
    h.lmS > 24 || h.NAs == 0 || h.NAs > 64) "shape-request-matrix-A"
  let plans ← (List.range y.NGr).mapM (group P y s midQ lines)
  match plans with
  | X :: _ =>
    tableHeldO o P .exp X.S.Tt
    pure { plans := plans.toArray, hCallsA := callsDigestO o lines }
  | [] => throw "shape-L"

end Attention

section
open OnBytes OnBytes.Model OnBytes.Model.Verify
variable (o : Nat → ByteArray → ByteArray)

/-- `callsDigest` (OnBytes/Model/VerifyPublic.lean) with the second hash function as o. -/
def callsDigestO (word : String) (calls : List CallD) : ByteArray :=
  o 73 (OnBytes.textWords (callText word calls).toUTF8)

/-- `publicOf` (OnBytes/Model/VerifyPublic.lean) with the second hash function as the argument o. -/
def publicOfO (pol KL : ByteArray) (layout : Option ByteArray) : Except String Public := do
  let (P, y) ← polLayout pol
  let h := y.h
  -- the scales
  let sc ← Layer.scalesOf h (fileWords KL)
  Layer.scalesHeld h sc
  -- the tables of the gate and of the sigmoid
  tableHeldO o P .silu y.silu
  if h.p3 then tableHeldO o P .sigmoid y.fs
  Layer.noWrap h sc y.dq
  let _ ← hParO o pol KL layout
  -- the widths of the weights, and the committed matrix
  Layer.weightWidthsHeld h y.kinds
  let hS := headShape P y
  Head.vocabulary hS
  let wsLay ← wsLayOf (weightShape P y) h.p3 P.lkW
  -- the rotary table
  let rope ← Layer.ropeOf h
  tableHeldO o P .rope rope
  -- the layouts of the head and of attention
  let tails := Layer.tailsOf y
  let HLy ← Head.layout hS y.tauFC
  let iQA := (Layer.matIx y).iQA
  let (A0, hCallsA) ←
    if h.p4 then do
      let c ← Attention.configO o P y sc fun g => ((tails.getD g {}).mats.getD iQA {}).aId
      pure (c.plans, c.hCallsA)
    else pure (#[], ByteArray.empty)
  -- the plans
  let layers ← Layer.Pub.of y sc rope wsLay P.h.V #[] P.settings
  let G ← Layer.plansG layers
  let seenG := G.map fun O => (⟨O.tl, O.Fp, O.Tp⟩ : SubPlan)
  let seenA ← attentionOwners h.p4 y.NGr seenG
    (A0.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩)
  let A := A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seenA
  let owner ← ownerOf y G
  let H ← Head.planH2 P.settings hS HLy (borderOf y) owner y.NGr P.lkW
  -- The C++ counts its comparisons of records as it makes them: one for each group but the first,
  -- for each attention and for the head. Here the count is computed from the numbers of plans, so
  -- crossPlans' first test shows only that the owners' and the readers' records are that many.
  crossPlans (G.size - 1 + A.size + 1) y.NGr h.p4 tails seenG seenA ⟨H.tl, H.Fp, H.Tp⟩
  let digests : Digests :=
    { hCalls := callsDigestO o "call" y.calls.toList, hCallsA := hCallsA,
      hCallsH := callsDigestO o "callH" HLy.calls.toList }
  pure { P := P, digests := digests, layers := layers, hS := hS, HLy := HLy, G := G, A := A,
         H := { H with Fp := H.Fp.trimL }, owner := owner }

end

section
open OnBytes.Params OnBytes.Model OnBytes.Model.Verify
variable (o : Nat → ByteArray → ByteArray)

/-- `plannedAt` (OnBytes/Tie/ChainsAtCfg.lean) with the second hash function as the argument o. c
need not be the digest of these files. -/
def plannedAtO (pol KL : ByteArray) (layout : Option ByteArray) (c : ByteArray) :
    Except String Verify.Planned := do
  let X ← publicOfO o pol KL layout
  let chains ← chainsOf X layout c
  pure { X := X, cfg := c, chains := chains, built := ← builtOf X chains }

end

end VerifiableInference.PlanWritten
