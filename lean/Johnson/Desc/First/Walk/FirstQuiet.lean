-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Walk/FirstQuiet.lean: two whole steps of the first chain as plain functions on
data: what stands between a link's first call and the first round of its sub-proof, at an attention
link and at a layers' link behind link 0.

  startFork       the fork from which a sub-proof starts: the record's planned fork, every virtual
                  row with its weights at 0, n empty slots: written anew after the two pure
                  routines of the program `verify-on-bytes` (Fork.fillL,
                  OnBytes/Model/Hide.lean:403-405; Fork.slots, :239-245)
  attFirstQuiet   the walk's lines (front: Quiet.lean) and the start of attention's routine
                  (Seam.start, OnBytes/Model/Attention.lean:61-63: two lines)
  layFirstQuiet   the walk's lines and the head of the layers' routine (runForkHidG2,
                  OnBytes/Model/Layer.lean:579-584: two public tests and one line)

Not here: link 0 (its index masks: StagesLinks.lean:561-565: LinkZero.lean): both functions refuse
there. The head's link.

Limits. No round, no item, no column; the statement and the book are not read. No Blk, no Ctx, no
SubM, no LinkM in any type of this file. The records are that verifier's, carried whole; on their
homes see Quiet.lean's head.
No soundness: definitions with code.

-/
import Johnson.Desc.First.Walk.Quiet
import OnBytes.Model.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk
open OnBytes OnBytes.Model

/-- Every virtual row gets its K weights, all 0.                                          after
  Fork.fillL, Hide.lean:403-405 -/
def weightsAtZero (F : Fork) : Fork :=
  { F with trees := F.trees.map fun X =>
    { X with rows := X.rows.map fun r => { r with L := Array.replicate X.K zeroE } } }

/-- n slots, none of them filled.                                                         after
  Fork.slots, Hide.lean:239-245 -/
def emptySlots (F : Fork) (n : Nat) : Fork :=
  { F with
    ns := n
    vp := Array.replicate n zeroE
    mf := Array.replicate n zeroE
    LS := Array.replicate n zeroE
    gotF := Array.replicate n false }

/-- The fork from which a sub-proof starts.      Attention.lean:62 · Layer.lean:584, from the
  record's planned fork (StagesLinks.lean:572) -/
def startFork (X : LinkPub) (ns : Nat) : Fork := emptySlots (weightsAtZero X.Fp) ns

/-- What an attention link's «0.quiet» lays. -/
structure AttStart where
  /-- the link's context -/
  L : LinkCtx
  /-- the walk's result -/
  out : Proof.LinksResult
  /-- the sub-proof's fork -/
  F : Fork
  /-- the smallness test's record -/
  tl : HTailF2

/-- **«0.quiet» at an attention link.** ns: the plan's number of slots. tl₀: the plan's record of
  the smallness test.
 [Q0] the link is not link 0 (its index masks: LinkZero.lean)
   StagesLinks.lean:562
 [W1] [W2] (e1) (e2) front
   StagesLinks.lean:566-570
 (e5) the fork: startFork
   Attention.lean:62
 (e6) the smallness test's record is the plan's, its list of tables open, no matrix drawn
   Attention.lean:63 -/
def attFirstQuiet (X : LinkPub) (l ns : Nat) (tl₀ : HTailF2) (check : ChainCheck) (out :
    Proof.LinksResult) :
    Except String AttStart :=
  if l == 0 then .error "Q0: link 0 has a step of its own"
  else match front X l check out with
    | .error e => .error e
    | .ok (L, out) => .ok ⟨L, out, startFork X ns, { tl₀ with funClosed := false, foldDrawn := 0 }⟩

/-- What a layers' link's «0.quiet» lays. -/
structure LayStart where
  /-- the link's context -/
  L : LinkCtx
  /-- the walk's result -/
  out : Proof.LinksResult
  /-- the sub-proof's fork -/
  F : Fork

/-- Rows and columns of a fork's arrays.
  Layer.lean:582 -/
def sizes (F : Fork) : Array (Nat × Nat) := F.trees.map fun X => (X.R, X.K)

/-- **«0.quiet» at a layers' link behind link 0.** p4: attention links stand between the layers'. g:
  the group. Tp, Fp, ns: the plan's list, planned
fork and number of slots.
 [Q0] the link is not link 0
   StagesLinks.lean:562
 [W1] [W2] (e1) (e2) front
   StagesLinks.lean:566-570
 [G1] «internal-g-link»: the link is the group's
   Layer.lean:580
 [G2] the link's list is the plan's, and the link's arrays have the sizes of the plan's
   Layer.lean:583
 (e5) the fork: startFork
   Layer.lean:584 -/
def layFirstQuiet (X : LinkPub) (l : Nat) (p4 : Bool) (g : Nat) (Tp : Tail2) (Fp : Fork) (ns : Nat)
    (check : ChainCheck)
    (out : Proof.LinksResult) : Except String LayStart :=
  if l == 0 then .error "Q0: link 0 has a step of its own"
  else match front X l check out with
    | .error e => .error e
    | .ok (L, out) =>
      if !(L.link == (if p4 then 2 * g else g)) then .error
          "G1: internal-g-link: the link is not the group's"
      else if !(L.list.nt == Tp.nt && sizes X.Fp == sizes Fp) then .error
          "G2: the link's list or sizes are not the plan's"
      else .ok ⟨L, out, startFork X ns⟩

end Johnson.Desc.First.Walk
