-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/LookAt.lean: the place of a lookup of the proof's first chain, as a function
of the public record alone: lookAt X i digits, with code. Three declarations (Place, digitsNext,
lookAt); no theorem; nothing is evaluated in this file.

What it is for. A link of the first chain has two lookups: one on the calls, one on the digits of
the smallness test. The verifier program's own routine Forest.pad (OnBytes/Model/Look.lean), and a
step that runs its flat form lkPad (OnBytes/K/Kc/FlatHear.lean), are called at calls, pub, lid and a
ledger F. The record of end values (endsOf) is called at three numbers of the plan: the lookup's
record of public numbers fs, the number lm, and the lookup's first slot F.next. The chain's plan
does not fix the calls: they come from the layouts. Place holds all of these; lookAt makes it for
link i and either lookup.

Limits. A SECOND WRITING: each entry repeats the arguments of the program's own call, read off its
text; the library's callers have named functions of the plan for some of them (foShapeG, slotNoG,
slotNoA, the lmb of bcRCG and bcRCA): this file names none and writes the plan's fields anew, so
that it loads without Mathlib; no theorem ties the two writings. AT A PLAN OF THE PLANNER's: the
digits' first slot reads ns, as the library's jLKAt does; at a free X ns and the slots in use may
part. AT THE DIGITS F IS NO STATE OF THE PROGRAM's: there other routines of the link have run
before; here F is the link's fresh state with next set to the plan's number: the link's slots, less
what follows, less the lookup's own scalars. No theorem says that the program's counter stands at
that number there. The stretch of the chain's
rounds that belongs to a lookup is not in the record. Nothing is said of any message, reading or
claim.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- A lookup of a sub-proof: what Forest.pad is handed there, the state from which it starts, the
plan's record of its shape. WHO READS WHAT: Forest.pad and lkPad read calls, pub, lid and F; the
record of end values reads fs, lm and F.next. -/
structure Place where
  name : String
  link : Nat
  calls : Array Call
  pub : Array Nat
  lid : Nat
  /-- the plan's state, its arrays allocated, before the slots are laid -/
  base : Fork
  /-- the state from which the routine starts: base.slots ns. Fork.slots leaves next as it is: at
  the calls it is the base's own (0: by law at the layers and attention, by the record's default at
  the head); at the digits it is set to the lookup's first slot -/
  F : Fork
  fs : Forest.Shape
  ns : Nat
  /-- the plan's lm -/
  lm : Nat

/-- The first slot of the lookup on the digits: the link's number of slots, less what follows
(behind), less the lookup's own scalars. NONE WHERE THAT WOULD FALL BELOW 0: ℕ's minus would give a
slot that is too low, in silence. -/
def digitsNext (ns behind elems : Nat) : Option Nat :=
  if behind + elems ≤ ns then some (ns - behind - elems) else none

/-- THE PLACE OF A LOOKUP, OF THE PUBLIC RECORD ALONE. i: the link's number, from 0; the head's is
the last. digits: the lookup on the digits; else the one on the calls.
Each entry is the arguments of the program's own call of Forest.pad, and of a LookPubOK of the
library (under OnBytes/Tie/Pv/Lookup/Ends/): calls: layers: OnBytes/Model/Layer.lean (hearLook;
runForkHidG2), FoLookPubGX0.lean · attention: Attention.lean (hear; Seam.start), FoLookPub0.lean ·
the head: HeadHeard.lean (hear), Head.lean (runForkHidH2), FoLookPubHX.lean · digits: Tail.lean
(transcriptF), FoLookPubZ.lean. The split by i is Plan.recordsOf's
(OnBytes/Tie/Pv/Plan/PlaceNums.lean).
AT THE DIGITS the routine does not start from a fresh state in the program: other routines of the
link have run. Here F is the link's fresh state WITH next SET TO THE LOOKUP's FIRST SLOT: the link's
number of slots, less that lookup's scalars, at the head also less the slots of the fork that
follows (written over X).
Forest.pad reads of the state its next, ns, the marks at its own slots and how many claims are owed
[reckoned; no theorem]. At the digits the fresh state has none owed where the program's has some.
The plan's tl gives the program's four arguments: the three routines between the plan and the call
(closeFuns, the opening at attention, drawMatrixF) write none of z1, z2, f9, lidb [read]; no other
write of them was met by a bounded search. -/
def lookAt (X : Verify.Public) (i : Nat) (digits : Bool) : Option Place :=
  let step := if X.p4 then 2 else 1
  let mk (kind : String) (calls : Array Call) (fs : Forest.Shape) (lid lm : Nat) (base : Fork)
      (ns : Nat) (tl : HTailF2) (behind : Nat) : Option Place :=
    if digits then
      (digitsNext ns behind (Forest.elems tl.f9)).map fun nx =>
        { name := s!"LINK {i} ({kind}) digits", link := i, calls := #[tl.z1.call, tl.z2.call],
          pub := tl.f9.pub, lid := tl.lidb, base := base, F := { base.slots ns with next := nx },
          fs := tl.f9, ns := ns, lm := 5 }
    else
      some { name := s!"LINK {i} ({kind}) calls", link := i, calls := calls, pub := fs.pub,
             lid := lid, base := base, F := base.slots ns, fs := fs, ns := ns, lm := lm }
  if i == step * X.NGr then
    mk "head" X.HLy.cl X.HLy.fs X.hS.LIDB X.hS.lmbH (({ trees := X.H.Fp.trees } : Fork).fillL)
      X.H.ns X.H.tl (wsForkSlots X.layers.wsLay.lk)
  else if i % step == 0 then
    X.G[i / step]?.bind fun hp =>
      mk "layers" X.y.cl X.y.fo X.y.h.lidb X.y.h.lmb hp.Fp.fillL hp.ns hp.tl 0
  else
    X.A[i / step]?.bind fun a =>
      mk "attention" (a.S.calls.map (·.call)) a.fs a.lid a.S.cf.lmb a.seam.Fp.fillL a.ns a.seam.tl 0

end VerifiableInference.Desc.First.Look
