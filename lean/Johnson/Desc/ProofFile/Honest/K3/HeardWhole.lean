-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/HeardWhole.lean: for the callers of a proof file's lookup: what the
verifier program's structure of a lookup (`Model.Forest.Heard`, OnBytes/Model/Look.lean) holds that
depends on the challenges and the public shape alone, as one structure, made of the challenges
heard. Two definitions.

Terms. Honest/K3/GLOSSARY.md ("heard structure", "open part").

What is defined.
  `lookHeardAt h base heard`: the structure. h is the lookup's shape; base is the number of rounds
    of the chain that stand in front of the lookup; heard is the list of the chain's challenges from
    its first round on.
  `OpenSame A B`: two structures agree in the eleven fields that are filled.

The eleven fields that are filled.
  shape: the argument.
  theta, alpha: the run's points (`ptsOf`, Honest/K3/Heard.lean).
  zx, zy, zk: the key tree's last point, cut (`keyPtsAt`, Heard.lean).
  e: each call's weight at zy.
  zb0, zb1: the challenges of the leaves' and of the bits' sumcheck (`leavesR`, `bitsR`,
    Heard.lean).
  tT: each call's table at its coordinates of zb0.
  leavesA: alpha - 1 - the joined table at zb0.
The formulas of e, tT and leavesA are to the letter those of `toHeard`
(Johnson/Desc/First/Look/K3LookupGeneral.lean).

Users. That the structure of the hearing at a place has these eleven fields is shown in
Honest/K3/Law/HeardWholeLaw.lean; by evaluation, in Honest/K3/HeardWholeGuards.lean
[not in this library].

Limits. All other fields are blank, at the structure's own defaults: a, rows, leaves, sBit, cEnd,
owedObjects, owedPlanes, owedJoin. Of these, rows, leaves and cEnd hold forms on values that are
sent or hidden; sBit and the three numbers depend on the ledger in front. A caller must not read
them off this structure. So the equation "the hearing's structure = lookHeardAt ..." is false of a
real structure and should not be stated: `OpenSame` is the relation to state.
Definitions alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E subE oneE)
open OnBytes.Model.Forest (callWeight tableAt joinedTableAt)

/-- **The verifier program's structure of the lookup of shape h, as far as it depends on the
challenges and the shape alone**; all other fields are blank. -/
def lookHeardAt (h : OnBytes.Model.Forest.Shape) (base : Nat) (heard : List Fmt.Drawn) :
    OnBytes.Model.Forest.Heard :=
  let f := VerifiableInference.Desc.K3.faceOf h
  let p := ptsOf f base heard
  let k := keyPtsAt h base heard
  let zb0 := leavesR f base heard
  let tT := h.calls.map fun c => tableAt c (zb0.extract (h.kT - c.k) h.kT)
  { shape := h, theta := p.theta, alpha := p.alpha, leaves := {}
    leavesA :=
      subE (subE p.alpha oneE) (joinedTableAt h p.theta tT (zb0.extract h.kT (h.kT + h.cK)))
    zx := k.zx, zy := k.zy, e := (Array.range h.NC).map (callWeight h k.zy), zb0 := zb0
    zb1 := bitsR f base heard, tT := tT, zk := k.zk }

/-- **Two structures agree in the eleven fields.** -/
structure OpenSame (A B : OnBytes.Model.Forest.Heard) : Prop where
  shape : A.shape = B.shape
  theta : A.theta = B.theta
  alpha : A.alpha = B.alpha
  leavesA : A.leavesA = B.leavesA
  zx : A.zx = B.zx
  zy : A.zy = B.zy
  e : A.e = B.e
  zb0 : A.zb0 = B.zb0
  zb1 : A.zb1 = B.zb1
  tT : A.tT = B.tT
  zk : A.zk = B.zk

end ProofFile.Honest.K3
