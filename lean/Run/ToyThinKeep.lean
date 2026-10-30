-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyThinKeep.lean: at the toy of Run/ToyQ.lean, one family runs, and gives, at five queries, the
answers of another. The first is the single oracle's family with the hash's state kept (`famCK`,
Run/CodingThinKeep.lean). The second is the family that writes the strings of the encoding of the
queries (`gT`, Run/ToyThin.lean).

Two definitions for the guards, and the guards (#guard). Nothing is proved here: that the two
families are one is Run/CodingThinKeep.lean's theorem, under its two hypotheses. (`F : PageFit C D`;
`hf`, the law of `fits`: `famCK_eq`.)

Main names:
  `gTK`: `famCK` at the toy's data, with the test "the round is not 0" for `fits`. That test is good
    for these guards alone: it does not meet the theorem's law at every typed query.
  `same3 q`: the three blocks of a chain answer are the same under both families.

Guards. Rounds 1 and 2 (the branch with the state kept; that the data lie in the hash's domain is
guarded at round 1), round 0 (the other branch), a node, a leaf.

Limits: the toy is this library's own and its messages are short. This file says nothing on time.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingThinKeep
import Run.ToyThin

set_option autoImplicit false

namespace Run.Toy1.GK
open Iop Rom Compile Compile.Batch Run.Toy1 Run.Toy1.G

def gTK : Fam (spec 256 2 Lt) := famCK LfT pageTP PD (fun q => q.round != 0)

def same3 (q : FbIn 256 Lt .test) : Bool :=
  let a : (Fin 2 → Dig 256) × Dig 256 := gTK (.fb .test) q
  let b : (Fin 2 → Dig 256) × Dig 256 := gT (.fb .test) q
  hxd a.2 == hxd b.2 && hxd (a.1 0) == hxd (b.1 0) && hxd (a.1 1) == hxd (b.1 1)

#guard same3 q1
#guard same3 q2
#guard same3 q0
#guard hxd (gTK .node (bts dl, bts dr)) == hxd (gT .node (bts dl, bts dr))
#guard hxd (gTK .leaf lq) == hxd (gT .leaf lq)
-- at round 1 the data lie in the hash's domain: so the branch with the state kept is the one that
-- runs
#guard _root_.Fmt.hDom 162 PD.label 1 (bitsToBytes (match q1.head with | .f2 _ ρ => ρ | _ => [])) (roundBytes (PD.msg 1 (q1.rt.map digToBytes) q1.plain) (PD.kind 1) (PD.work 1) 0 (PD.nonce 1 q1.plain))

end Run.Toy1.GK
