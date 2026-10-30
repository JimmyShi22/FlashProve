-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqEndAtS.lean: the object's list at the datum read off the final batching, from
`r.ZkS` and the other hypotheses of its statement.

A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves. The list is its parameter list: `PreKnowR`, round-by-round
knowledge soundness, and `PreListR`, all other items (Hiop/RecSubs.lean). The datum is `R.O`
(Cb/Obj/LdObjectReqEnd.lean): the data of the test for linear constraints, read off the batching's
last claim.
One statement (`Cb.Spec.ldOREAtS_object`) and its proof: the analogue of `ldOREAt_object`
(Cb/Obj/LdObjectReqEndAt.lean), with `r.ZkS` (Cb/Req1/LdReqS.lean: the set of fresh facts closed
under join at each segment's entry) in the place of `r.Zk`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReqEndAt
import Cb.Obj.LdObjectReqSegS

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

def Spec.ldOREAtS_object (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (Kc : Type) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (r : LdReq (LdStage.start E Kc (R.O.jReq core)) R.z) (w₀ : R.Cf.conf.PIdx × R.Cf.conf.Cells)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (qi : Finset R.z.J.E.Pos → Prop) (z0 : R.Cf.conf.PIdx × R.G) (r0 : R.S.Rnd),
    r.Hyp → r.ZkS → r.chain.Fmt (R.O.fmtA core qφ) (R.O.fmtZAt R.bEnd Prod.fst qi) →
    PreListR R.O.left (R.O.termAt (B := R.bEnd) r Prod.fst w₀).req
      (R.O.termAt (B := R.bEnd) r Prod.fst w₀).hReq Prod.snd Prod.fst R.Cf.conf.Rreq
      (R.O.termAt (B := R.bEnd) r Prod.fst w₀).nums ∧
    PreKnowR R.O.left (R.O.termAt (B := R.bEnd) r Prod.fst w₀).req
      (fun a => (R.Cf.conf.D a.2 a.1.2).isSome) R.Cf.conf.RreqR
      ((R.O.termAt (B := R.bEnd) r Prod.fst w₀).cellsOf z0 r0)
      (R.O.termAt (B := R.bEnd) r Prod.fst w₀).nums.err

theorem ldOREAtS_object (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldOREAtS_object F E := fun Kc R core r w₀ qφ qi z0 r0 hH hZ hF =>
  ldOR_object F E R.O Kc (R.O.termAt (B := R.bEnd) r Prod.fst w₀) core z0 r0
    (ldOS_okAtS F E R.O Kc core _ R.bEnd Prod.fst r w₀ qφ qi (ldOREAt_end F E Kc R) hH hZ hF)

end Cb
