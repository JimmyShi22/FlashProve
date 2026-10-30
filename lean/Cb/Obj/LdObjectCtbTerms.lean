-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbTerms.lean: bookkeeping for the compiler to a random-oracle argument, for which it
is asked that the types of positions, symbols and plain messages of every round are countable: here
for the object whose two closings are parameters.

A definition, one theorem. Bookkeeping for the passage to one random oracle. Generic.
Cb/Obj/LdObjectCtbParts.lean has this for the object at the plan without a splitting (`LdObjP.CtbP`,
`ldObjP_ctb`). Here the same one level lower, at `LdObjT` (Cb/Obj/LdObjectTerms.lean), where the two
closings of the test for linear constraints are parameters (`Qt`; `cZ`): so that it serves every
plan.

Main names:
  `T.CtbT`: countably many instances; the shapes of weights-formedness's link (`T.Bw.link`, its
    chain as one `IOR.Link`); the symbols as sent of the families of the two tests and of the link
    (`T.K`); `plan`: all links of the offline closing `Qt` have countable shapes; the link's whole
    test (`T.Kc`); all links of the request; `cz`: all annotated links of the online closing `cZ`
    have countable shapes.
  `ldObjT_ctb`: `T.CtbT` ⇒ `Ctb T.obj.subs r` (Cond/ObjCtb.lean), for every record r.

Limits: this file does not say that `T.CtbT` holds of a given plan. On a protocol it has one kind of
conditional conclusion, countability (`ldObjT_ctb`); beyond it no statement of the file concludes
anything of a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectCtbParts

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

structure LdObjT.CtbT (T : LdObjT F E) : Prop where
  inst : Countable T.W.Cf.Xm
  wf   : CtbSh T.Bw.link.R.shape
  nW   : T.W.NW.CtbSy
  nU   : T.W.NU.CtbSy
  nO   : T.W.NO.CtbSy
  plan : T.Qt.c.Ctb
  nK   : T.K.N.CtbSy
  tK   : CtbSh T.Kc.T.R.shape
  req  : T.r.chain.Ctb
  nWB  : T.on.NW.CtbSy
  nUB  : T.on.NU.CtbSy
  nOB  : T.on.NO.CtbSy
  cz   : T.cZ.forget.CtbA

theorem ldObjT_ctb (T : LdObjT F E) (r : T.obj.Cf.conf.Rec) (c : T.CtbT) :
    TopC.Ctb T.obj.subs r := by
  refine ⟨c.inst, inferInstanceAs (Countable (T.W.Cf.Row → F)), ?_, ?_, ?_⟩
  · exact ctbSh_append (s := T.Bw.link.R.shape) c.wf
      (ldOCtb_lin T.W.O T.εf T.Sn T.Qt T.fq T.dT c.nW c.nU c.nO c.plan)
  · exact ldOCtb_link T.K T.on0K T.on1K T.Sl T.ε₀ T.ε₁ T.Kc T.dK₂ T.dK c.nK c.tK
  · exact ctbS_app (s := (T.r.chain.link (ldStartW E T.w₀)).R.shape)
      (ctbS_allLocal (chainCtb_link T.r.chain _ c.req))
      (ldOnT_ctb T.on.ol T.onB T.SnB T.qaB T.εfB T.N T.cZ T.dB T.dB₀ c.nWB c.nUB c.nOB c.cz)

end
end Cb
