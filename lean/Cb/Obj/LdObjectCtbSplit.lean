-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbSplit.lean: bookkeeping for the compiler to a random-oracle argument, for which it
is asked that the types of positions, symbols and plain messages of every round are countable: here
for the object (`LdObjP`, Cb/Obj/LdObjectPlan.lean), split along its five parts.

Definitions, theorems. Bookkeeping for the passage to one random oracle
(CompileK/ImplCountable.lean: `CtbSh`).
Cb/Obj/LdObjectCtbParts.lean requires 17 small clauses of the whole object (`P.CtbP`).
Cb/Obj/LdObjectParts.lean cuts the object into five parts. Here each part gets its own clauses, so
that each part's can be shown by itself:
  `A.CtbW`: weights-formedness: instances; the preamble's shape; the three families that the test
    after it sends.
  `Ln.CtbL`: the test at one instance: its two whole tests, what is left.
  `Lk.CtbK`: the link: its family, its whole test.
  `Rq.CtbR`: a request: every link (`IOR.Link`) of its chain.
  `Bt.CtbB`: the test at N instances: the three families, its two whole tests, what is left.

Main names:
  `ldParts_ctbP`: the five give `(ldParts ..).CtbP`.
  `pWf_ctbW`: gives `A.CtbW` for weights-formedness with the assembled lookups
    (`A.Bw.sub = K.sub`), from countably many instances and `Sig.CtbSy` of its four families.
  `stdLk_ctbK`: gives `Lk.CtbK` for the link with standard parts, if the code `Cf.C₀` and
    the type P of `D : StdLk Cf P` have a position (`Nonempty`), from "a native symbol has
    finitely many coordinates" (`LdCode.FinNS`) of the member's code `D.M.Cm`.





Notation: `CtbSh` (CompileK/ImplCountable.lean): says that positions, symbols and plain parts of
every round are countable; `Sig.CtbSy` (Cb/Obj/LdObjectCtb.lean): says that the symbols as sent of
every member are countable; `Chain.Ctb` (Cb/Obj/LdObjectCtb.lean): `CtbSh` of the shape of every
`IOR.Link` of the chain; `ChainA.CtbA` (Cb/Obj/LdObjectCtbParts.lean): `CtbS`
(CompileK/ImplCountable.lean) of the shape and annotation of every `IOR.LinkA` of the chain.

Limits: on a protocol this file has one kind of conclusion, countability (as in `ldParts_ctbP`,
under `A.CtbW`, `Ln.CtbL`, `Lk.CtbK`, `Rq.CtbR` and `Bt.CtbB`); beyond it no statement of the file
concludes anything of a protocol.












Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectCtbParts
import Cb.Obj.LdObjectCtbReq
import Cb.Obj.LdObjectCtbToy
import Cb.Obj.LdObjectPartLink
import Cb.Ld.LdWfToyPart

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

structure PWf.CtbW (A : PWf F E) : Prop where
  inst : Countable A.W.Cf.Xm
  wf   : CtbSh A.Bw.link.R.shape
  nW   : A.W.NW.CtbSy
  nU   : A.W.NU.CtbSy
  nO   : A.W.NO.CtbSy

structure PLin.CtbL {A : PWf F E} (Ln : PLin A) : Prop where
  t₁   : CtbSh Ln.TP.D₁.T.R.shape
  t₂   : CtbSh Ln.TP.D₂.T.R.shape
  rest : Ln.TP.Q'.c.Ctb

structure PLink.CtbK {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] (Lk : PLink Cf) : Prop where
  nK : Lk.K.N.CtbSy
  tK : CtbSh Lk.Kc.T.R.shape

def PReq.CtbR {Cf : LdCf F E} (Rq : PReq Cf) : Prop := Rq.r.chain.Ctb

structure PBat.CtbB {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] {on : LdOLd Cf} (Bt : PBat Cf on) :
    Prop where
  nW   : on.NW.CtbSy
  nU   : on.NU.CtbSy
  nO   : on.NO.CtbSy
  t₁   : CtbSh Bt.TB.D₁.T.R.shape
  t₂   : CtbSh Bt.TB.D₂.T.R.shape
  rest : Bt.cA'.CtbA

/-- The five parts give the whole. -/
theorem ldParts_ctbP (A : PWf F E) (Ln : PLin A) (Lk : PLink A.W.Cf) (Rq : PReq A.W.Cf)
    (Bt : PBat A.W.Cf Rq.on) (z0 : A.W.Cf.conf.PIdx) (r0 : Rq.on.S.Rnd)
    (dOff : A.W.O.left.AMsg) (dOn : Rq.on.ol.left.AMsg) (hA : A.CtbW) (hL : Ln.CtbL)
    (hK : Lk.CtbK) (hR : Rq.CtbR) (hB : Bt.CtbB) :
    (ldParts A Ln Lk Rq Bt z0 r0 dOff dOn).CtbP :=
  ⟨hA.inst, hA.wf, hA.nW, hA.nU, hA.nO, hL.t₁, hL.t₂, hL.rest, hK.nK, hK.tK, hR, hB.nW, hB.nU,
    hB.nO, hB.t₁, hB.t₂, hB.rest⟩

/-- a request whose moves are as Cb/Obj/LdObjectCtbReq.lean asks -/
theorem pReq_ctbR {Cf : LdCf F E} (Rq : PReq Cf) (h : Rq.r.Ctb) : Rq.CtbR := ctb_req Rq.r h

/-- weights-formedness with the assembled lookups -/
theorem pWf_ctbW (A : PWf F E) (K : A.W.P.Lks) (hB : A.Bw.sub = K.sub) (hX : Countable A.W.Cf.Xm)
    (hS : A.W.P.S.CtbSy) (hW : A.W.NW.CtbSy) (hU : A.W.NU.CtbSy) (hO : A.W.NO.CtbSy) : A.CtbW :=
  ⟨hX, ldWfCtb_lks A.Bw K hB hS, hW, hU, hO⟩

omit [Fintype F] in
/-- the link with standard parts -/
theorem stdLk_ctbK {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] {P : Type} [Fintype P] [Nonempty P]
    (D : StdLk Cf P) (L t ε₀ ε₁ : ℕ) (h : D.M.Cm.FinNS) : (D.part L t ε₀ ε₁).CtbK :=
  ⟨fun _ p => by
    haveI := h p
    exact inferInstanceAs (Countable (D.M.Cm.NS p → E)),
      ctb_base _ _ _ _ _ _ (finNS_grp _ fun _ => h)⟩

end

end Cb
