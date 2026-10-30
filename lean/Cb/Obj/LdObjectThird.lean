-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectThird.lean: the offline phase over one configuration (`LdCf`,
Cb/Obj/LdObjectConf.lean): its data (`LdOff3`) and three terms, and a test on a group within a
third of the distances (`D.In3`).


In standard terms: the part of the proof system that is made once for an encoded index: an
interactive oracle proof for the claim that an encoded index is the encoding, with its record, of a
message that holds an index, and, for each further encoding, one for the claim that it holds the
same index. Within a third of the minimum distances, for codes that have their laws, lists have
at most one member and mutual correlated agreement is a theorem.



Definitions and statements; the proofs are in Cb/Obj/LdObjectThirdProofs.lean.
Cb/Obj/LdObjectThirdEnd.lean has the like data (`LdOffE`). This file has `D.In3` and `LdOff3`.


The offline phase: the offline IOP = the preamble of weights-formedness, then the test for linear
constraints at one instance with its closing; and, for each further encoded index, the link with its
closing.
Lists: `LdCode.ListAt`; agreement: `LdCode.MCAat` (both in Cb/Ld/LdRel.lean).
The three terms: wf: Cb/Ld/LdWfFull.lean (`G.B.wf`: the lookups are the assembled lookup on the keys
of the index); lin: Cb/Obj/LdObjectLinFull.lean (`O.full`) at the plan without a splitting
(Cb/Ld/LdLinClosePlan.lean): a test on the group with G_u and Ω, a test on the group with Ω and W
(the oracle messages G_u, Ω, W of the test: Cb/Ld/LdLin.lean), then one test on all that the
preamble left, which takes the rows that the lookups filed (Cb/Obj/LdObjectWfRows.lean); link:
Cb/Obj/LdObjectLinkFull.lean (`K.full`).

Main names:
  `D.In3`: a test on a group within a third: its whole test is a tower all of whose radii lie within
    a third of the distances (Cb/Obj/LdObjectTowerThird.lean: any number of stages; the base case
    alone is one), it needs what that tower needs, its bound for the list is 1; the group is within
    a third (Cb/Obj/LdObjectThirdTests.lean); the bridge's evader evades. `Spec.ldIn3_ok`: then
    `D.OK`.
  `LdOff3 F E`: the data of the three terms, and the distances; its field `ne`: `Fin Cf.C₀.n`
    non-empty.































Limits: declared, as in Cb/Obj/LdObjectThirdTests.lean: the fold of the index keeps the summand v
q^(v-1) for the one member of the list; the link takes both encoded indices by the first regime
(no collision; radius at most eM). Both on the safe side.

This file gives no instance of `LdOff3`; no instance of `LdOffE` (Cb/Obj/LdObjectThirdEnd.lean)
is part of this library.


This file says nothing on the online phase. It says nothing beyond a third of the distance. It
says nothing on the compiled argument.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecMainProof
import Cb.Obj.LdObjectThirdErr
import Cb.Obj.LdObjectTowerThird
import Cb.Ld.LdWfThird
import Cb.Obj.LdObjectWfRowsProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

/-- A test on a group within a third of the distances. -/
def LdRunD.In3 {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) : Prop :=
  ∃ (Tw : LdTowG3 D.G D.Sb D.sl D.Z) (d : ℕ),
    D.T = Tw.toG.toEnd ∧ D.t = Tw.toG.q ∧ D.L = 1 ∧ D.G.Third d ∧ D.Z.OK ∧ Tw.Third

/-- The offline phase: the data. -/
structure LdOff3 (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Type 1 where
  /-- weights-formedness with its lookups as values; the layout of the sender's coins; distances of
  the oracle messages sent; the places of the named entries -/
  G   : LdWfF F E
  [ne : Nonempty (Fin G.W.Cf.C₀.n)]
  Y   : G.B.MaskLay
  dS  : G.W.P.S.O → ℕ
  nAt : G.W.P.N → G.W.P.S.Ent
  /-- the test at one instance: its sendings with their distances; the plan; its first two tests
  (T's own "rest" is not used); the one test on what the preamble left -/
  Sn  : G.W.O.toC.P.Snd
  dW  : G.W.O.toC.P.NW.O → ℕ
  dU  : G.W.O.toC.P.NU.O → ℕ
  dO  : G.W.O.toC.P.NO.O → ℕ
  p   : LdLinPl G.W.O.toC
  T   : LdLinPlT p
  X   : LdRowsD p.S₂ G.W.O.toC.E₀ G.W.O.toC.Wpa (p.rowsL (G.W.rowsA nAt))
  w₀  : (p.S₂.sub X.kp).Wit × G.W.O.toC.Wpa
  dT  : G.W.O.toC.P.W0
  dOff : G.W.O.left.AMsg
  /-- the link -/
  K   : G.W.Cf.LinkPar
  Sl  : K.P.Snd
  dN  : K.P.N.O → ℕ
  Kc  : K.P.Cl
  dK₂ : K.P.W2
  dK  : K.P.W0

attribute [instance] LdOff3.ne

namespace LdOff3
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (A : LdOff3 F E)

abbrev Cf : LdCf F E := A.G.W.Cf
abbrev O : LdOL F E := A.G.W.O

/-- the plan's three tests -/
@[reducible] def TT : LdLinPlT A.p := A.T.withRest (A.X.one A.G.W.tgA A.w₀)

/-- The three terms, their honest sides, their numbers. -/
def wf : IOR A.Cf.conf.Rec A.Cf.conf.E0 (A.O.left.Xl × A.Cf.conf.Rec) A.O.left.El :=
  A.G.B.wf
def hWf : A.wf.Honest A.Cf.conf.PIdx (A.Cf.conf.PIdx × A.O.left.WAux) := A.G.B.hWf
def nW : PreNums A.wf := A.G.B.nums
def lin : IOR (A.O.left.Xl × A.Cf.conf.Rec) A.O.left.El Unit extNone :=
  A.O.full A.Sn (A.Cf.εThird A.O.e') A.TT.Q A.TT.fq A.dT
def hLin : A.lin.Honest (A.Cf.conf.PIdx × A.O.left.WAux) Unit :=
  A.O.hFull A.Sn (A.Cf.εThird A.O.e') A.TT.Q A.TT.fq A.dT
def nL : LinNumsR A.lin.shape :=
  A.O.numsF A.Sn (A.Cf.εThird A.O.e') A.TT.Q A.TT.fq A.dT
def tl : A.K.Tail :=
  A.K.full A.Sl (A.Cf.εThird A.K.e₀) (A.Cf.εThird A.K.e₁) A.Kc A.dK₂ A.dK

end LdOff3

namespace Spec

/-- A test on a group within a third meets its conditions (`LdRunD.OK`). -/
def ldIn3_ok : Prop := ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S), D.In3 → D.OK

end Spec
end Cb
