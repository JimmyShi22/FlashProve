-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectThirdEnd.lean: this file is on the offline phase over one configuration (`LdCf`,
Cb/Obj/LdObjectConf.lean): it has the phase's data (`LdOffE`), the plan's three tests and the term
of weights-formedness with its honest side and its numbers.




In standard terms: the part of the proof system that is made once for an encoded index: an
interactive oracle proof for the claim that an encoded index is the encoding, with its record, of a
message that holds an index, and, for each further encoding, one for the claim that it holds the
same index.





Definitions.
The offline phase: the offline IOP = the preamble of weights-formedness, then the test for linear
constraints at one instance with its closing; and, for each further encoded index, the link with its
closing.

The analogue of Cb/Obj/LdObjectThird.lean (`LdOff3`), with weights-formedness given by an `LdWfE`
(Cb/Ld/LdWfEnd.lean).





`wf`: `Z.G.B.wf` (the lookups are the assembled lookup on the keys of the index).





Main names:
  `LdOffE F E`: the data of the three terms, and the distances; its field `ne`: `Fin Cf.C₀.n`
    non-empty.









































Notation: `dS`: a map to ℕ (`Z.Third p dS`, Cb/Ld/LdWfEndThird.lean, says `Dist (dS a)` of the code
of the oracle message a: distance `dS a` or more); `X`: an `LdRowsD` (the one test on what the
preamble left); `Kc`: of type `K.P.Cl` (`LdLkP.Cl`, Cb/Ld/LdLinkClose.lean: the closing); `dOff`: a
value of `A.O.left.AMsg` (the `d0` of `LinKnowR`, Hiop/RecSubs.lean).

Limits: the senders are values of which laws are asked (in `Z.Rest p`, `Sn.Third`, `Sl.Third`), not
terms with proved laws.
No instance of `LdOffE` is part of this library. No instance with parameters of a protocol is
given here.

This file says nothing on the online phase. It says nothing beyond a third of the distance. It
says nothing on the compiled argument. It says nothing on plans with a splitting, or on several
groups for the filed rows.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectThird
import Cb.Ld.LdWfEndThird
import Cb.Obj.LdObjectWfRest
import Cb.Obj.LdObjectThirdNil
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

/-- The offline phase: the data. -/
structure LdOffE (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Type 1 where
  /-- weights-formedness: all data; the distances of the oracle messages sent -/
  Z   : LdWfE F E
  [ne : Nonempty (Fin Z.W.Cf.C₀.n)]
  dS  : Z.W.P.S.O → ℕ
  /-- the test at one instance: its sendings with their distances; the plan; its first two tests
  (T's own "rest" is not used); the one test on what the preamble left -/
  Sn  : Z.W.O.toC.P.Snd
  dW  : Z.W.O.toC.P.NW.O → ℕ
  dU  : Z.W.O.toC.P.NU.O → ℕ
  dO  : Z.W.O.toC.P.NO.O → ℕ
  p   : LdLinPl Z.W.O.toC
  T   : LdLinPlT p
  X   : LdRowsD p.S₂ Z.W.O.toC.E₀ Z.W.O.toC.Wpa (p.rowsL (Z.W.rowsA Z.X.nAt))
  w₀  : (p.S₂.sub X.kp).Wit × Z.W.O.toC.Wpa
  dT  : Z.W.O.toC.P.W0
  dOff : Z.W.O.left.AMsg
  /-- the link -/
  K   : Z.W.Cf.LinkPar
  Sl  : K.P.Snd
  dN  : K.P.N.O → ℕ
  Kc  : K.P.Cl
  dK₂ : K.P.W2
  dK  : K.P.W0

attribute [instance] LdOffE.ne

namespace LdOffE
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (A : LdOffE F E)

abbrev Cf : LdCf F E := A.Z.W.Cf
abbrev O : LdOL F E := A.Z.W.O
abbrev nAt : A.Z.W.P.N → A.Z.W.P.S.Ent := A.Z.X.nAt

/-- the plan's three tests -/
@[reducible] def TT : LdLinPlT A.p := A.T.withRest (A.X.one A.Z.W.tgA A.w₀)

/-- `wf`, its honest side, its numbers. -/
def wf : IOR A.Cf.conf.Rec A.Cf.conf.E0 (A.O.left.Xl × A.Cf.conf.Rec) A.O.left.El :=
  A.Z.G.B.wf
def hWf : A.wf.Honest A.Cf.conf.PIdx (A.Cf.conf.PIdx × A.O.left.WAux) := A.Z.G.B.hWf
def nW : PreNums A.wf := A.Z.G.B.nums
end LdOffE

end Cb
