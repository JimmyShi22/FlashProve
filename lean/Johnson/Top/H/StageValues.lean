-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/StageValues.lean: the stages of a proximity test behind its first, as values of the
data of a test in which the joints of neighbours meet by type, and the conditions of the whole at
these values.

A stage is given in numbers (`Sg`, OnBytes/Slice/Stage.lean). The fold is the library's at
`Sg.par` (OnBytes/Slice/FoldPeel.lean), with the form that the block before hands on
(`SumPar.reform`). Its number of public weights on the fresh mask row is the length of a mask
row's message (`s.Z.l`), as the walk of OnBytes/Slice/ManyBlk.lean asks (`StepPub.n0`). The code
switch starts where that fold ends (`LdSwD`, Cb/Obj/LdObjectTower.lean); its new code, pad,
places, sample and coefficients are those of OnBytes/Slice/CsData.lean. The data of a test are
`TowR` (Cb/Pv/Tower/Test.lean). Definitions, statements and proofs.
Main names:
  `swOf hf sl`: the switch from the stage s to the stage s', behind the fold of s at the form sl.
  `reform_hypK`: the fold's conditions at `(s.par s.Z.l).reform sl`: they read no form.
  `swOf_hypK`, `swOf_reads`: the switch's conditions and what locality asks: they read no form.
  `stepMid hf sl e e' bC bZ rest`: a stage whose switch bears the next fold's mask, then the
    remainder.
  `stepLast hf sl e e' bC bZ rest`: a stage whose switch bears the last step's masking word.
  `lastAt hf sl e e' bC bZ`: the last step, at the joint at which that switch ends.
  `stepMid_hypK`, `stepLast_hypK`, `lastAt_hypK`, and the same with `_reads`: the conditions of
    the whole from those of the remainder, `Sg.Sized`, `InJ` and `CountsAt`
    (Johnson/Top/H/StageJ.lean).
Limits: the first stage of a test stands on a group of oracle messages and is not treated.
`CountsAt` is asked and not proved here. A leaf of a new tree is a position of the new stage: that
this is the program's layout is not shown, and no condition reads it. What
Johnson/Top/H/StageJ.lean says of the base field and of slots holds here too.

-/
import Cb.Pv.Tower.Test
import Johnson.Top.H.StageJ
import OnBytes.Slice.CsSmp
import OnBytes.Slice.CloseKnow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Cb.Pv.Tower

instance (s : Sg) : Nonempty s.Ps := ⟨⟨0, Nat.two_pow_pos _⟩⟩

variable {s s' : Sg} {St : Type}

/-- The switch from s to s', behind the fold of s at the form sl. -/
noncomputable def swOf (hf : CsFit s s') (sl : Slf GE St s.cIn.J) :
    LdSwD ((s.par s.Z.l).reform sl) s'.Ps where
  finAa := inferInstanceAs (Fintype s.cMid.Aa)
  Cnew := s'.cIn
  Qo := CsFree hf
  finQo := Fintype.ofFinite _
  decQo := Classical.decEq _
  place := csPlace hf
  Zo := csSample hf
  ts := s.t
  Zb := (Evader.powers GE (2 + 3 * s.t)).comap (csRowNo s)

/-- The fold's conditions read no form. -/
theorem reform_hypK (sl : Slf GE St s.cIn.J) (hs : s.Sized) {e bC bZ : ℕ} (hj : InJ s e)
    (hc : CountsAt s e bC bZ) :
    ((s.par s.Z.l).reform sl).HypK s.d e (fun _ => lstJ s e) (fun _ => bC) (fun _ => bZ)
      (fun _ => bZ) :=
  have h := foldNums_joh hs hj hc
  ⟨Sg.codesOK hs hj.1, ⟨h.list, h.mcaC, h.mcaS, h.mcaW⟩, Function.injective_id, le_rfl,
    fun j => hideW_deg s.h s.g s.Z.l j.val⟩

/-- The switch's conditions read no form. -/
theorem swOf_hypK (hf : CsFit s s') (sl : Slf GE St s.cIn.J) (e : ℕ) (hs : s.Sized)
    (hs' : s'.Sized) {e' : ℕ} (hj : InJ s' e') : ((swOf hf sl).D e).HypK e' (lstJ s' e') :=
  ⟨(Sg.fit_cMid hs).laws, listJ_of (Sg.fit_cIn hs') hj, csSample_ok hf,
    ok_powers_comap _ _ (csRowNo_inj s)⟩

theorem swOf_reads (hf : CsFit s s') (sl : Slf GE St s.cIn.J) (e : ℕ) (hs' : s'.Sized) :
    ((swOf hf sl).D e).Cout.Reads := (Sg.fit_cIn hs').laws.loc

/-- A stage whose switch bears the next fold's mask, then the remainder. -/
noncomputable def stepMid (hf : CsFit s s') (sl : Slf GE St s.cIn.J) (e e' bC bZ : ℕ)
    (rest : TowR (((swOf hf sl).D e).jOut e') (s'.par s'.Z.l).Cw.nat) :
    TowR (wholeJ (s.par s.Z.l) sl e) (s.par s.Z.l).Cw.nat :=
  TowR.step (s.par s.Z.l) sl e (1, 1) (swOf hf sl) (s'.par s'.Z.l).Cw s'.Ps (Sum.elim id id) id s.d
    (fun _ => lstJ s e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ) e' (lstJ s' e') rest

/-- A stage whose switch bears the last step's masking word, then the remainder. -/
noncomputable def stepLast (hf : CsFit s s') (sl : Slf GE St s.cIn.J) (e e' bC bZ : ℕ)
    (rest : TowR (((swOf hf sl).D e).jOut e') s'.cIn.nat) :
    TowR (wholeJ (s.par s.Z.l) sl e) (s.par s.Z.l).Cw.nat :=
  TowR.step (s.par s.Z.l) sl e (1, 1) (swOf hf sl) s'.cIn s'.Ps (Sum.elim id id) (Sum.elim id id)
    s.d (fun _ => lstJ s e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ) e' (lstJ s' e') rest

/-- The last step, at the joint at which the switch from s to s' ends. -/
noncomputable def lastAt (hf : CsFit s s') (sl : Slf GE St s.cIn.J) (e e' bC bZ : ℕ) :
    TowR (((swOf hf sl).D e).jOut e') s'.cIn.nat :=
  TowR.base (((swOf hf sl).D e).jOut e') s'.t (Sum.elim id id) s'.d (bC + bZ) (lstJ s' e')

theorem lastAt_hypK (hf : CsFit s s') (sl : Slf GE St s.cIn.J) (e : ℕ) (hs' : s'.Sized)
    {e' bC bZ : ℕ} (hj : InJ s' e') (hc : CountsAt s' e' bC bZ) :
    (lastAt hf sl e e' bC bZ).HypK :=
  have h := baseCodes_joh hs' hj hc
  LdJoint.BaseHypK.mk h.laws hj.1 h.mca h.list

theorem lastAt_reads (hf : CsFit s s') (sl : Slf GE St s.cIn.J) (e e' bC bZ : ℕ) :
    (lastAt hf sl e e' bC bZ).Reads := trivial

theorem stepMid_hypK (hf : CsFit s s') (sl : Slf GE St s.cIn.J) {e e' bC bZ : ℕ}
    (rest : TowR (((swOf hf sl).D e).jOut e') (s'.par s'.Z.l).Cw.nat) (hs : s.Sized)
    (hs' : s'.Sized)
    (hj : InJ s e) (hj' : InJ s' e') (hc : CountsAt s e bC bZ) (hr : rest.HypK) :
    (stepMid hf sl e e' bC bZ rest).HypK :=
  And.intro (reform_hypK sl hs hj hc) (And.intro (swOf_hypK hf sl e hs hs' hj') hr)

theorem stepLast_hypK (hf : CsFit s s') (sl : Slf GE St s.cIn.J) {e e' bC bZ : ℕ}
    (rest : TowR (((swOf hf sl).D e).jOut e') s'.cIn.nat) (hs : s.Sized) (hs' : s'.Sized)
    (hj : InJ s e) (hj' : InJ s' e') (hc : CountsAt s e bC bZ) (hr : rest.HypK) :
    (stepLast hf sl e e' bC bZ rest).HypK :=
  And.intro (reform_hypK sl hs hj hc) (And.intro (swOf_hypK hf sl e hs hs' hj') hr)

theorem stepMid_reads (hf : CsFit s s') (sl : Slf GE St s.cIn.J) (e e' bC bZ : ℕ)
    (rest : TowR (((swOf hf sl).D e).jOut e') (s'.par s'.Z.l).Cw.nat) (hs' : s'.Sized)
    (hr : rest.Reads) : (stepMid hf sl e e' bC bZ rest).Reads :=
  And.intro (swOf_reads hf sl e hs') hr

theorem stepLast_reads (hf : CsFit s s') (sl : Slf GE St s.cIn.J) (e e' bC bZ : ℕ)
    (rest : TowR (((swOf hf sl).D e).jOut e') s'.cIn.nat) (hs' : s'.Sized)
    (hr : rest.Reads) : (stepLast hf sl e e' bC bZ rest).Reads :=
  And.intro (swOf_reads hf sl e hs') hr

end Johnson.Top.H

#print axioms Johnson.Top.H.swOf_hypK
#print axioms Johnson.Top.H.stepMid_hypK
#print axioms Johnson.Top.H.lastAt_hypK
