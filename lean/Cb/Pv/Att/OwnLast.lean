-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/OwnLast.lean: what the chain of an attention sub-proof's own rounds, at the value of
Cb/Pv/Att/OwnSteps.lean, owes at its end, written out by name.

Knowledge soundness of the chain (ownSteps_knowAt) ends at the claim `Ch.Last Dn` on the chain's
last statement: a claim that whoever follows must discharge. Here it is unfolded at the value.

Main names:
  `P.Run`: all that was sent, drawn and put out along the chain, by name: the first statement x; the
    further scalars rM, rD, rE, rV; the pairs' scalars s; the draws th, pt, bF, bK, bH; the eight
    outputs oM, oD, oE, oVM, oVD, oF, oK, oH. `u.y0`, `yE`, `yVM`, `yVD`, `z`, `yF`, `yK`, `yH`: the
    statements of the tail's stages, made of a run.
  `P.endOf Mn u`, `P.runOf Mn e`, `endOf_runOf`, `back_endOf`: a last statement is made of a run,
    and every last statement is made of its own run; the first statement inside it is x.
  `own_last_raw`: the claim as the definition gives it (by definition).
  `own_last`: the claim sorted. It holds exactly if all of these hold: Dn of the first statement;
    the three free linear claims LM, LD, LE; the two hidden sums of the value products add up to the
    hidden ACC plus th times the hidden ZC; the hidden value of each pair's scalar is the rule value
    `AttSeg.rvM6` at the point drawn; the row of each of the eight sumchecks (`UHolds`); the claim
    on every end value of seven sumchecks, and on the first end value of each pair of the score's
    sumcheck (`EHolds`). The claims on the second end values of the score's sumcheck are not owed at
    the end: they are what is claimed before the next draw, whose bad draws the chain's errors count
    (`TailG.laws`, Cb/Pv/Att/Gaps.lean).
  `own_last_at`: the same at any last statement, through its run.
  `step_end`: how to read the claim on an end value of a step of the description.

Limits: definitions unfolded and sorted: nothing is proved of a ledger, a table or a commitment, and
no claim of the list is discharged. An output carries a public state of its own (o.st), at which its
row and its end values' claims are read. On the output of a run that state is the claim's (shortV,
Cb/G6/Value.lean); of an arbitrary last statement nothing says so, and `own_last` speaks of every
last statement. Nothing is said on an honest prover or on hiding.
-/
import Cb.Pv.Att.OwnSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole Johnson.L5.Layers Inst.Model

namespace OwnPar
variable {E M X : Type} [Field E] [Fintype E] (P : OwnPar E M X) (Mn : Means E P.D P.C P.kap)

/-- All that was sent, drawn and put out along the chain, by name. -/
structure Run where
  x : X
  rM : Fin (3 * P.npl + 7) → E
  oM : P.uM.T.our.par.Out
  rD : Fin 7 → E
  oD : P.uD.T.our.par.Out
  rE : Fin (5 + P.D.lT + 2) → E
  oE : P.sE.T.our.par.Out
  th : E
  rV : Fin 2 → E
  oVM : P.sVM.T.our.par.Out
  oVD : P.sVD.T.our.par.Out
  pt : Fin (P.g1 + P.g2) → E
  s : Fin P.D.nb → E
  bF : E
  oF : P.sF.T.our.par.Out
  bK : E
  oK : P.sD.T.our.par.Out
  bH : E
  oH : P.sH.T.our.par.Out

namespace Run
variable {P} (u : P.Run)

/-- no further scalar -/
def r0 : Fin 0 → E := Fin.elim0

/-- The statements of the tail's stages. -/
def y0 : Seen E X := (u.x, [List.ofFn u.rM, List.ofFn u.rD])
def yE : P.sE.Nx := ((u.y0, u.rE), u.oE)
def yVM : P.sVM.Nx := (((u.yE, u.th), u.rV), u.oVM)
def yVD : P.sVD.Nx := ((u.yVM, r0), u.oVD)
def z : P.sVD.Nx × (Fin (P.g1 + P.g2) → E) := (u.yVD, u.pt)
def yF : P.sF.Nx := ((((u.z, u.s), u.bF), r0), u.oF)
def yK : P.sD.Nx := (((u.yF, u.bK), r0), u.oK)
def yH : P.sH.Nx := (((u.yK, u.bH), r0), u.oH)

end Run

/-- The chain's last statement made of a run. -/
def endOf (u : P.Run) : (P.own Mn).ch.End :=
  ((((((((((((((((((((((u.x, u.rM), u.oM), u.rD), u.oD), u.rE), u.oE), u.th), u.rV), u.oVM),
    Run.r0), u.oVD), u.pt), u.s), u.bF), Run.r0), u.oF), u.bK), Run.r0), u.oK), u.bH), Run.r0),
    u.oH)

theorem back_endOf (u : P.Run) : (P.own Mn).ch.back (P.endOf Mn u) = u.x := rfl

/-- The run inside a last statement. -/
def runOf (e : (P.own Mn).ch.End) : P.Run where
  x := e.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  rM := e.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  oM := e.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  rD := e.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  oD := e.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  rE := e.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  oE := e.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  th := e.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  rV := e.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  oVM := e.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  oVD := e.1.1.1.1.1.1.1.1.1.1.1.2
  pt := e.1.1.1.1.1.1.1.1.1.1.2
  s := e.1.1.1.1.1.1.1.1.1.2
  bF := e.1.1.1.1.1.1.1.1.2
  oF := e.1.1.1.1.1.1.2
  bK := e.1.1.1.1.1.2
  oK := e.1.1.1.2
  bH := e.1.1.2
  oH := e.2

/-- Every last statement is made of its run. -/
theorem endOf_runOf (e : (P.own Mn).ch.End) : P.endOf Mn (P.runOf Mn e) = e := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨x, rM⟩, oM⟩, rD⟩, oD⟩, rE⟩, oE⟩, th⟩, rV⟩, oVM⟩, a0⟩, oVD⟩, pt⟩,
    s⟩, bF⟩, a1⟩, oF⟩, bK⟩, a2⟩, oK⟩, bH⟩, a3⟩, oH⟩ := e
  obtain rfl : Run.r0 = a0 := Subsingleton.elim _ _
  obtain rfl : Run.r0 = a1 := Subsingleton.elim _ _
  obtain rfl : Run.r0 = a2 := Subsingleton.elim _ _
  obtain rfl : Run.r0 = a3 := Subsingleton.elim _ _
  rfl

/-- What the chain owes at its end, as the definition gives it. -/
theorem own_last_raw (Dn : X → M → Prop) (u : P.Run) (m : M) :
    (P.own Mn).ch.Last Dn (P.endOf Mn u) m ↔
      ((((((((Dn u.x m ∧ P.LM (u.x, []) u.rM m ∧ P.uM.T.our.par.OutHolds u.oM (P.msg m)) ∧
        P.LD (u.x, [List.ofFn u.rM]) u.rD m ∧ P.uD.T.our.par.OutHolds u.oD (P.msg m)) ∧
        P.LE u.y0 u.rE m ∧ P.sE.Out u.yE m) ∧
        P.sVM.L (u.yE, u.th) u.rV m ∧ P.sVM.Out u.yVM m) ∧
        True ∧ P.sVD.Out u.yVD m) ∧
        P.lF u.z u.s m) ∧
        True ∧ (P.sF.T.our.par.UHolds u.oF (P.msg m) ∧
          ∀ a, (∀ i, a ≠ P.iB i) → P.sF.T.our.par.EHolds u.oF (P.msg m) a)) ∧
        True ∧ P.sD.Out u.yK m) ∧
        True ∧ P.sH.Out u.yH m :=
  Iff.rfl

/-- The first end value of pair i of the score's sumcheck. -/
def iA (i : Fin P.D.nb) : P.sF.T.A := (i, false)

/-- What the chain owes at its end, sorted: what rides; the free linear claims; the two linear
claims that are written out; the eight rows; the end values' claims. -/
theorem own_last (Dn : X → M → Prop) (u : P.Run) (m : M) :
    (P.own Mn).ch.Last Dn (P.endOf Mn u) m ↔
      Dn u.x m ∧
      (P.LM (u.x, []) u.rM m ∧ P.LD (u.x, [List.ofFn u.rM]) u.rD m ∧ P.LE u.y0 u.rE m) ∧
      ((u.rV 0 - P.msg m (P.kV 0)) + (u.rV 1 - P.msg m (P.kV 1)) =
        (u.rE P.iACC - P.msg m (P.kE P.iACC)) + u.th * (u.rE P.iZC - P.msg m (P.kE P.iZC))) ∧
      (∀ i : Fin P.D.nb, u.s i - P.msg m (P.kF i) = AttSeg.rvM6 P.D (P.pubZ u.z) (P.tOf m) i) ∧
      (P.uM.T.our.par.UHolds u.oM (P.msg m) ∧ P.uD.T.our.par.UHolds u.oD (P.msg m) ∧
        P.sE.T.our.par.UHolds u.oE (P.msg m) ∧ P.sVM.T.our.par.UHolds u.oVM (P.msg m) ∧
        P.sVD.T.our.par.UHolds u.oVD (P.msg m) ∧ P.sF.T.our.par.UHolds u.oF (P.msg m) ∧
        P.sD.T.our.par.UHolds u.oK (P.msg m) ∧ P.sH.T.our.par.UHolds u.oH (P.msg m)) ∧
      (∀ a, P.uM.T.our.par.EHolds u.oM (P.msg m) a) ∧
      (∀ a, P.uD.T.our.par.EHolds u.oD (P.msg m) a) ∧
      (∀ a, P.sE.T.our.par.EHolds u.oE (P.msg m) a) ∧
      (∀ a, P.sVM.T.our.par.EHolds u.oVM (P.msg m) a) ∧
      (∀ a, P.sVD.T.our.par.EHolds u.oVD (P.msg m) a) ∧
      (∀ i, P.sF.T.our.par.EHolds u.oF (P.msg m) (P.iA i)) ∧
      (∀ a, P.sD.T.our.par.EHolds u.oK (P.msg m) a) ∧
      ∀ a, P.sH.T.our.par.EHolds u.oH (P.msg m) a := by
  rw [own_last_raw]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨hDn, hLM, hUM, hEM⟩, hLD, hUD, hED⟩, hLE, hUE, hEE⟩, hA, hUVM, hEVM⟩, -, hUVD,
      hEVD⟩, hlF⟩, -, hUF, hEF⟩, -, hUK, hEK⟩, -, hUH, hEH⟩
    exact ⟨hDn, ⟨hLM, hLD, hLE⟩, hA, hlF, ⟨hUM, hUD, hUE, hUVM, hUVD, hUF, hUK, hUH⟩, hEM, hED,
      hEE, hEVM, hEVD,
      fun i => hEF (P.iA i) fun _ h => Bool.false_ne_true (congrArg Prod.snd h), hEK, hEH⟩
  · rintro ⟨hDn, ⟨hLM, hLD, hLE⟩, hA, hlF, ⟨hUM, hUD, hUE, hUVM, hUVD, hUF, hUK, hUH⟩, hEM, hED,
      hEE, hEVM, hEVD, hEF, hEK, hEH⟩
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨hDn, hLM, hUM, hEM⟩, hLD, hUD, hED⟩, hLE, hUE, hEE⟩, hA, hUVM, hEVM⟩, trivial,
      hUVD, hEVD⟩, hlF⟩, trivial, hUF, fun a ha => ?_⟩, trivial, hUK, hEK⟩, trivial, hUH, hEH⟩
    obtain ⟨i, b⟩ := a
    cases b
    · exact hEF i
    · exact absurd rfl (ha i)

/-- The same at any last statement. -/
theorem own_last_at (Dn : X → M → Prop) (e : (P.own Mn).ch.End) (m : M) :
    (P.own Mn).ch.Last Dn e m ↔ (P.own Mn).ch.Last Dn (P.endOf Mn (P.runOf Mn e)) m := by
  rw [endOf_runOf]

end OwnPar

/-! ### How to read an end value's claim -/

section Ends
variable {E : Type} [Field E] [Fintype E] (D : AttSeg.Dim) (C : AttSeg.Calls) {J : Type}
  [Fintype J] (rd : (J → E) → AttSeg.Raw → E) (s : AttSeg.Step) (inc : AttSeg.Pub E → J → E)
  (wAt : PIdx (ldPartFmt E (s.g D) (fun _ => 3) ++ [pDummy E 2]) → J) (cAt : Fin D.nb × Bool → J)

/-- The claim on an end value of step s: the description's own extension of A_i or B_i, at the
challenges in the output's own state and at the point of the variables' challenges, plus the map's
mask entry times the further challenge, is the end value. -/
theorem step_end (o : (stepSc3 D C rd s inc wAt cAt).plain.our.par.Out) (m : J → E)
    (i : Fin D.nb) (b : Bool) :
    (stepSc3 D C rd s inc wAt cAt).plain.our.par.EHolds o m (i, b) ↔
      (if b then AttSeg.Bext D C o.st (rd m) s i
          (Blocks.nat (ldPartFn (s.g D) (fun _ => 3) (stepSc3 D C rd s inc wAt cAt).plain.dat
            ((stepSc3 D C rd s inc wAt cAt).plain.our.ini o.st
              ((stepSc3 D C rd s inc wAt cAt).plain.our.par.hp o.st o.pt))))
        else AttSeg.Aext D C o.st (rd m) s i
          (Blocks.nat (ldPartFn (s.g D) (fun _ => 3) (stepSc3 D C rd s inc wAt cAt).plain.dat
            ((stepSc3 D C rd s inc wAt cAt).plain.our.ini o.st
              ((stepSc3 D C rd s inc wAt cAt).plain.our.par.hp o.st o.pt))))) +
        m (cAt (i, b)) * (stepSc3 D C rd s inc wAt cAt).plain.our.lst o.st
          ((stepSc3 D C rd s inc wAt cAt).plain.our.par.hp o.st o.pt) = o.vals (i, b) :=
  plain_val (stepSc3 D C rd s inc wAt cAt).plain o m (i, b)

end Ends

end Cb.Pv.Att

#print axioms Cb.Pv.Att.OwnPar.endOf_runOf
#print axioms Cb.Pv.Att.OwnPar.own_last
#print axioms Cb.Pv.Att.step_end
