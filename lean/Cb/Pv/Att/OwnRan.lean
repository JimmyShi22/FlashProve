-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/OwnRan.lean: on the last statement of a run of the chain of an attention sub-proof's own
rounds, at the value of Cb/Pv/Att/OwnSteps.lean, each output's public state is its claim's state.

Cb/Pv/Att/OwnLast.lean writes out what the chain owes at its end, at every last statement. There an
output's own public state o.st, at which its row and its end values' claims are read, is tied to
nothing. On the last statement that the chain's verifier puts out on a transcript given stage by
stage (c.run x ts, Cb/Pv/Att/ChainRun.lean) it is the state of that sumcheck's claim: the challenges
gathered from the statement as it has grown.

Main names:
  `u.Ran`: the eight equations: oM and oD have pub0 at the first statement and the units' further
    scalars so far; oE has pub0; oVM and oVD have pubV; oF has pubF; oK has pubD and the incoming
    form of the key's sumcheck; oH has pubH.
  `run_st`: the run inside c.run x ts has Ran (by definition). `run_x`: its first statement is x.
  `own_last_run`: so at c.run x ts the chain owes the list of own_last at a run with Ran.
  `u.Bill m`: that list without what rides (Dn). `own_last_bill`: own_last in these words.
  `own_owed`: what the stages claim on a run given stage by stage (`Ch.Owed`,
    Cb/Pv/Att/ChainLast.lean) is the Bill at the run inside c.run x ts.
  `step_end_at`: the claim on an end value of a step of the description, where the output's state is
    a known p: the extensions are the description's at the challenges p.
  `sD_eGap`: the gap of an end value of the key's sumcheck, in the description's scalars KC and IBP.

Limits: those of Cb/Pv/Att/OwnLast.lean. Nothing is discharged. That what the chain's verifier puts
out is the last statement of a run given stage by stage is not shown here: it is Ch.out_run in
Cb/Pv/Att/Ran.lean, where all picks of the chain are lawful. Nothing is said on an honest prover or
on hiding.
-/
import Cb.Pv.Att.OwnLast
import Cb.Pv.Att.ChainLast
import Cb.Pv.Att.Step18Ends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole Johnson.L5.Layers Inst.Model

namespace OwnPar
variable {E M X : Type} [Field E] [Fintype E] (P : OwnPar E M X) (Mn : Means E P.D P.C P.kap)

/-- The public state in each output is the state of that sumcheck's claim. -/
structure Run.Ran {P : OwnPar E M X} (u : P.Run) : Prop where
  oM : u.oM.st = P.pub0 (u.x, [])
  oD : u.oD.st = P.pub0 (u.x, [List.ofFn u.rM])
  oE : u.oE.st = P.pub0 u.y0
  oVM : u.oVM.st = P.pubV (u.yE, u.th)
  oVD : u.oVD.st = P.pubV (u.yE, u.th)
  oF : u.oF.st = P.pubF ((u.z, u.s), u.bF)
  oK : u.oK.st = (P.pubD (u.yF, u.bK),
    incAt (fun i => P.cAt .s16 (i, true)) fun i : Fin P.D.nb => u.bK ^ (i : ℕ) * P.sF.lstOf u.yF)
  oH : u.oH.st = P.pubH (u.yK, u.bH)

/-- On the last statement of a run that is given stage by stage. -/
theorem run_st (x : X) (ts : (P.own Mn).ch.Trs) :
    (P.runOf Mn ((P.own Mn).ch.run x ts)).Ran :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The first statement in the run inside the last statement of a run is the run's. -/
theorem run_x (x : X) (ts : (P.own Mn).ch.Trs) :
    (P.runOf Mn ((P.own Mn).ch.run x ts)).x = x :=
  ((P.back_endOf Mn _).symm.trans (congrArg _ (P.endOf_runOf Mn _))).trans
    (Ch.back_run (P.own Mn).ch x ts)

/-- What the chain owes at the end of a run: the list of own_last at the run inside the last
statement, whose outputs have the claims' states (run_st). -/
theorem own_last_run (Dn : X → M → Prop) (x : X) (ts : (P.own Mn).ch.Trs) (m : M) :
    (P.own Mn).ch.Last Dn ((P.own Mn).ch.run x ts) m ↔
      (P.own Mn).ch.Last Dn (P.endOf Mn (P.runOf Mn ((P.own Mn).ch.run x ts))) m :=
  P.own_last_at Mn Dn _ m

/-- The list of own_last without what rides: the free linear claims; the two linear claims that are
written out; the eight rows; the end values' claims. -/
def Run.Bill {P : OwnPar E M X} (u : P.Run) (m : M) : Prop :=
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
  ∀ a, P.sH.T.our.par.EHolds u.oH (P.msg m) a

theorem own_last_bill (Dn : X → M → Prop) (u : P.Run) (m : M) :
    (P.own Mn).ch.Last Dn (P.endOf Mn u) m ↔ Dn u.x m ∧ u.Bill m :=
  P.own_last Mn Dn u m

/-- What the stages of the chain claim on a run given stage by stage (Ch.Owed,
Cb/Pv/Att/ChainLast.lean) is the list at the run inside the last statement. -/
theorem own_owed (x : X) (ts : (P.own Mn).ch.Trs) (m : M) :
    (P.own Mn).ch.Owed x ts m ↔ (P.runOf Mn ((P.own Mn).ch.run x ts)).Bill m := by
  have h1 := Ch.last_run (P.own Mn).ch (fun _ _ => True) x ts m
  have h2 := (P.own_last_run Mn (fun _ _ => True) x ts m).trans
    (P.own_last_bill Mn (fun _ _ => True) _ m)
  exact ⟨fun h => (h2.1 (h1.2 ⟨trivial, h⟩)).2, fun h => (h1.1 (h2.2 ⟨trivial, h⟩)).2⟩

end OwnPar

/-! ### An end value's claim at a known state -/

section Ends
variable {E : Type} [Field E] [Fintype E] (D : AttSeg.Dim) (C : AttSeg.Calls) {J : Type}
  [Fintype J] (rd : (J → E) → AttSeg.Raw → E)

/-- The claim on an end value of step s, where the output's state is p: the description's own
extension of A_i or B_i at the challenges p. -/
theorem step_end_at (s : AttSeg.Step) (inc : AttSeg.Pub E → J → E)
    (wAt : PIdx (ldPartFmt E (s.g D) (fun _ => 3) ++ [pDummy E 2]) → J)
    (cAt : Fin D.nb × Bool → J) (o : (stepSc3 D C rd s inc wAt cAt).plain.our.par.Out)
    (m : J → E) (i : Fin D.nb) (b : Bool) (p : AttSeg.Pub E) (h : o.st = p) :
    (stepSc3 D C rd s inc wAt cAt).plain.our.par.EHolds o m (i, b) ↔
      (if b then AttSeg.Bext D C p (rd m) s i
          (Blocks.nat (ldPartFn (s.g D) (fun _ => 3) (stepSc3 D C rd s inc wAt cAt).plain.dat
            ((stepSc3 D C rd s inc wAt cAt).plain.our.ini o.st
              ((stepSc3 D C rd s inc wAt cAt).plain.our.par.hp o.st o.pt))))
        else AttSeg.Aext D C p (rd m) s i
          (Blocks.nat (ldPartFn (s.g D) (fun _ => 3) (stepSc3 D C rd s inc wAt cAt).plain.dat
            ((stepSc3 D C rd s inc wAt cAt).plain.our.ini o.st
              ((stepSc3 D C rd s inc wAt cAt).plain.our.par.hp o.st o.pt))))) +
        m (cAt (i, b)) * (stepSc3 D C rd s inc wAt cAt).plain.our.lst o.st
          ((stepSc3 D C rd s inc wAt cAt).plain.our.par.hp o.st o.pt) = o.vals (i, b) := by
  subst h
  exact step_end D C rd s inc wAt cAt o m i b

end Ends

namespace OwnPar
variable {E M X : Type} [Field E] [Fintype E] (P : OwnPar E M X)

/-- The gap of an end value of the key's sumcheck: the description's scalar KC or IBP (rv18,
Cb/Pv/Att/Step18Ends.lean) at the challenges in the output's state and at the point, plus the map's
mask entry times the further challenge, less the end value. -/
theorem sD_eGap (b : P.sD.Nx) (m : M) (a : (size18 P.D).A) :
    P.sD.eGap b m a =
      rv18 P.D b.2.st.1 (P.tOf m) (Blocks.nat (P.sD.ptOf b)) a +
        P.msg m (P.c18 a) * P.sD.lstOf b - b.2.vals a := by
  rw [SumL.eGap_eq]
  have e : P.sD.T.map b.2.st (P.sD.msg m) a (P.sD.ptOf b) =
      rv18 P.D b.2.st.1 (P.tOf m) (Blocks.nat (P.sD.ptOf b)) a := by
    cases a with
    | inl l => exact step18_KC P.D P.rd (fun _ _ => 0) P.w18 P.c18 b.2.st.1 (P.msg m) l _
    | inr x =>
      obtain ⟨i, t⟩ := x
      exact step18_IB P.D P.rd (fun _ _ => 0) P.w18 P.c18 b.2.st.1 (P.msg m) i t _
  rw [e]
  rfl

end OwnPar
end Cb.Pv.Att

#print axioms Cb.Pv.Att.OwnPar.run_st
#print axioms Cb.Pv.Att.OwnPar.run_x
#print axioms Cb.Pv.Att.OwnPar.own_last_run
#print axioms Cb.Pv.Att.OwnPar.own_owed
#print axioms Cb.Pv.Att.step_end_at
#print axioms Cb.Pv.Att.OwnPar.sD_eGap
