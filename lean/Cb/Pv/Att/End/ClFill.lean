-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/ClFill.lean: a run of the chain of an attention sub-proof's own rounds can be filled
so that the chain's bill is paid.

Definitions, statements and proofs. The bill (u.Bill m in Cb/Pv/Att/OwnRan.lean) asks of a run u and
a tuple m of messages: linear claims on the scalars sent, and the output claims of the eight
sumchecks. It does not ask that a sum claim holds. So for every m, and whatever was drawn, the
scalars sent, the end values shown and the last values can be picked so that the bill is paid, but
for the join, which is one equation more on the scalars picked. This file picks them. It serves as a
witness that the premises of att_last (Cb/Pv/Att/End/Cl.lean) can be met together.

Main names:
  fillOut T o m: the output statement o with its end values and its last value picked anew;
    fillOut_holds: all output claims hold of it and m.
  ruleFill name kk p t m: sent scalars whose hidden values are the rule values of their names, and 0
    where there is no name; ruleFill_rule.
  fill P u m: the run u with all that is sent or shown picked anew; what was drawn, the public
    states and the points stay.
  fill_bill: the bill is paid at fill P u m, if the three free linear claims of P are those of
    Cb/Pv/Att/End/Hid.lean and the join holds at the scalars picked.

Limits: a filled run is no honest run: no sum claim is looked at. Nothing on an honest prover or on
hiding.


-/
import Cb.Pv.Att.End.Hid
import Cb.Pv.Att.OwnRan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open Cb Finset
open Inst.Model Inst.Model.AttSeg

variable {E : Type} [Field E] [Fintype E]

/-! ### An output statement, filled -/

/-- The end values and the last value picked so that the output claims hold. -/
noncomputable def fillOut (Y : PscPar E) (o : Y.Out) (m : Y.J → E) : Y.Out where
  st := o.st
  eps := o.eps
  pt := o.pt
  vals := fun a => Y.G o.st m a (Y.hp o.st o.pt)
  fin := hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt) +
      o.eps * hPsi (Y.vars o.st) (Y.hp o.st o.pt) * Y.inc o.st m +
      o.eps * ∑ b, Y.S1 o.st (Y.hp o.st o.pt) (fun a => Y.G o.st m a (Y.hp o.st o.pt)) b *
        Y.Gb o.st m b (Y.hp o.st o.pt) +
    o.eps * Y.S0 o.st (Y.hp o.st o.pt) fun a => Y.G o.st m a (Y.hp o.st o.pt)

omit [Fintype E] in
theorem fillOut_holds (Y : PscPar E) (o : Y.Out) (m : Y.J → E) :
    Y.OutHolds (fillOut Y o m) m :=
  ⟨(add_sub_cancel_right _ _).symm, fun _ => rfl⟩

/-! ### Sent scalars, filled -/

/-- Sent scalars whose hidden values are the rule values of their names. -/
def ruleFill {J : Type} (D : Dim) (C : Calls) (name : ℕ → Option KSc) {n : ℕ} (kk : Fin n → J)
    (p : Pub E) (t : Raw → E) (m : J → E) (j : Fin n) : E :=
  (match name j.val with
    | some k => rv D C p t k
    | none => 0) + m (kk j)

omit [Fintype E] in
theorem ruleFill_rule {J : Type} (D : Dim) (C : Calls) (name : ℕ → Option KSc) {n : ℕ}
    (kk : Fin n → J) (p : Pub E) (t : Raw → E) (m : J → E) :
    RuleAt D C name (ruleFill D C name kk p t m) kk p t m := by
  intro j k hk
  unfold ruleFill
  rw [hk]
  exact add_sub_cancel_right _ _

section Own
variable {M X : Type} (P : OwnPar E M X)

/-- The run u with all that is sent or shown picked anew for the messages m. -/
noncomputable def fill (u : P.Run) (m : M) : P.Run where
  x := u.x
  rM := ruleFill P.D P.C nameM P.kM (P.pub0 (u.x, [])) (P.tOf m) (P.msg m)
  oM := fillOut _ u.oM (P.msg m)
  rD := ruleFill P.D P.C nameD P.kD (P.pub0 (u.x, [])) (P.tOf m) (P.msg m)
  oD := fillOut _ u.oD (P.msg m)
  rE := ruleFill P.D P.C (nameE P.D) P.kE (P.pub0 (u.x, [])) (P.tOf m) (P.msg m)
  oE := fillOut _ u.oE (P.msg m)
  th := u.th
  rV := fun i => if i = 0 then
      u.th * rv P.D P.C (P.pub0 (u.x, [])) (P.tOf m) .zc + P.msg m (P.kV 0)
    else P.msg m (P.kV 1)
  oVM := fillOut _ u.oVM (P.msg m)
  oVD := fillOut _ u.oVD (P.msg m)
  pt := u.pt
  s := fun i => rvM6 P.D (P.pubZ u.z) (P.tOf m) i + P.msg m (P.kF i)
  bF := u.bF
  oF := fillOut _ u.oF (P.msg m)
  bK := u.bK
  oK := fillOut _ u.oK (P.msg m)
  bH := u.bH
  oH := fillOut _ u.oH (P.msg m)

variable {P}

/-- The bill is paid at the filled run, if the join holds at the scalars picked. -/
theorem fill_bill (Q : JoinLay P) (hLM : ∀ x r m, P.LM x r m ↔ LMat P x r m)
    (hLD : ∀ x r m, P.LD x r m ↔ LDat P x r m) (hLE : ∀ x r m, P.LE x r m ↔ LEat P Q x r m)
    (u : P.Run) (m : M)
    (hJ : joinVal (Q.q u.x) (KF (scl := Q.scl) P.D P.C (P.pub0 (fill P u m).y0)
      (hidV P (fill P u m).y0 (fill P u m).rE m)) ((Q.ce u.x).val (P.msg m)) = 0) :
    (fill P u m).Bill m := by
  have rE := ruleFill_rule P.D P.C (nameE P.D) P.kE (P.pub0 (u.x, [])) (P.tOf m) (P.msg m)
  have hA : (fill P u m).rE P.iACC - P.msg m (P.kE P.iACC) = 0 := by
    show ruleFill P.D P.C (nameE P.D) P.kE (P.pub0 (u.x, [])) (P.tOf m) (P.msg m) P.iACC - _ = 0
    simp [ruleFill, nameE, OwnPar.iACC]
  have hC : (fill P u m).rE P.iZC - P.msg m (P.kE P.iZC) =
      rv P.D P.C (P.pub0 (u.x, [])) (P.tOf m) .zc := rE P.iZC .zc (by simp [nameE, OwnPar.iZC])
  refine ⟨⟨(hLM _ _ _).mpr (ruleFill_rule P.D P.C nameM P.kM _ _ _),
    (hLD _ _ _).mpr (ruleFill_rule P.D P.C nameD P.kD _ _ _), (hLE _ _ _).mpr ⟨rE, hJ⟩⟩, ?_,
    fun i => add_sub_cancel_right _ _,
    ⟨(fillOut_holds _ u.oM _).1, (fillOut_holds _ u.oD _).1, (fillOut_holds _ u.oE _).1,
      (fillOut_holds _ u.oVM _).1, (fillOut_holds _ u.oVD _).1, (fillOut_holds _ u.oF _).1,
      (fillOut_holds _ u.oK _).1, (fillOut_holds _ u.oH _).1⟩,
    (fillOut_holds _ u.oM _).2, (fillOut_holds _ u.oD _).2, (fillOut_holds _ u.oE _).2,
    (fillOut_holds _ u.oVM _).2, (fillOut_holds _ u.oVD _).2,
    fun i => (fillOut_holds _ u.oF _).2 _, (fillOut_holds _ u.oK _).2,
    (fillOut_holds _ u.oH _).2⟩
  rw [hA, hC]
  show (u.th * rv P.D P.C (P.pub0 (u.x, [])) (P.tOf m) .zc + P.msg m (P.kV 0) -
      P.msg m (P.kV 0)) + (P.msg m (P.kV 1) - P.msg m (P.kV 1)) =
    0 + u.th * rv P.D P.C (P.pub0 (u.x, [])) (P.tOf m) .zc
  ring

end Own

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.fillOut_holds
#print axioms Cb.Pv.Att.End.fill_bill
