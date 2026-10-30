-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/ClRan.lean: the ledger of an attention sub-proof's own rounds, pulled back, pays the
chain's bill; at a run that is given stage by stage it gives what the stages owe.

Statements and proofs, from att_last (Cb/Pv/Att/End/Cl.lean) and the bill as
Cb/Pv/Att/OwnRan.lean writes it.

Main names:
  att_bill: the pull-backs of the claims of ownCl L Q u give u.Bill m, at every u.
  att_owed: at the last statement of a run that is given stage by stage, they give Ch.Owed.
  tb_ran: at such a run the challenges that the tables' weights and the reading forms take from the
    outputs' public states are the true ones.
  att_hEnd_ran: the premise hEnd of sub_link_ran (Cb/Pv/Att/LinkRan.lean [not in this library]),
    with its three named premises at runs. att_hEnd_at: the same with the lift and the frame's share
    in the place of B₀.

Limits: those of Cb/Pv/Att/End/Cl.lean.


-/
import Cb.Pv.Att.End.Cl
import Cb.Pv.Att.OwnRan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open Iop Prob Cb IOR TWhole Cb.Sub Finset Blocks
open Inst.Model.AttSeg

section Own
variable {E M X : Type} [Field E] [Fintype E] {P : OwnPar E M X} {J₂ : Type} [Fintype J₂]
  [DecidableEq J₂] {L : EndLay P J₂} {Q : JoinLay P}

/-- The ledger's pull-back pays the chain's bill. -/
theorem att_bill (Mn : Means E P.D P.C P.kap) (F : Fits L Q) (u : P.Run) (m : M)
    (h : ∀ f ∈ ownCl L Q u, (pullF (attA L u) f).Holds (P.msg m)) : u.Bill m :=
  ((P.own_last_bill Mn (fun _ _ => True) u m).mp
    (att_last Mn F (fun _ _ => True) u m trivial h)).2

/-- At a run that is given stage by stage, the ledger's pull-back gives what the stages owe. -/
theorem att_owed (Mn : Means E P.D P.C P.kap) (F : Fits L Q) (x : X) (ts : (P.own Mn).ch.Trs)
    (m : M)
    (h : ∀ f ∈ ownCl L Q (P.runOf Mn ((P.own Mn).ch.run x ts)),
      (pullF (attA L (P.runOf Mn ((P.own Mn).ch.run x ts))) f).Holds (P.msg m)) :
    (P.own Mn).ch.Owed x ts m :=
  (P.own_owed Mn x ts m).mpr (att_bill Mn F _ m h)

/-- At a run whose outputs have their claims' states, the challenges that the tables' weights and
the reading forms take from the outputs' states are the true ones: the lookup's end point of the
first statement; the element drawn for the value products; the point of the score at the index. -/
theorem tb_ran (u : P.Run) (hu : u.Ran) :
    Pub.z u.oM.st = zT u ∧ Pub.z u.oD.st = zT u ∧ Pub.z u.oE.st = zT u ∧
      (Pub.z u.oVM.st = zT u ∧ Pub.th u.oVM.st = u.th) ∧
      (Pub.z u.oVD.st = zT u ∧ Pub.th u.oVD.st = u.th) ∧
      Prod.fst u.oK.st = P.pubD (u.yF, u.bK) := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hu.oM]
    rfl
  · rw [hu.oD]
    rfl
  · rw [hu.oE]
    rfl
  · rw [hu.oVM]
    rfl
  · rw [hu.oVM]
    rfl
  · rw [hu.oVD]
    rfl
  · rw [hu.oVD]
    rfl
  · rw [hu.oK]

/-- The premise hEnd of the link's statement at runs (sub_link_ran in Cb/Pv/Att/LinkRan.lean
[not in this library]), for a ledger cl whose pull-back, at the last statement of a run, gives the
pull-backs of the claims of the own rounds (hcl). hA0: B₀ gives what rides. hDn: B₀ and the ledger
give Dn. Of the three parts of the conclusion the third is proved here. -/
theorem att_hEnd_ran (Mn : Means E P.D P.C P.kap) (F : Fits L Q) {Kc X0 Wp : Type} {Ex : ExtSpec}
    (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0) (Dn : X → M → Prop)
    (B₀ : Rels Kc (P.own Mn).ch.End Ex (M × Wp))
    (cl : (P.own Mn).ch.End → TWhole.Ledger E (P.J ⊕ J₂))
    (hcl : ∀ x ts y w, A0.on (pr x, y) → B₀.relR ((P.own Mn).ch.run x ts, y) w →
      TWhole.Ledger.Holds (pullL (attA L (P.runOf Mn ((P.own Mn).ch.run x ts)))
        (cl ((P.own Mn).ch.run x ts))) (P.msg w.1) →
      ∀ f ∈ ownCl L Q (P.runOf Mn ((P.own Mn).ch.run x ts)),
        (pullF (attA L (P.runOf Mn ((P.own Mn).ch.run x ts))) f).Holds (P.msg w.1))
    (hA0 : ∀ x ts y w, A0.on (pr x, y) → B₀.relR ((P.own Mn).ch.run x ts, y) w →
      A0.relR (pr x, y) w)
    (hDn : ∀ x ts y w, A0.on (pr x, y) → B₀.relR ((P.own Mn).ch.run x ts, y) w →
      TWhole.Ledger.Holds (pullL (attA L (P.runOf Mn ((P.own Mn).ch.run x ts)))
        (cl ((P.own Mn).ch.run x ts))) (P.msg w.1) → Dn x w.1) :
    ∀ x ts y w, A0.on (pr x, y) → B₀.relR ((P.own Mn).ch.run x ts, y) w →
      TWhole.Ledger.Holds (pullL ((fun e => attA L (P.runOf Mn e)) ((P.own Mn).ch.run x ts))
        (cl ((P.own Mn).ch.run x ts))) (P.msg w.1) →
      A0.relR (pr x, y) w ∧ Dn x w.1 ∧ (P.own Mn).ch.Owed x ts w.1 :=
  fun x ts y w ho hB hL =>
    ⟨hA0 x ts y w ho hB, hDn x ts y w ho hB hL, att_owed Mn F x ts w.1 (hcl x ts y w ho hB hL)⟩

/-- The same in the form in which the link's statement at the written value of the own rounds asks
it: in the place of B₀ stand a statement Bs on the tuple of messages (there: the lift, Base (sym m))
and the frame's share Fr. -/
theorem att_hEnd_at (Mn : Means E P.D P.C P.kap) (F : Fits L Q) {Kc X0 Wp : Type} {Ex : ExtSpec}
    (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0) (Dn : X → M → Prop) (Bs : M → Prop)
    (Fr : Rels Kc (P.own Mn).ch.End Ex (M × Wp))
    (cl : (P.own Mn).ch.End → TWhole.Ledger E (P.J ⊕ J₂))
    (hcl : ∀ x ts y w, A0.on (pr x, y) → Bs w.1 → Fr.relR ((P.own Mn).ch.run x ts, y) w →
      TWhole.Ledger.Holds (pullL (attA L (P.runOf Mn ((P.own Mn).ch.run x ts)))
        (cl ((P.own Mn).ch.run x ts))) (P.msg w.1) →
      ∀ f ∈ ownCl L Q (P.runOf Mn ((P.own Mn).ch.run x ts)),
        (pullF (attA L (P.runOf Mn ((P.own Mn).ch.run x ts))) f).Holds (P.msg w.1))
    (hA0 : ∀ x ts y w, A0.on (pr x, y) → Bs w.1 → Fr.relR ((P.own Mn).ch.run x ts, y) w →
      A0.relR (pr x, y) w)
    (hDn : ∀ x ts y w, A0.on (pr x, y) → Bs w.1 → Fr.relR ((P.own Mn).ch.run x ts, y) w →
      TWhole.Ledger.Holds (pullL (attA L (P.runOf Mn ((P.own Mn).ch.run x ts)))
        (cl ((P.own Mn).ch.run x ts))) (P.msg w.1) → Dn x w.1) :
    ∀ x ts y w, A0.on (pr x, y) → Bs w.1 → Fr.relR ((P.own Mn).ch.run x ts, y) w →
      TWhole.Ledger.Holds (pullL ((fun e => attA L (P.runOf Mn e)) ((P.own Mn).ch.run x ts))
        (cl ((P.own Mn).ch.run x ts))) (P.msg w.1) →
      A0.relR (pr x, y) w ∧ Dn x w.1 ∧ (P.own Mn).ch.Owed x ts w.1 :=
  fun x ts y w ho hb hf hL =>
    ⟨hA0 x ts y w ho hb hf, hDn x ts y w ho hb hf hL,
      att_owed Mn F x ts w.1 (hcl x ts y w ho hb hf hL)⟩

end Own

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.att_bill
#print axioms Cb.Pv.Att.End.att_owed
#print axioms Cb.Pv.Att.End.att_hEnd_ran
#print axioms Cb.Pv.Att.End.att_hEnd_at
