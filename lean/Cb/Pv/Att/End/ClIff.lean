-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/ClIff.lean: the ledger of an attention sub-proof's own rounds, pulled back, says what
the chain's bill says, no more and no less; and it holds at a filled run, if the join holds at the
scalars picked there.

Statements and proofs. att_bill (Cb/Pv/Att/End/ClRan.lean) is one direction. The other uses that
each part of the ledger is equivalent to its share of the bill.

Main names:
  bill_cl: u.Bill m gives the pull-backs of all claims of ownCl L Q u.
  att_bill_iff: the equivalence.
  cl_filled: at the filled run (Cb/Pv/Att/End/ClFill.lean) the pull-backs of all claims hold, if the
    join holds at the scalars picked. So the premises of att_last can be met together wherever Fits
    can be met and the join's letters are picked to fit.

Limits: those of Cb/Pv/Att/End/Cl.lean and Cb/Pv/Att/End/ClFill.lean.


-/
import Cb.Pv.Att.End.ClRan
import Cb.Pv.Att.End.ClFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open Iop Prob Cb IOR TWhole Cb.Sub Finset Blocks
open Inst.Model.AttSeg

section Own
variable {E M X : Type} [Field E] [Fintype E] {P : OwnPar E M X} {J₂ : Type} [Fintype J₂]
  [DecidableEq J₂] {L : EndLay P J₂} {Q : JoinLay P}

/-- The bill gives the pull-backs of all claims of the ledger. -/
theorem bill_cl (F : Fits L Q) (u : P.Run) (m : M) (h : u.Bill m) :
    ∀ f ∈ ownCl L Q u, (pullF (attA L u) f).Holds (P.msg m) := by
  obtain ⟨⟨hLM, hLD, hLE⟩, hline, hlF, ⟨uM, uD, uE, uVM, uVD, uF, uK, uH⟩, eM, eD, eE, eVM, eVD,
    eF, eK, eH⟩ := h
  obtain ⟨hLE1, hLE2⟩ := (F.LE _ _ _).mp hLE
  have ht : P.tOf m = rdOf L.cellJ (P.msg m) := F.rd (P.msg m)
  have lin : ∀ (name : ℕ → Option KSc) (_ : ∀ j k, name j = some k → LinK P.D k) {n : ℕ}
      (r : Fin n → E) (kk : Fin n → P.J) (x : Seen E X) (_ : x.1 = u.x)
      (_ : RuleAt P.D P.C name r kk (P.pub0 x) (P.tOf m) (P.msg m)),
      ∀ f ∈ linCl (J₁ := P.J) P.D P.C L.ls L.lmS L.Y name r kk (zT u),
        (pullF (attA L u) f).Holds (P.msg m) := by
    intro name hn n r kk x hx hr
    rw [ht] at hr
    have hz : (P.pub0 x).z = zT u := by
      show P.zOf x.1 = P.zOf u.x
      rw [hx]
    have := linCl_in L.cellJ P.D P.C L.ls L.lmS L.Y (attTb L u) (P.pub0 x) (P.msg m) F.ls F.lmS
      (by rw [hz]; exact linTabs F u) F.gLin name hn r kk hr
    rw [hz] at this
    exact this
  intro f hf
  simp only [ownCl, List.mem_append, List.mem_cons] at hf
  rcases hf with hf | hf | hf | hf | hf | hf | rfl | rfl | hf | hf | hf | hf | hf | hf
  · exact lin nameM (fun _ _ => nameM_lin P.D) u.rM P.kM _ rfl ((F.LM _ _ _).mp hLM) f hf
  · exact (out6b_iff P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s6b)
      (P.wAt .s6b) u.oM F.ls ⟨rfl, rfl⟩ F.g6b (P.msg m)).mpr ⟨uM, eM⟩ f hf
  · exact lin nameD (fun _ _ => nameD_lin P.D) u.rD P.kD _ rfl ((F.LD _ _ _).mp hLD) f hf
  · exact (out6d_iff P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s6d)
      (P.wAt .s6d) u.oD F.ls ⟨rfl, rfl⟩ F.g6d (P.msg m)).mpr ⟨uD, eD⟩ f hf
  · exact lin (nameE P.D) (fun _ _ => nameE_lin P.D) u.rE P.kE _ rfl hLE1 f hf
  · exact (out8_iff P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s8)
      (P.wAt .s8) u.oE F.ls ⟨rfl, rfl⟩ F.g8 (P.msg m)).mpr ⟨uE, eE⟩ f hf
  · refine (claim_pull (attA L u) _ (P.msg m)).mpr ?_
    rw [val_joinA, val_liftA]
    simp only [val_kfA, val_hidA]
    exact hLE2
  · refine (claim_pull (attA L u) _ (P.msg m)).mpr ?_
    rw [val_aSub, val_aAdd, val_aAdd, val_aSmul, val_hidF, val_hidF, val_hidF, val_hidF,
      sub_eq_zero]
    exact hline
  · exact (out11_iff P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s11)
      (P.wAt .s11) u.oVM F.ls (F.lmS .m1 trivial) ⟨rfl, rfl⟩ F.g11 (P.msg m)).mpr ⟨uVM, eVM⟩ f hf
  · exact (out12_iff P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s12)
      (P.wAt .s12) u.oVD F.ls (F.lmS .d1 trivial) ⟨rfl, rfl⟩ F.g12 (P.msg m)).mpr ⟨uVD, eVD⟩ f hf
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
    refine (m6_iff P.D L.ls L.lmS L.Y (attTb L u) L.cellJ (P.pubZ u.z) ⟨rfl⟩ F.gM i.val i.isLt
      (u.s i) (P.kF i) (P.msg m)).mpr ?_
    rw [← ht]
    exact hlF i
  · exact (score16_iff P.D P.C L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd _ (P.cAt .s16)
      (P.wAt .s16) u.oF F.ls ⟨rfl⟩ F.g16 (P.msg m)).mpr ⟨uF, eF⟩ f hf
  · exact (out18_iff P.D L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd (fun _ _ => 0) Prod.fst
      Prod.snd P.w18 P.c18 u.oK F.ls ⟨rfl, rfl⟩ F.g18 (P.msg m)).mpr ⟨uK, eK⟩ f hf
  · exact (outBits_iff P.D L.ls L.lmS L.Y (attTb L u) L.cellJ P.rd F.rd (fun _ _ => 0) P.kap
      F.kap P.cH P.wH u.oH ⟨rfl⟩ F.gH (P.msg m)).mpr ⟨uH, eH⟩ f hf

/-- The ledger's pull-back says what the bill says. -/
theorem att_bill_iff (Mn : Means E P.D P.C P.kap) (F : Fits L Q) (u : P.Run) (m : M) :
    (∀ f ∈ ownCl L Q u, (pullF (attA L u) f).Holds (P.msg m)) ↔ u.Bill m :=
  ⟨att_bill Mn F u m, bill_cl F u m⟩

/-- At the filled run the pull-backs of all claims hold, if the join holds at the scalars picked. -/
theorem cl_filled (F : Fits L Q) (u : P.Run) (m : M)
    (hJ : joinVal (Q.q u.x) (KF (scl := Q.scl) P.D P.C (P.pub0 (fill P u m).y0)
      (hidV P (fill P u m).y0 (fill P u m).rE m)) ((Q.ce u.x).val (P.msg m)) = 0) :
    ∀ f ∈ ownCl L Q (fill P u m), (pullF (attA L (fill P u m)) f).Holds (P.msg m) :=
  bill_cl F _ m (fill_bill Q F.LM F.LD F.LE u m hJ)

end Own

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.att_bill_iff
#print axioms Cb.Pv.Att.End.cl_filled
