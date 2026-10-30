-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/FirstOut.lean: the ledgers of the first four sumchecks of an attention sub-proof,
pulled back, give the blocks' output claims.

Statements and proofs. For the steps s6b, s6d, s8 and s11 at the parameters of Cb/Pv/Att/Steps.lean:
the ledger of the step (plainCl in Cb/Pv/Att/End/Step.lean) with the reading forms of
Cb/Pv/Att/End/First.lean, at the challenges and the point of the output statement o.

Main names:
  ptN T o: the point of an output statement, with coordinates numbered by ℕ.
  Tabs6b, Tabs6d, Tabs8, Tabs11: what the weights of a step's two tables are, from the challenges p
    and the step's point ξ.
  Good6b, Good6d, Good8, Good11: the names that a step's forms read are names of late entries.
  out6b_iff, out6d_iff, out8_iff, out11_iff: the pull-backs of all claims of the step's ledger hold
    of m exactly if all output claims of the block hold of m. out6b, out6d, out8, out11: the first
    direction.

The reading rd of the cells off the entries is a letter, as in Cb/Pv/Att/Steps.lean; the theorems
ask that it reads the entries at the places cellJ.

Limits: those of Cb/Pv/Att/End/Tabs.lean and Cb/Pv/Att/End/Step.lean.


-/
import Cb.Pv.Att.End.First
import Cb.Pv.Att.End.Dec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E] [Fintype E] {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
  [DecidableEq J₁] [DecidableEq J₂]

/-- The point of an output statement, with coordinates numbered by ℕ. -/
noncomputable def ptN (T : PlainSc E) (o : T.our.par.Out) : ℕ → E := Blocks.nat (pointAt T o)

variable (D : Dim) (C : Calls) (ls lmS : ℕ) (Y : LateLay AttTab J₂) (tb : AttTab → TabW E)

/-! ### What is asked of tables and names -/

structure Tabs8 (p : Pub E) (ξ : ℕ → E) : Prop where
  hE : tb .hE = .row (eqT D (sh ξ D.lg))
  qO : tb .qO = .long (eqN ls (D.ln - ls) (yn D C p.z)) (eqT D (sh ξ D.lg))

structure Good8 : Prop where
  hE : ∀ b < D.nb, ∀ g < D.nG, ∀ k < 4, Y.good (.hE, .den k b g 0)
  qO : ∀ b < D.nb, ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
    Y.good (.qO, (Raw.out k b g 0 0).addN (ch * 2 ^ ls))

structure Tabs6d (p : Pub E) (ξ : ℕ → E) : Prop where
  tQ : tb .tQd = .long (eqN ls (D.ln - ls) (sh ξ (D.lg + (D.lP + 1))))
    (psiDiag D (sh ξ D.lg) (zi' D C p.z))
  tK : tb .tKd = .long (eqN ls (D.ln - ls) (sh ξ (D.lg + (D.lP + 1))))
    (psiDiag D (sh ξ D.lg) (zj' D C p.z))

structure Good6d : Prop where
  tQ : ∀ b < D.nb, ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
    Y.good (.tQd, (Raw.qry k b g 0 0).addN (ch * 2 ^ ls))
  tK : ∀ b < D.nb, ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
    Y.good (.tKd, (Raw.key k (D.lamOf b) g 0 0).addN (ch * 2 ^ ls))

structure Tabs6b (p : Pub E) (ξ : ℕ → E) : Prop where
  tQ : tb .tQm = .long (eqN ls (D.ln - ls) (sh ξ (D.lg + D.lP + (D.lP + 1))))
    (psiRow D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) (zi' D C p.z))
  tK : tb .tKm = .long (eqN ls (D.ln - ls) (sh ξ (D.lg + D.lP + (D.lP + 1))))
    (psiCol D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) (zj' D C p.z))

structure Good6b : Prop where
  tQ : ∀ b < D.nb, ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
    Y.good (.tQm, (Raw.qry k b g 0 0).addN (ch * 2 ^ ls))
  tK : ∀ b < D.nb, ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
    Y.good (.tKm, (Raw.key k (D.lamOf b) g 0 0).addN (ch * 2 ^ ls))

structure Tabs11 (p : Pub E) (ξ : ℕ → E) : Prop where
  tVM : tb .tVM = .col (eqN lmS (D.lM - lmS) (ptBelow D C p ξ))
  qVM : tb .qVM = .long (eqN ls (D.ln - ls) (yn D C p.z))
    (psiCol D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) (sh ξ (D.lg + D.lP + (D.lP + 1))))

structure Good11 : Prop where
  tVM : ∀ b < D.nb, ∀ jj < 5, ∀ hi < 2 ^ (D.lM - lmS),
    Y.good (.tVM, (Raw.c .M jj b 0).addX (hi * 2 ^ lmS))
  qVM : ∀ b < D.nb, ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
    Y.good (.qVM, (Raw.val k (D.lamOf b) g 0 0).addN (ch * 2 ^ ls))

/-! ### The four steps -/

variable (cellJ : Raw → J₁) (rd : (J₁ → E) → Raw → E) (hrd : ∀ m, rd m = rdOf cellJ m)
  (inc : Pub E → J₁ → E) (cAt : Fin D.nb × Bool → J₁)
include hrd

/-- The denominator times the output. -/
theorem out8_iff (wAt : PIdx (ldPartFmt E (Step.s8.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s8 inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hT : Tabs8 D C ls tb o.st (ptN _ o)) (hG : Good8 D ls Y) (m : J₁ → E) :
    (∀ f ∈ plainCl (stepSc3 D C rd .s8 inc wAt cAt).plain o (pairs D.nb)
        (pick (rA8 D Y (ptN _ o)) (rB8 D C ls Y o.st (ptN _ o))),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) ↔
      (stepSc3 D C rd .s8 inc wAt cAt).plain.our.par.OutHolds o m :=
  stepCl_iff (stepSc3 D C rd .s8 inc wAt cAt) _ o _ _ m
    (fun b => by
      show _ = Aext D C o.st (rd m) .s8 b.val (ptN _ o)
      rw [hrd m]
      exact rA8_val cellJ D C ls lmS Y tb o.st _ m hT.hE b.val (hG.hE b.val b.isLt))
    (fun b => by
      show _ = Bext D C o.st (rd m) .s8 b.val (ptN _ o)
      rw [hrd m]
      exact rB8_val cellJ D C ls lmS Y tb o.st _ m hls hT.qO b.val (hG.qO b.val b.isLt))

theorem out8 (wAt : PIdx (ldPartFmt E (Step.s8.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s8 inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hT : Tabs8 D C ls tb o.st (ptN _ o)) (hG : Good8 D ls Y) (m : J₁ → E)
    (h : ∀ f ∈ plainCl (stepSc3 D C rd .s8 inc wAt cAt).plain o (pairs D.nb)
        (pick (rA8 D Y (ptN _ o)) (rB8 D C ls Y o.st (ptN _ o))),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) :
    (stepSc3 D C rd .s8 inc wAt cAt).plain.our.par.OutHolds o m :=
  (out8_iff D C ls lmS Y tb cellJ rd hrd inc cAt wAt o hls hT hG m).mp h

/-- The scores of the unit on the diagonal. -/
theorem out6d_iff (wAt : PIdx (ldPartFmt E (Step.s6d.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s6d inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hT : Tabs6d D C ls tb o.st (ptN _ o)) (hG : Good6d D ls Y) (m : J₁ → E) :
    (∀ f ∈ plainCl (stepSc3 D C rd .s6d inc wAt cAt).plain o (pairs D.nb)
        (pick (rA6d D ls Y (ptN _ o)) (rB6d D ls Y (ptN _ o))),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) ↔
      (stepSc3 D C rd .s6d inc wAt cAt).plain.our.par.OutHolds o m :=
  stepCl_iff (stepSc3 D C rd .s6d inc wAt cAt) _ o _ _ m
    (fun b => by
      show _ = Aext D C o.st (rd m) .s6d b.val (ptN _ o)
      rw [hrd m]
      exact rA6d_val cellJ D C ls lmS Y tb o.st _ m hls hT.tQ b.val (hG.tQ b.val b.isLt))
    (fun b => by
      show _ = Bext D C o.st (rd m) .s6d b.val (ptN _ o)
      rw [hrd m]
      exact rB6d_val cellJ D C ls lmS Y tb o.st _ m hls hT.tK b.val (hG.tK b.val b.isLt))

theorem out6d (wAt : PIdx (ldPartFmt E (Step.s6d.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s6d inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hT : Tabs6d D C ls tb o.st (ptN _ o)) (hG : Good6d D ls Y) (m : J₁ → E)
    (h : ∀ f ∈ plainCl (stepSc3 D C rd .s6d inc wAt cAt).plain o (pairs D.nb)
        (pick (rA6d D ls Y (ptN _ o)) (rB6d D ls Y (ptN _ o))),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) :
    (stepSc3 D C rd .s6d inc wAt cAt).plain.our.par.OutHolds o m :=
  (out6d_iff D C ls lmS Y tb cellJ rd hrd inc cAt wAt o hls hT hG m).mp h

/-- The scores of the unit below the diagonal. -/
theorem out6b_iff (wAt : PIdx (ldPartFmt E (Step.s6b.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s6b inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hT : Tabs6b D C ls tb o.st (ptN _ o)) (hG : Good6b D ls Y) (m : J₁ → E) :
    (∀ f ∈ plainCl (stepSc3 D C rd .s6b inc wAt cAt).plain o (pairs D.nb)
        (pick (rA6b D ls Y (ptN _ o)) (rB6b D ls Y (ptN _ o))),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) ↔
      (stepSc3 D C rd .s6b inc wAt cAt).plain.our.par.OutHolds o m :=
  stepCl_iff (stepSc3 D C rd .s6b inc wAt cAt) _ o _ _ m
    (fun b => by
      show _ = Aext D C o.st (rd m) .s6b b.val (ptN _ o)
      rw [hrd m]
      exact rA6b_val cellJ D C ls lmS Y tb o.st _ m hls hT.tQ b.val (hG.tQ b.val b.isLt))
    (fun b => by
      show _ = Bext D C o.st (rd m) .s6b b.val (ptN _ o)
      rw [hrd m]
      exact rB6b_val cellJ D C ls lmS Y tb o.st _ m hls hT.tK b.val (hG.tK b.val b.isLt))

theorem out6b (wAt : PIdx (ldPartFmt E (Step.s6b.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s6b inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hT : Tabs6b D C ls tb o.st (ptN _ o)) (hG : Good6b D ls Y) (m : J₁ → E)
    (h : ∀ f ∈ plainCl (stepSc3 D C rd .s6b inc wAt cAt).plain o (pairs D.nb)
        (pick (rA6b D ls Y (ptN _ o)) (rB6b D ls Y (ptN _ o))),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) :
    (stepSc3 D C rd .s6b inc wAt cAt).plain.our.par.OutHolds o m :=
  (out6b_iff D C ls lmS Y tb cellJ rd hrd inc cAt wAt o hls hT hG m).mp h

/-- The value product below the diagonal. -/
theorem out11_iff (wAt : PIdx (ldPartFmt E (Step.s11.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s11 inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hl : lmS ≤ D.lM) (hT : Tabs11 D C ls lmS tb o.st (ptN _ o)) (hG : Good11 D ls lmS Y)
    (m : J₁ → E) :
    (∀ f ∈ plainCl (stepSc3 D C rd .s11 inc wAt cAt).plain o (pairs D.nb)
        (pick (rA11 D C lmS Y o.st (ptN _ o)) (rB11 D C ls Y o.st (ptN _ o))),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) ↔
      (stepSc3 D C rd .s11 inc wAt cAt).plain.our.par.OutHolds o m :=
  stepCl_iff (stepSc3 D C rd .s11 inc wAt cAt) _ o _ _ m
    (fun b => by
      show _ = Aext D C o.st (rd m) .s11 b.val (ptN _ o)
      rw [hrd m]
      exact rA11_val cellJ D C ls lmS Y tb o.st _ m hl hT.tVM b.val (hG.tVM b.val b.isLt))
    (fun b => by
      show _ = Bext D C o.st (rd m) .s11 b.val (ptN _ o)
      rw [hrd m]
      exact rB11_val cellJ D C ls lmS Y tb o.st _ m hls hT.qVM b.val (hG.qVM b.val b.isLt))

theorem out11 (wAt : PIdx (ldPartFmt E (Step.s11.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s11 inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hl : lmS ≤ D.lM) (hT : Tabs11 D C ls lmS tb o.st (ptN _ o)) (hG : Good11 D ls lmS Y)
    (m : J₁ → E)
    (h : ∀ f ∈ plainCl (stepSc3 D C rd .s11 inc wAt cAt).plain o (pairs D.nb)
        (pick (rA11 D C lmS Y o.st (ptN _ o)) (rB11 D C ls Y o.st (ptN _ o))),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) :
    (stepSc3 D C rd .s11 inc wAt cAt).plain.our.par.OutHolds o m :=
  (out11_iff D C ls lmS Y tb cellJ rd hrd inc cAt wAt o hls hl hT hG m).mp h

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.out8
#print axioms Cb.Pv.Att.End.out6d
#print axioms Cb.Pv.Att.End.out6b
#print axioms Cb.Pv.Att.End.out11
