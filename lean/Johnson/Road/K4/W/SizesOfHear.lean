-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/SizesOfHear.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE. That a hearing returns. Where K4Plan holds: see
W/GroundOfHear.lean's head. Nothing on soundness, on completeness or on any other property.
No property is claimed.

The public numbers K4Sizes (W/Ground.lean) at what a hearing of the layers' own rounds (sub-protocol
K4) returned, from the hearing's return and the public facts K4Plan (W/GroundOfHear.lean). So
K4Sizes is no hypothesis of its own where a hearing returns.

  `sizes_of_hear`   the eighteen numbers. The powers of two come from the layout's own tests (an
      expert's width has one bit set, and a layer's width is twice that), the three points' sizes
      from the hearing's return and from what readsOf lays.
-/
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.K4.PlanClauses
import Johnson.Road.K4.Total.HearSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road OnBytes.K.Kc
open OnBytes.Model.Layer (Env Lay Heard Pub Own Reads layout scalesHeld readsOf)
open Inst.Model.FFSeg (Dim lF lFe)
open OnBytes.Desc.First.K4 (engFl hear)

/-- **K4Sizes at what a hearing returned.** CONDITIONAL: on the hearing's return and on A. -/
theorem sizes_of_hear {P : Pub} {hp : Layer.HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) {hS : Layer.Shape}
    {pc : List (List String)} {tl : HTailF2} {D : Dim} (A : K4Plan hS pc P g tl D) :
    K4Sizes P o.v o.H o.hd o.hd2 D := by
  obtain ⟨_, vy, _⟩ := ground_of_hear h A
  obtain ⟨_, sV, sH, sH2, _⟩ := Desc.First.K4.Total.hear_sizes h
  obtain ⟨m1, m2, m3⟩ := Fo.readsOf_mu A.reads
  have L := laySizes_of_layout A.lay
  have Mr := layMore_of_layout A.lay
  have Ad := admitted_of_layout A.lay A.sw.p3
  obtain ⟨_, _, n3, n4, _⟩ := norms_sizes A.lay A.sized
  obtain ⟨g1, g2, g3, g4⟩ := gated_sizes A.lay A.sw.p3 A.sized
  have Z := A.sized
  have two : 2 * 2 ^ hS.ll = 2 ^ (hS.ll + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have eN : P.rd.lNI = hS.ll + 1 := by
    rw [Model.Fit.readsOf_lNI A.reads, L.NI, two, ceilLog2_eq_clog, Nat.clog_pow 2 _ (by decide)]
  have efe : hS.fe = 2 ^ lFe D := by
    rw [← Z.fe]
    exact g4
  have ef : hS.f = 2 ^ (lFe D + 1) := by rw [Mr.ffe A.sw.p3, efe, Nat.pow_succ, Nat.mul_comm]
  have eF : lF D = lFe D + 1 := by
    show Nat.clog 2 D.P.f = _
    rw [Z.f, ef, Nat.clog_pow 2 _ (by decide)]
  have elPf : P.y.lPf = lF D := by
    rw [L.lPf, ceilLog2_eq_clog, ef, Nat.clog_pow 2 _ (by decide), eF]
  have elfe : P.y.lfe = lFe D := by
    rw [L.lfe, if_pos A.sw.p3, ceilLog2_eq_clog, efe, Nat.clog_pow 2 _ (by decide)]
  have ela : P.y.h.la = P.y.ls + D.lT := by
    rw [L.shape, Ad.la, Z.lT]
  have elt : P.y.h.lt = D.lT := by rw [L.shape, Z.lT]
  have ell : P.y.h.ll = D.lL := by rw [L.shape, Z.lL]
  have ell' : hS.ll = D.lL := Z.lL.symm
  rw [elt] at m1 m2 m3
  rw [ell] at m2 m3
  rw [elPf] at m2
  rw [elfe] at m3
  refine
    { y := vy.symm
      NI := ?_
      la := ?_
      Pd := ?_
      lsPd := ?_
      NIle := ?_
      blocks := ?_
      wpl := ?_
      lsF := ?_
      lsFe := ?_
      Lam := ?_
      f := ?_
      Pf := ?_
      LamM := ?_
      fe := ?_
      Dfe := g4
      hd := ?_
      hd2 := ?_ }
  · rw [vy, L.NI, nNu_tie Z]
  · rw [vy]
    exact ela
  · rw [vy]
    exact Mr.Pd
  · rw [vy]
    exact n4
  · rw [vy, L.NI, eN, two]
  · rw [vy, L.shape]
    exact n3
  · rw [vy, sV, m1, ela]
    omega
  · rw [vy]
    exact g2
  · rw [vy]
    exact g3
  · rw [vy, L.Lam, ell']
  · rw [vy, L.shape, ef, eF]
  · rw [vy, Mr.Pf, elPf]
  · rw [vy, L.LamM, ell']
    obtain ⟨k, hk⟩ : ∃ k, D.lL = k + 1 := ⟨D.lL - 1, by omega⟩
    rw [hk, Nat.pow_succ, Nat.mul_div_cancel _ (by decide), Nat.add_sub_cancel]
  · rw [vy, L.shape]
    exact efe
  · rw [vy, sH, m2]
    omega
  · intro o2 h2
    rw [h2] at sH2
    have e : o2.r.size = P.rd.muH2 := Option.some.inj sH2
    rw [vy, e, m3]
    omega

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.sizes_of_hear
