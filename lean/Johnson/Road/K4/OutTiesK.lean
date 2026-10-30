-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OutTiesK.lean: THE RECORD OF PUBLIC TIES `OutTies`
(Johnson/Road/K4/StageOutsAll.lean), PAID FROM `Plan4.Meets` (Johnson/Road/K4/PlanMaps.lean) AND THE
RETURN OF THE BATCHED SUMCHECK's HEARING, at the value with its slots and orders laid
(`Plan4L.plan`, Johnson/Road/K4/ValueSlots.lean). Small statements and one theorem.

  `stackEnd_wD`, `stack_wD`: where `hearStack` returns, the width of the first gated panel in its
    record is ll + lPf: the plain function `stackEnd` (OnBytes/Model/LayerPanels.lean) returns
    nothing otherwise (`hearStack_public`).
  `stack_rs_size`: its record holds as many challenges as the sumcheck has rounds
    (`hearStack_tape`).
  `wide5`, `wide6`: lL + lF and lFe are at most the library's number of rounds of the batched
    sumcheck: the panel of the gated products is one of the stacked panels (`panTotal_eq`,
    Johnson/Road/K4/PlanSizes.lean); an expert is no wider than a layer.
  `outTies_K`: all twenty fields.

WHERE THE FIELDS COME FROM. The three orders and the two bounds "at least nine variables": what
`Plan4L.plan` lays in, and its fields h5, h6; not taken from `Meets` here (the two bounds are no
open debt: see the head of Johnson/Road/K4/SevenPaid.lean). The numbers of rounds and the bits:
`DimIs` (`Plan4.Meets.dimIs`) and `Fo.readsOf_mu`. wD and rs: the hearing. The reading of
1/2: `gl_half` (Johnson/Road/K4/ClaimsPaid.lean).

Limits. Equations and bounds between numbers. `Meets` and the hearing's return are premises.

-/
import Johnson.Road.K4.StageOutsAll
import Johnson.Road.K4.ClaimsPaid
import Johnson.Road.K4.ValueSlots
import OnBytes.Desc.First.K4.StackPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2 Own Heard HeardStack Env Lay SBlk StackEnd stackEnd)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim lDd lF lFe lamS panTotal)
open Cb.Pv.Lay.At (kS kS_eq)
open OnBytes.Desc.First.K4 (Par hearStack engFl hearStack_public hearStack_tape)
open OnBytes.Desc.First.P1 (gl plainWs)

/-- The plain function returns nothing unless the down product's panel has ll + lPf bits. -/
theorem stackEnd_wD {y : Lay} {bl : Array SBlk} {rs : Array E} {lam : ℕ} {om H1 V : Array E}
    {a b : E} {s : StackEnd} (h : stackEnd y bl rs lam om H1 V a b = some s) :
    s.wD = y.h.ll + y.lPf := by
  unfold stackEnd at h
  obtain ⟨s0, _, h1⟩ := Option.bind_eq_some_iff.mp h
  by_cases hw : (s0.wD != y.h.ll + y.lPf) = true
  · rw [if_pos hw] at h1
    cases h1
  · rw [if_neg hw] at h1
    obtain rfl := Option.some.inj h1
    simpa using hw

theorem stack_wD {P : Pub} {v : Env} {H : Heard} {lamS NCLp : ℕ} {F G : Fork} {t u : Tape}
    {K : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    K.fin.wD = P.y.h.ll + P.y.lPf := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hE⟩ := hearStack_public h
  exact stackEnd_wD hE

theorem stack_rs_size {P : Pub} {v : Env} {H : Heard} {lamS NCLp : ℕ} {F G : Fork} {t u : Tape}
    {K : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    K.rs.size = lamS := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ms, _, _, _, _, _, _, _, _, _, _, hw, _, _, hr,
    _⟩ := hearStack_tape h
  have hl : ms.length = lamS := by
    have e := congrArg List.length hw
    rw [List.length_map] at e
    rw [e]
    exact List.length_replicate
  rw [← Array.length_toList, hr, List.length_reverse, List.length_map, hl]

/-- The gated products' panel is one of the stacked panels. -/
theorem wide5 (D : Dim) : D.lL + lF D ≤ kS D := by
  have e0 : Nat.clog 2 D.nl = D.lL := by
    unfold Inst.Model.FFSeg.Dim.nl
    exact Nat.clog_pow 2 _ (by norm_num)
  have h1 : 2 ^ (D.lL + lF D) ≤ panTotal D := by
    rw [panTotal_eq, e0]
    unfold lF
    exact (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  rw [kS_eq]
  unfold lamS
  calc D.lL + lF D = Nat.clog 2 (2 ^ (D.lL + lF D)) := (Nat.clog_pow 2 _ (by norm_num)).symm
    _ ≤ Nat.clog 2 (panTotal D) := Nat.clog_mono_right 2 h1

/-- An expert is no wider than a layer. -/
theorem wide6 (D : Dim) (hfe : D.fe ≤ D.f) : lFe D ≤ kS D := by
  have h1 : lFe D ≤ lF D := Nat.clog_mono_right 2 hfe
  have h2 := wide5 D
  omega

variable [scl : Scl] {M X : Type} {QL : Plan4L Cb.Gl.E M X} {par : Par} {hS : Layer.Shape}
  {pcl : List (List String)}

/-- **The twenty public ties**, under `Meets` at the value with its slots and orders laid, where the
batched sumcheck's hearing returns K4's record. -/
theorem outTies_K (A : QL.plan.Meets par hS pcl) (tk : Array Nat) {o : Own} {NCLp : ℕ}
    {G2 G3 : Fork} {t u : Tape}
    (c4 : hearStack engFl { par.P with tokv := tk } o.v o.H par.hp.lamS NCLp G2 t =
      some (o.K, G3, u)) :
    OutTies QL.plan.full { par.P with tokv := tk } par.hp o := by
  have Xd := A.dimIs
  obtain ⟨m1, m2, m3⟩ := Fo.readsOf_mu A.hrd
  have xlt : QL.plan.D.lT = par.P.y.h.lt := Xd.lt
  have xlNI : QL.plan.D.lL + 1 = par.P.rd.lNI := Xd.lNI
  have xlPd : lDd QL.plan.D = par.P.y.lPd := Xd.lPd
  have xll : QL.plan.D.lL = par.P.y.h.ll := Xd.ll
  have xlPf : lF QL.plan.D = par.P.y.lPf := Xd.lPf
  have xlfe : lFe QL.plan.D = par.P.y.lfe := Xd.lfe
  have xk : kS QL.plan.D = par.hp.lamS := (kS_eq QL.plan.D).trans Xd.lamS
  exact
    { eS := rfl
      n5 := QL.h5
      e5 := rfl
      n6 := QL.h6
      e6 := rfl
      m1 := by
        show QL.plan.D.lL + 1 + (lDd QL.plan.D + QL.plan.D.lT) = par.P.rd.muV
        omega
      lt := xlt
      k4 := xk
      m5 := by
        show QL.plan.D.lL + lF QL.plan.D + QL.plan.D.lT = par.P.rd.muH
        omega
      m6 := by
        show QL.plan.D.lL - 1 + (lFe QL.plan.D + QL.plan.D.lT) = par.P.rd.muH2
        omega
      k7 := A.wk
      lI := xlNI
      lP := xlPd
      lfe := xlfe.symm
      ll := by
        show par.P.y.h.ll - 1 = QL.plan.D.lL - 1
        omega
      wD := by
        have e := stack_wD c4
        show o.K.fin.wD = QL.plan.D.lL + lF QL.plan.D
        rw [e]
        show par.P.y.h.ll + par.P.y.lPf = _
        omega
      le5 := wide5 QL.plan.D
      le6 := wide6 QL.plan.D QL.hfe
      rs := by
        show kS QL.plan.D ≤ o.K.rs.size
        rw [stack_rs_size c4, xk]
      half := eq_inv_of_mul_eq_one_left gl_half }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.stack_wD
#print axioms OnBytes.Road.K4.stack_rs_size
#print axioms OnBytes.Road.K4.wide5
#print axioms OnBytes.Road.K4.outTies_K
