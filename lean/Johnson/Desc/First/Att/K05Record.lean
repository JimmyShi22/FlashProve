-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Record.lean: the plan's record of the own rounds is recOf: the premise
"p.own = recOf P rows" from the
planner's own return (OnBytes/Model/AttentionPlan.lean: Attention.plan).

Main names:
  `plan_rec`: what plan lays as "own", field by field. (The proof goes the way of plan_shape,
    Johnson/Road/Lane5AttPlan.lean.)
  `counts_place`: over the place's four calls (Att/Claims/Place.lean: PlaceIs): two plane messages;
    two score units with their
    numbers.
  `keys_beq`, `npOf_unit`: a call's number of pieces of a list is the unit's.
  `rec_of_plan`: A.own = recOf P A.own.rows, at every parameter record with the shape's sizes, two
    plane messages and kap = 4.

Premises of rec_of_plan: plan's return; PlaceIs; the shape's Norm; UnitsAll (Att/K05UnitsOk.lean),
for "each score unit has as many
pieces as there are pairs".
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Lane5AttPlan
import Johnson.Desc.First.Att.Claims.Place
import Johnson.Desc.First.Att.K05UnitsOk
import OnBytes.Tie.Pv.Att.OwnAtFits
import Johnson.Desc.First.Att.K05Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Attention Cb.Pv.Att Inst.Model
open OnBytes.Road.L5 (jp_ok bind_ok dimOf callsOf)
open OnBytes.Tie.Pv.Att (recOf)
open K5Law (PlaceIs)

/-- **What plan lays as the record of the own rounds.** -/
theorem plan_rec {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (h : Attention.plan settings i cf = Except.ok A) :
    A.own = { lt := A.S.cf.lt, lgk := A.S.cf.lgk, pairs := A.S.NP, Lam := A.S.Lam,
              planeMessages := (Counts.of A.S).nKRp, score := (Counts.of A.S).score.toList, e := A.S.nvE,
              valueM := A.S.nvVM, valueD := A.S.nvVD, attained := A.S.nvF, bits := A.S.nvH, rows := A.own.rows } := by
  unfold Attention.plan at h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨S, fs⟩ := r
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨seam0, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨seam, -, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  rfl

/-- The counts over the place's four calls. -/
theorem counts_place {S : Attention.Shape} {c0 c1 c2 c3 : ACall} (Pl : PlaceIs S c0 c1 c2 c3) :
    (Counts.of S).nKRp = 2 ∧
      (Counts.of S).score.toList = [(S.nvKF .fm, c1.npOf .fm), (S.nvKF .fd, c1.npOf .fd)] := by
  unfold Counts.of
  rw [← Array.foldl_toList, Pl.calls]
  simp [Counts.call, Counts.plane, Counts.scores, ACall.holds, Pl.k0, Pl.k1, Pl.k2, Pl.k3, Pl.g0, Pl.g1]

theorem keys_beq (a b : Attention.Seg) : (keysOf a == keysOf b) = (a == b) := by
  cases a <;> cases b <;> rfl

/-- A call's number of pieces of a list is the unit's. -/
theorem npOf_unit (g : Geo) (q : ℕ) (c : ACall) (s : Attention.Seg) :
    c.npOf s = (g.unitAt q (callOf c) (keysOf s)).pcs.length := by
  unfold ACall.npOf Geo.unitAt callOf
  simp only [List.filter_map, List.length_map, Function.comp_def, keys_beq]
  rw [← Array.length_toList, Array.toList_filter]

/-- **The plan's record is recOf**, at every parameter record with the shape's sizes, two plane
messages and kap = 4. -/
theorem rec_of_plan {K M X : Type} [Field K] [Fintype K] {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {A : Attention.Plan} (h : Attention.plan settings i cf = Except.ok A) {c0 c1 c2 c3 : ACall}
    (Pl : PlaceIs A.S c0 c1 c2 c3) (N : OnBytes.Road.L5.Norm A.S) (hl : 1 ≤ A.S.lnT) {fs : Model.Forest.Shape}
    {r1 r2 u1 u2 wl ix wh : UnitG} (U : UnitsAll A.S fs r1 r2 u1 u2 wl ix wh) (P : OwnPar K M X)
    (hD : P.D = dimOf A.S) (hn : P.npl = 2) (hk : P.kap = 4) : A.own = recOf P A.own.rows := by
  obtain ⟨k1, k2⟩ := counts_place Pl
  have e := (K5Law.place_scores Pl).symm.trans U.sco
  simp only [List.cons.injEq, and_true] at e
  have nb : (dimOf A.S).nb = A.S.NP := rfl
  have n1 : c1.npOf .fm = A.S.NP := by
    rw [npOf_unit (geoOf A.S) 1 c1 .fm, ← nb, ← U.m2.nPw #[], weights_size, ← e.1]
    rfl
  have n2 : c1.npOf .fd = A.S.NP := by
    rw [npOf_unit (geoOf A.S) 1 c1 .fd, ← nb, ← U.d2.nPw #[], weights_size, ← e.2]
    rfl
  have hlt := N.lt
  rw [plan_rec h, k1, k2, n1, n2]
  unfold recOf
  rw [hD, hn, hk]
  have a1 : A.S.cf.lt = (dimOf A.S).lT := hlt
  have dlg : (dimOf A.S).lg = A.S.cf.lgk := rfl
  have dlP : (dimOf A.S).lP = A.S.lnT - 1 := rfl
  have dlB : (dimOf A.S).lB = A.S.cf.lB := rfl
  have dln : (dimOf A.S).ln = A.S.cf.ldh := rfl
  have dlT : (dimOf A.S).lT = A.S.lnT - 1 + 1 + A.S.cf.lB := rfl
  congr 1
  · show [(A.S.nvKF .fm, A.S.NP), (A.S.nvKF .fd, A.S.NP)] = [((dimOf A.S).lg + (dimOf A.S).lP + ((dimOf A.S).lP + 1) +
      (dimOf A.S).ln, (dimOf A.S).nb), ((dimOf A.S).lg + ((dimOf A.S).lP + 1) + (dimOf A.S).ln, (dimOf A.S).nb)]
    have b1 : A.S.nvKF .fm = A.S.cf.lgk + 2 * A.S.lnT - 1 + A.S.cf.ldh := rfl
    have b2 : A.S.nvKF .fd = A.S.cf.lgk + A.S.lnT + A.S.cf.ldh := rfl
    rw [b1, b2, nb, dlg, dlP, dln]
    congr 2 <;> first | omega | (congr 1; omega)
  · show A.S.cf.lgk + A.S.cf.lt = (dimOf A.S).lg + (dimOf A.S).lT
    omega
  · show A.S.cf.lgk + 2 * A.S.lnT - 1 + A.S.cf.lB = (dimOf A.S).lg + (dimOf A.S).lP + ((dimOf A.S).lP + 1) + (dimOf A.S).lB
    omega
  · show A.S.cf.lgk + A.S.lnT + A.S.cf.lB = (dimOf A.S).lg + ((dimOf A.S).lP + 1) + (dimOf A.S).lB
    omega
  · show A.S.cf.lt + A.S.cf.lgk + A.S.cf.ldh = (dimOf A.S).lT + (dimOf A.S).lg + (dimOf A.S).ln
    omega
  · show A.S.cf.lt + A.S.cf.lgk + 4 = (dimOf A.S).lT + (dimOf A.S).lg + 4
    omega

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.rec_of_plan
