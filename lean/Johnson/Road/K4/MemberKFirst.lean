-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MemberKFirst.lean: THE FIRST GROUP's TWIN OF Johnson/Road/K4/MemberK.lean AND
Johnson/Road/K4/RefSlotsAt.lean: THE RECORD `Plan4L.ValueIs` (Johnson/Road/K4/CloseSevenK.lean)
HOLDS OF THE FIRST GROUP's VALUE AT THE REFERENCE SIZES (`refLF`,
Johnson/Road/K4/RefValueFirst.lean), at the letters that it shares with a later group's, AT THE
RECORD's OWN nT AND nI, UNDER THE PREMISES OF `refF_meets`; AND ITS EMBEDDING's SLOT IS A CLOSED
NUMBER. Four statements.

  `Plan4F.MeetsF.nEndT_eq`, `Plan4F.MeetsF.nI_eq`: the plan's two numbers of end values (the terms'
    and the batched sumcheck's) are the library's, as equations, under `MeetsF`:
    nEndT y = nNu + ne + ne · nx; 2 + (1 + LamM) + (NCL less one in the first group) =
    2 + (1 + ne) + (6 nl + 4 ne).
  `refF_valueIs`: `ValueIs` at nT, nI the plan's two numbers. `ValueIs` is silent on the first
    group's own letters (ls, nb, gB, tok, sE).
  `refF_slots_at`: the embedding's slot is n0 + 726, and the merge's first own slot + 1 + 2 kRef + 2
    is n0 + 766: one more than the later groups' number.

What is a theorem, what a run and what a premise: the heads of RefValue.lean and RefValueFirst.lean
(hla, the shape's number la is 16, is a premise; a run evaluates it at linesKF).

Limits. Numbers, and the table of scales. The public half alone. No statement here names a hearing
or a ledger: that `hear` asks for these two numbers of end values is its text
(OnBytes/Desc/First/K4/Hear.lean: `hearTerms`, `hearStack`). That sE is the hearing's field sVE, and
that f7 + 1 + 2 kRef + 2 is a ledger's next slot behind K4, is not joined here (`hear_end_first`,
`slotsAt_k4Slots`, `MeetsF`'s field wk): Johnson/Road/K4/RefHearNextFirst.lean, which joins the
second, is not in this library.
Which number n0 is at a run is said in no Lean file.
-/
import Johnson.Road.K4.RefValueFirst
import Johnson.Road.K4.RefSlots
import Johnson.Road.K4.CapFromMeets
import Johnson.Road.K4.CloseSevenK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Slice
open OnBytes.Model.Layer (nEndT)
open OnBytes.Model.Verify (Public publicOf layerShape)
open OnBytes.Road.Alg (recordB)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (covers Par)

variable [scl : Scl] {M Xs : Type}

/-- The number of end values of the terms' sumcheck, nEndT y, is the library's, under `MeetsF`. -/
theorem Plan4F.MeetsF.nEndT_eq {Q : Plan4F GE M Xs} {p : Par} {hS : Layer.Shape}
    {pc : List (List String)} (A : Q.MeetsF p hS pc) :
    nEndT p.P.y = Q.D.nNu + Q.D.ne + Q.D.ne * Q.D.nx := by
  have L := laySizes_of_layout A.hy
  have hp3 : hS.p3 = true := by
    rw [← L.shape]
    exact (covers_shape A.hc).2.1
  have hNN : p.P.y.NN * p.P.y.Lam = Q.D.nNu := by
    rw [L.NN, L.Lam, nNu_tie A.Z]
  have hLM : p.P.y.LamM = Q.D.ne := L.LamM.trans (ne_tie A.Z).symm
  have hNE : p.P.y.h.NE = Q.D.nx := by
    rw [L.shape]
    exact A.Z.nexp.symm
  unfold nEndT
  rw [hNN, hLM, hNE, L.shape, hp3, if_pos rfl]
  ring

/-- The number of end values of the batched sumcheck is the library's, under `MeetsF`. -/
theorem Plan4F.MeetsF.nI_eq {Q : Plan4F GE M Xs} {p : Par} {hS : Layer.Shape}
    {pc : List (List String)} (A : Q.MeetsF p hS pc) :
    2 + (1 + p.P.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)) =
      2 + (1 + Q.D.ne) + (6 * Q.D.nl + 4 * Q.D.ne) := by
  have hLM : p.P.y.LamM = Q.D.ne := (laySizes_of_layout A.hy).LamM.trans (ne_tie A.Z).symm
  have e1 : Q.nW = p.hp.NCL - (if (p.g == 0) = true then 1 else 0) :=
    OnBytes.Tie.Pv.Lay.At.nW_eq Q.toPlan4.full _ A.dimIs
  have e2 : Q.nW = 6 * Q.D.nl + 4 * Q.D.ne := by
    have e3 : Q.nW = (Verify.layerNumbers p.P p.hp p.g).weightClaims :=
      OnBytes.Tie.Pv.Lay.At.nW_eq Q.toPlan4.full _ A.dimIs
    rw [e3, ← A.dimIs.claims, sum_cntB]
  rw [hLM, ← e1, e2]

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **`ValueIs` holds of the letters that the first group's value shares with a later group's**, at
nT, nI the plan's two numbers, at `publicOf`'s own record, under the premises of `refF_meets` and
hscl. -/
theorem refF_valueIs (hscl : scl = sclX X p.g) (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hc : covers X.layers = true)
    (hla : (layerShape X.P).la = 16) :
    Plan4L.ValueIs (refLF R tok (nEndT X.layers.y)
        (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)))).toPlan4L
      p (layerShape X.P) := by
  have A := refF_meets R tok (nEndT X.layers.y)
    (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0))) h t hP hG hg0
    hc hla
  have eg : p.g = 0 := beq_iff_eq.mp hg0
  have eT := A.nEndT_eq
  rw [hP] at eT
  refine ⟨by rw [hP]; rfl, by rw [hP]; rfl, fun _ => rfl, Nat.le_of_eq eT.symm,
    (refF_room R tok _ _).1, rfl, rfl, by rw [hscl, hP], ?_⟩
  rw [eg, Nat.zero_mul]
  rfl

/-- **The embedding's slot of the first group's value at the reference sizes, and its merge's first
own slot + 1 + 2 kRef + 2, as closed numbers**, at `publicOf`'s own record, under the premises of
`refF_meets` (among them: the test `recordB` says true; the group is the first; the shape's la is
16). -/
theorem refF_slots_at (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hc : covers X.layers = true)
    (hla : (layerShape X.P).la = 16) {QF : Plan4LF GE M Xs}
    (hQ : QF = refLF R tok (nEndT X.layers.y)
      (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)))) :
    QF.planF.sE = R.n0 + 726 ∧ QF.planF.f7 + 1 + 2 * kRef + 2 = R.n0 + 766 := by
  subst hQ
  have A := refF_meets R tok (nEndT X.layers.y)
    (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0))) h t hP hG hg0
    hc hla
  have eT : nEndT X.layers.y = 266 := by
    have e := A.nEndT_eq
    rw [hP] at e
    exact e.trans ref_nT
  have eI : 2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)) =
      37 := by
    have e := A.nI_eq
    rw [hP] at e
    exact e.trans ref_nI
  rw [eT, eI]
  have s := ref_span R.n0
  have b := ref_behind R.n0
  constructor
  · exact s
  · show (slotsAt Dim.ref R.n0 266 37).f7 + 1 + 1 + 2 * kRef + 2 = R.n0 + 766
    omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.MeetsF.nEndT_eq
#print axioms OnBytes.Road.K4.Plan4F.MeetsF.nI_eq
#print axioms OnBytes.Road.K4.refF_valueIs
#print axioms OnBytes.Road.K4.refF_slots_at
