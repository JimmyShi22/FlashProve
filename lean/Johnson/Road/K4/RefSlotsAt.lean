-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RefSlotsAt.lean: THE PLAN's TWO NUMBERS OF END VALUES (THE TERMS' AND THE BATCHED
SUMCHECK's) ARE THE LIBRARY's, AS EQUATIONS, UNDER `Plan4.Meets` (Johnson/Road/K4/PlanMaps.lean);
AND SO THE MERGE's FIRST OWN SLOT OF THE VALUE AT THE REFERENCE SIZES (`refL`,
Johnson/Road/K4/RefValue.lean) IS THE CLOSED NUMBER OF Johnson/Road/K4/RefSlots.lean, UNDER THE
PREMISES OF `ref_meets`. Three statements.

  `Plan4.Meets.nEndT_eq`: nEndT y = nNu + ne + ne · nx.
  `Plan4.Meets.nI_eq`: 2 + (1 + LamM) + (NCL less one in the first group) =
    2 + (1 + ne) + (6 nl + 4 ne).
  `ref_slots_at`: at `publicOf`'s own record, under the premises of `ref_meets`: the merge's first
    own slot of `refL` is n0 + 726, and that number + 1 + 2 kRef + 2 is n0 + 765. Whatever the table
    of scales.

Limits. Numbers alone. No statement here names a hearing or a ledger: that `hear` asks for these two
numbers of end values is its text (OnBytes/Desc/First/K4/Hear.lean: `hearTerms`, `hearStack`).
`Meets` shuts out the first group (its field hg): the "less one" in `nI_eq` is idle there, and
stands so that the left side is `ref_nine`'s. That f7 + 1 + 2 kRef + 2 is a ledger's next slot
behind K4 is not joined here (`hear_end_later`, `slotsAt_k4Slots`, `Meets`' field wk). Which number
n0 is at a run is said in no Lean file. What is a theorem, what a run and what a premise: the head
of RefValue.lean.
-/
import Johnson.Road.K4.RefValue
import Johnson.Road.K4.RefSlots
import Johnson.Road.K4.CapFromMeets

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Slice
open OnBytes.Model.Layer (nEndT)
open OnBytes.Model.Verify (Public publicOf)
open OnBytes.Road.Alg (recordB)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef)
open OnBytes.Desc.First.K4 (covers Par)

variable [scl : Scl] {M Xs : Type}

/-- The number of end values of the terms' sumcheck, nEndT y, is the library's, under `Meets`. -/
theorem Plan4.Meets.nEndT_eq {Q : Plan4 GE M Xs} {p : Par} {hS : Layer.Shape}
    {pc : List (List String)} (A : Q.Meets p hS pc) :
    nEndT p.P.y = Q.D.nNu + Q.D.ne + Q.D.ne * Q.D.nx := by
  have L := laySizes_of_layout A.hy
  have hNN : p.P.y.NN * p.P.y.Lam = Q.D.nNu := by
    rw [L.NN, L.Lam, nNu_tie A.Z]
  have hLM : p.P.y.LamM = Q.D.ne := L.LamM.trans (ne_tie A.Z).symm
  have hNE : p.P.y.h.NE = Q.D.nx := by
    rw [L.shape]
    exact A.Z.nexp.symm
  unfold nEndT
  rw [hNN, hLM, hNE, L.shape, A.p3, if_pos rfl]
  ring

/-- The number of end values of the batched sumcheck is the library's, under `Meets`. -/
theorem Plan4.Meets.nI_eq {Q : Plan4 GE M Xs} {p : Par} {hS : Layer.Shape}
    {pc : List (List String)} (A : Q.Meets p hS pc) :
    2 + (1 + p.P.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)) =
      2 + (1 + Q.D.ne) + (6 * Q.D.nl + 4 * Q.D.ne) := by
  have hLM : p.P.y.LamM = Q.D.ne := (laySizes_of_layout A.hy).LamM.trans (ne_tie A.Z).symm
  have e1 : Q.nW = p.hp.NCL - (if (p.g == 0) = true then 1 else 0) :=
    OnBytes.Tie.Pv.Lay.At.nW_eq Q.full _ A.dimIs
  rw [hLM, ← e1, nW_closed A]

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **The merge's first own slot of the value at the reference sizes, and that number + 1 + 2 kRef +
2, as closed numbers**, at `publicOf`'s own record, under the premises of `ref_meets` (among them:
the test `recordB` says true; the group is not the first). -/
theorem ref_slots_at (R : RefLetters M Xs) (hg : p.g < 12) (h : publicOf pol KL lay = .ok X)
    (t : recordB X p.g = true) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hg0 : (p.g == 0) = false) (hc : covers X.layers = true)
    {QL : Plan4L GE M Xs}
    (hQ : QL = refL R p.g hg (nEndT X.layers.y)
      (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)))) :
    QL.slots.f7 = R.n0 + 726 ∧ QL.slots.f7 + 1 + 2 * kRef + 2 = R.n0 + 765 := by
  subst hQ
  have A := ref_meets R hg h t hP hG hg0 hc (nEndT X.layers.y)
    (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)))
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
  exact ⟨ref_span R.n0, ref_behind R.n0⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.Meets.nEndT_eq
#print axioms OnBytes.Road.K4.Plan4.Meets.nI_eq
#print axioms OnBytes.Road.K4.ref_slots_at
