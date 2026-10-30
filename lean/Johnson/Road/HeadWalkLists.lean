-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadWalkLists.lean: which claims on the planes of the lookup's counts the output head's
sub-proof adds.

Johnson/Road/HeadLink.lean names three forms on the planes of the lookup's counts: those that the
lookup's routine planeClaims returns, with the reads that the head's routine claimPlanes hands to it
(PlanesOf). A hypothesis "these claims hold" speaks of such forms. This file shows that they are the
claims which claimPlanes adds: the routine runs planeClaims, adds the three forms that it returns,
in their order, and marks them as added.

Main theorems: claimPlanes_list (with the tables' beginnings and the run of planeClaims written out,
so that the state to which the forms are added is the one that planeClaims leaves); walk_lists (the
same inside the walk, with the lookup's rows, which the walk's first routine adds).

What is not claimed. Nothing on what the three forms are worth, or on what the lookup shows. The
theorems begin "if the routine succeeds": none says that it does. The program does not import
this file.
-/
import Johnson.Road.HeadWalk
import Johnson.Road.HeadLink

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd.Walk

open OnBytes.Model (Aff Fork SubM)

/-- If claimPlanes succeeds: the three tables begin at tB0, tB1, tP; planeClaims, run from the same
state and context, has returned the forms A and left F1 and C1; the list of these forms leads from
F1 to a state G'; and the routine leaves G' with the claims marked as added, and the context C1. In
the words of Johnson/Road/HeadLink.lean: A are three forms on the planes (PlanesOf). -/
theorem claimPlanes_list {R : Model.Head.Run} {F G : Fork} {C D : Ctx} {u : Unit}
    (h : Ok (Model.Head.claimPlanes R) F C u G D) :
    ∃ A tB0 tB1 tP F1 C1 G', Starts R "bH-bits-0" tB0 ∧ Starts R "bH-bits-1" tB1 ∧
      Starts R "bH-pin" tP ∧
      Ok (Model.Forest.planeClaims R.x.g1 R.h.lmbH
        (fun e x => planeCol R (if e == 0 then tB0 else tB1) x) (planeCol R tP)) F C A F1 C1 ∧
      F1.lins A.toList = some G' ∧ G = G'.paid R.x.g1.owedPlanes ∧ D = C1 ∧ PlanesOf R F C A := by
  unfold Model.Head.claimPlanes at h
  rw [ok_bind] at h
  obtain ⟨tB0, F1, C1, h1, h⟩ := h
  obtain ⟨rfl, rfl, s0⟩ := ok_tabAt h1
  rw [ok_bind] at h
  obtain ⟨tB1, F2, C2, h2, h⟩ := h
  obtain ⟨rfl, rfl, s1⟩ := ok_tabAt h2
  rw [ok_bind] at h
  obtain ⟨tP, F3, C3, h3, h⟩ := h
  obtain ⟨rfl, rfl, s2⟩ := ok_tabAt h3
  replace h : Ok (Model.Forest.planeClaims R.x.g1 R.h.lmbH
      (fun e x => planeCol R (if e == 0 then tB0 else tB1) x) (planeCol R tP) >>= fun A =>
        A.forM SubM.lin >>= fun _ => SubM.paid R.x.g1.owedPlanes) _ _ u G D := h
  rw [ok_bind] at h
  obtain ⟨A, F4, C4, h4, h⟩ := h
  rw [ok_bind] at h
  obtain ⟨_, F5, C5, h5, h6⟩ := h
  obtain ⟨e5, hl⟩ := ok_forM_lin h5
  rw [ok_paid] at h6
  exact ⟨A, tB0, tB1, tP, F4, C4, F5, s0, s1, s2, h4, hl, h6.1, h6.2.trans e5,
    tB0, tB1, tP, F4, C4, s0, s1, s2, h4⟩

/-- The lookup's claims in the walk, for XL = 5. The walk's first routine, Forest.objects, starts
from the state F in which the walk begins; the list of the forms that the lookup has kept as its
rows leads from F to a state G0, and the routine leaves G0 with these claims marked as added. The
walk's seventh routine, claimPlanes, starts from a state F6 that is kept from F; there planeClaims
returns forms A and leaves a state Fa; the list of these forms leads from Fa to a state Ga, and the
routine leaves Ga with these claims marked as added. So the forms of which the hypotheses on the
lookup's claims speak (the rows; PlanesOf at a state that is kept from F) are forms that the walk
adds. -/
theorem walk_lists {R : Model.Head.Run} {tl tl' : Model.HTailF2} {wo : Model.WsForkOut}
    {Lc Lc' : Model.LinkCtx} {F G : Fork} {C D : Ctx} (hXL : R.h.XL = 5)
    (hs : F.LS.size = F.ns) (h : OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D) :
    (∃ F1 d0 G0, Ok (Model.Forest.objects R.x.g1) F C () F1 d0 ∧
        F.lins R.x.g1.rows.toList = some G0 ∧ F1 = G0.paid R.x.g1.owedObjects) ∧
      ∃ F6 c6 F7 d6 A tB0 tB1 tP Fa Ca Ga, Kept F F6 ∧
        Ok (Model.Head.claimPlanes R) F6 c6 () F7 d6 ∧
        Ok (Model.Forest.planeClaims R.x.g1 R.h.lmbH
          (fun e x => planeCol R (if e == 0 then tB0 else tB1) x) (planeCol R tP))
          F6 c6 A Fa Ca ∧
        Fa.lins A.toList = some Ga ∧ F7 = Ga.paid R.x.g1.owedPlanes ∧ PlanesOf R F6 c6 A := by
  obtain ⟨_, F1, F2, F3, F4, F5, F6, F7, F8, F9, c1, c2, c3, c4, c5, c6, c7, c8, c9,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9,
    a0, _, a1, _, a2, _, a3, _, a4, _, a5, _, a6, _, _, _, _, _, _, _⟩ := walk_parts h
  obtain ⟨_, G0, l0, e0⟩ := objects_list a0
  have k1 : Kept F F1 := keeps_objects _ F C _ F1 d0 hs a0
  have k2 : Kept F F2 := k1.trans ((adds_claimSquares R).keeps F1 c1 _ F2 d1 k1.1 a1)
  have k3 : Kept F F3 := k2.trans (keeps_claimLedger hXL F2 c2 _ F3 d2 k2.1 a2)
  have k4 : Kept F F4 := k3.trans ((adds_claimStream hXL).keeps F3 c3 _ F4 d3 k3.1 a3)
  have k5 : Kept F F5 := k4.trans (keeps_claimJoin R F4 c4 _ F5 d4 k4.1 a4)
  have k6 : Kept F F6 := k5.trans ((adds_claimPolicy R).keeps F5 c5 _ F6 d5 k5.1 a5)
  obtain ⟨A, tB0, tB1, tP, Fa, Ca, Ga, _, _, _, hp, hl, e6, _, hA⟩ := claimPlanes_list a6
  exact ⟨⟨F1, d0, G0, a0, l0, e0⟩, F6, c6, F7, d6, A, tB0, tB1, tP, Fa, Ca, Ga, k6, a6, hp, hl, e6,
    hA⟩

#print axioms claimPlanes_list
#print axioms walk_lists

end OnBytes.Road.Hd.Walk
