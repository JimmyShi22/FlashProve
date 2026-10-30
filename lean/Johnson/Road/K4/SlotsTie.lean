-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/SlotsTie.lean: THE SEVENTEEN FIRST SLOTS OF THE VALUE (`slotsAt`,
Johnson/Road/K4/ValueSlots.lean: formulas in the library's sizes D) ARE THE NUMBERS THAT A HEARING
OF K4's TEXT HOLDS (`k4Slots`, Johnson/Road/K4/HearSlots.lean: formulas in the program's public
numbers). A definition, statements and proofs.

  `to4`: the seventeen numbers of `Slots4` among the twenty of `K4Slots`: all but sH1, sB0 and sV.
  `slotsAt_k4Slots`: `slotsAt D n0 nT nI = to4 (k4Slots P hp g n0)` at nT := `nEndT P.y` and
    nI := 2 + (1 + LamM) + (NCL less one in the first group), under the premises of
    `dimIs_layerNumbers` (Johnson/Road/K4/PlanSizes.lean).
  `hear_slotsAt`: where the hearing returns in a later group from a ledger with arrays of the
    right sizes and next slot n0: the fifteen slot numbers of `hear_slots` and the merge's first
    own slot are fields of `slotsAt D n0 nT nI`; three of them (further end values of the batched
    sumcheck) are its field vI plus a public number.

Limits. Numbers of slots alone: nothing on what lies under a slot. The numbers fS, fI, f5 and f6
stand in no field of the hearing's record: `hear_slotsAt` says nothing of them. In the first group
the merge's first own slot is f7 + 1 (`hear_end_first`), so `hear_slotsAt` is stated for a later
group. The table of scales and the reading ρ are idle letters. One direction: from a return.

-/
import Johnson.Road.K4.PlanSizes
import Johnson.Road.K4.ValueSlots
import Johnson.Road.K4.HearSlotsEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Lay Pub Reads HPlan2 Own layout readsOf lamSOf nclOf nEndT)
open Cb.Pv.Lay.At (kS kS_eq)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim lamS lDd lF lFe)
open OnBytes.Desc.First.K4 (covers K4Slots k4Slots sPvAt sClAt tClAt kPAt hPAt engFl hear
  hear_slots hear_end_later)

/-- The seventeen numbers of `Slots4` among the twenty of `K4Slots`. -/
def to4 (s : K4Slots) : Slots4 :=
  ⟨s.sW, s.sS, s.sL, s.sPv, s.sCl, s.sP, s.sEnd, s.tCl, s.tP, s.tEnd, s.kP, s.sA0, s.hP, s.hL,
    s.h2P, s.h2L, s.nx⟩

variable {hS : Layer.Shape} {D : Dim} [scl : Scl] {pc : List (List String)} {P : Pub} {hp : HPlan2}
  {g : ℕ}

include scl in
/-- **The value's formulas are the hearing's**, under the premises of `dimIs_layerNumbers`. -/
theorem slotsAt_k4Slots (hy : layout hS pc = .ok P.y) (hc : covers P = true)
    (hrd : readsOf P.y = .ok P.rd) (Z : Sized hS D) (hl : hp.lamS = lamSOf P.y)
    (hn : hp.NCL = nclOf P.y g) (n0 : ℕ) :
    slotsAt D n0 (nEndT P.y)
        (2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0))) =
      to4 (k4Slots P hp g n0) := by
  have X := dimIs_layerNumbers hy hc hrd Z hl hn
  obtain ⟨m1, m2, m3⟩ := Fo.readsOf_mu hrd
  have xlt : P.y.h.lt = D.lT := X.lt.symm
  have xNI : P.y.NI = D.nNu := X.NI.symm
  have xNS : ledNS P.y.h.xl = 9 := X.NS.symm
  have xlNI : P.rd.lNI = D.lL + 1 := X.lNI.symm
  have xlPd : P.y.lPd = lDd D := X.lPd.symm
  have xNP : ledNP P.y.h.xl = 7 := X.NP.symm
  have xNO : ledNO P.y.h.xl = 4 := X.NO.symm
  have xlam : hp.lamS = lamS D := X.lamS.symm
  have xll : P.y.h.ll = D.lL := X.ll.symm
  have xlPf : P.y.lPf = lF D := X.lPf.symm
  have xlfe : P.y.lfe = lFe D := X.lfe.symm
  simp only [slotsAt, to4, k4Slots, sPvAt, sClAt, tClAt, kPAt, hPAt, kS_eq, m1, m2, m3, xlt, xNI,
    xNS, xlNI, xlPd, xNP, xNO, xlam, xll, xlPf, xlfe]
  generalize hp.NCL - (if (g == 0) = true then 1 else 0) = c
  generalize nEndT P.y = nT
  generalize lamS D = a1
  generalize lDd D = a2
  generalize lF D = a3
  generalize lFe D = a4
  generalize D.nNu = a5
  generalize D.lL = a6
  generalize D.lT = a7
  generalize P.y.LamM = a8
  congr 1 <;> omega

variable {K : Type} [Field K] (ρ : Reading K)

include scl ρ in
/-- **A hearing in a later group holds the value's numbers**, from a ledger with arrays of the
right sizes, under the premises of `dimIs_layerNumbers`. -/
theorem hear_slotsAt (hy : layout hS pc = .ok P.y) (hrd : readsOf P.y = .ok P.rd) (Z : Sized hS D)
    (hl : hp.lamS = lamSOf P.y) (hn : hp.NCL = nclOf P.y g) {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hF : OnBytes.PscRun.Sized F)
    (h : hear engFl P hp g fo F t = some (o, G, u)) (hg : (g == 0) = false) {s : Slots4}
    (hs : s = slotsAt D F.next (nEndT P.y)
      (2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0)))) :
    o.H.sW = s.sW ∧ o.H.wpl.sL = s.vS ∧ o.H.sPv = s.sP ∧ o.H.tV.sCl = s.cP0 ∧
      o.H.tV.p.first = s.fP ∧ o.H.tV.sEnd = s.vP ∧
      (∃ tT, o.H.tT = some tT ∧ tT.sCl = s.cT0 ∧ tT.p.first = s.fT ∧ tT.sEnd = s.vT) ∧
      o.K.sA0 = s.vI ∧ o.K.sH1 = s.vI + 1 ∧ o.K.sB0 = s.vI + 1 + (1 + P.y.LamM) ∧
      o.K.sV = s.vI + 1 + (1 + P.y.LamM) + 1 ∧ o.hd.sL = s.v5 ∧
      (∃ hd2, o.hd2 = some hd2 ∧ hd2.sL = s.v6) ∧ o.wo.p.first = s.f7 := by
  have hc : covers P = true := (OnBytes.Desc.First.K4.hear_parts_later h hg).1
  rw [slotsAt_k4Slots hy hc hrd Z hl hn F.next] at hs
  subst hs
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hear_slots ρ hF h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, (hear_end_later ρ hF h hg).2.1⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.slotsAt_k4Slots
#print axioms OnBytes.Road.K4.hear_slotsAt
