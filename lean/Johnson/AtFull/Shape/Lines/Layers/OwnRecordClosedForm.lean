-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/OwnRecordClosedForm.lean: what stays of the shape of what the
hearing of the layers' own rounds leaves, when the parts named below are left out, is a closed form
in the plan, the lookup's record's shape and two numbers of the ledger. General; nothing is
evaluated.

Why. So the shape after the step can be written without running the hearing. It holds from a
return and the library's HearLeft, which hearing_returnsAtBlankRun hands over at the blank run. Left
out are the calls and rows of own.H.fo, H.tV.rowU, the p and rowU of H.tT, H.KT, and the entries of
K.Alin, K.Blin and K.rowS (their slots stay); K, of type StackSh, is the batched sumcheck's part of
the record. wo.recs stays a variable here: MergeRecordsClosedForm.lean gives it.

  emptyForm, bareSumcheckShape   what stands in the place of what is left out.
  lookupRecordLessParts, normsLessParts, stackLessParts, **ownRecordLessParts**   what stays.
  normsClosedForm, stackClosedForm, mergeSlotsAt, **ownRecordClosedForm**   the closed forms.
  norms_isClosedForm, stack_isClosedForm, **ownRecord_isClosedForm**   from a return and HearLeft,
                          what stays is the closed form.

Limits. From a return and HearLeft: that the hearing returns is not said here. What the parts left
out hold is not said, and that no later member opens them is not shown here. What any of this costs
Lean's kernel is not measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.BatchedSumcheckSlots

set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own TableAt)
open VerifiableInference.Desc.First.Shape

/-- The form that names nothing. -/
def emptyForm : AffSh := AffSh.mk [] []
/-- The shape of a sumcheck with nothing in it. -/
def bareSumcheckShape : PscSh := PscSh.mk false false [] 0 0 emptyForm false

/-- A lookup's record less its calls and rows. -/
def lookupRecordLessParts (h : HeardAll) : HeardAll :=
    { h with shape := { h.shape with calls := #[] }, rows := [] }

/-- What stays of the norms' part of the own record. -/
def normsLessParts (H : NormsSh) : NormsSh :=
  { H with fo := lookupRecordLessParts H.fo, tV := { H.tV with rowU := emptyForm },
           tT := H.tT.map fun t => { t with p := bareSumcheckShape, rowU := emptyForm }, KT :=
               emptyForm }

/-- What stays of the batched sumcheck's part: the three long forms keep their slots alone. -/
def stackLessParts (K : StackSh) : StackSh :=
  { K with Alin := AffSh.mk [] K.Alin.slots, Blin := AffSh.mk [] K.Blin.slots,
           rowS := AffSh.mk [] K.rowS.slots }

/-- **What stays of the own record.** -/
def ownRecordLessParts (ow : OwnSh) : OwnSh :=
    { ow with H := normsLessParts ow.H, K := stackLessParts ow.K }

/-- The closed form of what stays of the norms' part. n: the ledger's next slot before. -/
def normsClosedForm (P : Pub) (g : Nat) (h : HeardAll) (n : Nat) : NormsSh :=
  { fo := lookupRecordLessParts h, PV := P.y.h.lt
    ZE := if (g == 0) = true then P.y.ls + P.y.h.lt else 0
    tkh := if (g == 0) = true then P.y.lPd - P.y.ls else 0
    ztF := P.y.h.lt, sW := n, gp := ledNS P.y.h.xl
    wpl :=
      { r := P.rd.muV, sL := n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + 2))
        sR := n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + 2)) + 1
        row := rowFormSh (n + ledNS P.y.h.xl * P.y.NI) (2 * P.rd.muV + 3)
          (AffSh.mk [] ((List.range P.y.NI).flatMap fun i =>
            (List.range (ledNS P.y.h.xl)).map fun s => n + ledNS P.y.h.xl * i + s))
          (AffSh.mk [] []) }
    sPv := n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + (2 + 2)))
    omV := ledNP P.y.h.xl * P.y.NI
    tV :=
      { sCl := n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + (2 + 2))) + ledNP P.y.h.xl *
          P.y.NI
        sEnd := n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + (2 + 2))) +
          ledNP P.y.h.xl * P.y.NI + 1 + (1 + (2 * P.y.h.lt + 2))
        r := P.y.h.lt
        p := PscSh.mk false true (List.replicate P.y.h.lt 3 ++ [3]) (P.y.h.lt + 1)
          (n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + (2 + 2))) + ledNP P.y.h.xl * P.y.NI +
              1)
          (AffSh.mk [] [n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + (2 + 2))) +
            ledNP P.y.h.xl * P.y.NI]) true
        rowU := emptyForm }
    tT := some { sCl := n + slotsNorms P, sEnd := n + slotsNorms P + (1 + (1 + (2 * P.y.h.lt + 1)))
                 r := P.y.h.lt, p := bareSumcheckShape, rowU := emptyForm }
    KT := emptyForm }

variable {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}
  {iU3 : Nat} {tab : List TableAt}

/-- From a return and HearLeft, what stays of the norms' part is the closed form. -/
theorem norms_isClosedForm (hh : hearFl P hp g fo F t = some (o, G, u))
    (hL : HearLeft P hp g fo iU3 tab F G o) :
    normsLessParts (normsSh o.H) = normsClosedForm P g (heardAll fo) F.next := by
  have N := hL.nums
  obtain ⟨f, e1, e2⟩ := squaresLayer_rowShape hh
  have hf : f = F.next + ledNS P.y.h.xl * P.y.NI := by
    have := N.wplL
    omega
  obtain ⟨tT, hT⟩ := Option.isSome_iff_exists.1 hL.tT
  have hT3 := N.tT
  rw [hT] at hT3
  have hT4 : (tT.sCl, tT.sEnd, tT.r.size) = (F.next + slotsNorms P,
      F.next + slotsNorms P + (1 + (1 + (2 * P.y.h.lt + 1))), P.y.h.lt) := Option.some.inj hT3
  have t1 : tT.sCl = F.next + slotsNorms P := congrArg Prod.fst hT4
  have t2 : tT.sEnd = F.next + slotsNorms P + (1 + (1 + (2 * P.y.h.lt + 1))) :=
    congrArg (fun x => x.2.1) hT4
  have t3 : tT.r.size = P.y.h.lt := congrArg (fun x => x.2.2) hT4
  unfold normsLessParts normsClosedForm normsSh levelSh tscSh
  dsimp only
  rw [hT, hL.fo, N.pv, N.ze, N.tkh, N.ztF, N.gp, N.omV, hL.wpl, N.wplR, N.wplL, e2, hf, N.tvR,
    rowProductsSumcheck_openShape hh, hL.tvEnd, hL.tvFirst, N.tvCl, N.sPv, N.sW]
  show _ = _
  simp only [Option.map_some, t1, t2, t3]

/-- The closed form of what stays of the batched sumcheck's part. -/
def stackClosedForm (P : Pub) (hp : HPlan2) (h : HeardAll) (n : Nat) : StackSh :=
  { rs := hp.lamS, sA0 := n + slotsNorms P + slotsTerms P + (1 + (2 * hp.lamS + 2))
    sH1 := n + slotsNorms P + slotsTerms P + (1 + (2 * hp.lamS + 2)) + 1
    sB0 := n + slotsNorms P + slotsTerms P + (1 + (2 * hp.lamS + 2)) + 1 + (1 + P.y.LamM)
    sV := n + slotsNorms P + slotsTerms P + (1 + (2 * hp.lamS + 2)) + 1 + (1 + P.y.LamM) + 1
    Alin := AffSh.mk [] [], Blin := AffSh.mk [] [], wD := P.y.h.ll + P.y.lPf
    rowS := AffSh.mk [] (List.range' (n + slotsNorms P + slotsTerms P) (2 * hp.lamS + 3) ++
      ((n + slotsNorms P) :: h.cEnd.slots ++
        (List.range' (n + slotsNorms P + 1) (2 * P.y.h.lt + 2) ++ [n + slotsNorms P]))) }

/-- From a return and HearLeft, what stays of the batched sumcheck's part is the closed form. -/
theorem stack_isClosedForm (hh : hearFl P hp g fo F t = some (o, G, u))
    (hL : HearLeft P hp g fo iU3 tab F G o) :
    stackLessParts (stackSh o.K) = stackClosedForm P hp (heardAll fo) F.next := by
  have N := hL.nums
  obtain ⟨a1, a2⟩ := endForms_nameNoSlots hh
  obtain ⟨tT, hT, k1⟩ := secondTokenForm_slots hh
  obtain ⟨f, tT', hT', s1, s2⟩ := batchedRow_slots hh
  obtain rfl : tT = tT' := Option.some.inj (hT.symm.trans hT')
  have hf : f = F.next + slotsNorms P + slotsTerms P := by
    have := N.sA0
    omega
  have hT3 := N.tT
  rw [hT] at hT3
  have t1 : tT.sCl = F.next + slotsNorms P := congrArg Prod.fst (Option.some.inj hT3)
  unfold stackLessParts stackClosedForm stackSh
  dsimp only
  rw [a1, a2, s2, k1, hf, t1, hL.fo, N.rs, N.sV, N.sB0, N.sH1, N.sA0, N.wD]
  rfl

/-- mergeSlots' text (OnBytes/Desc/First/K4/MergeClaims.lean) at two numbers. -/
def mergeSlotsAt (hp : HPlan2) (g sV sVE : Nat) : Array Nat :=
  (Array.range (hp.NCL - (if (g == 0) = true then 1 else 0))).map (sV + ·) ++
    (if (g == 0) = true then #[sVE] else #[])

/-- **The closed form.** n, m: the ledger's next slot before and after; recs: what the merge
leaves of each weight claim. -/
def ownRecordClosedForm (P : Pub) (hp : HPlan2) (g iU3 : Nat) (tab : List TableAt) (h : HeardAll)
    (n m : Nat) (recs : List RecSh) : OwnSh :=
  let base := n + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g)
  let sH1 := n + slotsNorms P + slotsTerms P + (1 + (2 * hp.lamS + 2)) + 1
  { g := g, iU3 := iU3, K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0
    tab := tab.map fun x => (x.name, x.first, x.len), zk := h.zk
    H := normsClosedForm P g h n, K := stackClosedForm P hp h n
    hd := { r := P.rd.muH, sL := base + (1 + (2 * P.rd.muH + 2))
            sR := base + (1 + (2 * P.rd.muH + 2)) + 1
            row := rowFormSh base (2 * P.rd.muH + 3) (AffSh.mk [] [sH1]) (AffSh.mk [] []) }
    hd2 := some
      { r := P.rd.muH2, sL := base + (1 + (2 * P.rd.muH + (2 + 2))) + (1 + (2 * P.rd.muH2 + 2))
        sR := base + (1 + (2 * P.rd.muH + (2 + 2))) + (1 + (2 * P.rd.muH2 + 2)) + 1
        row := rowFormSh (base + (1 + (2 * P.rd.muH + (2 + 2)))) (2 * P.rd.muH2 + 3)
          (AffSh.mk [] ((List.range P.y.LamM).map fun lm => sH1 + 1 + lm)) (AffSh.mk [] []) }
    sVE := if (g == 0) = true then base + slotsGated P else 0
    wo := { rm := P.wsLay.lk
            p := PscSh.mk false true (List.replicate P.wsLay.lk 3 ++ [2]) (P.wsLay.lk + 1)
              (m - slotsMerge P.wsLay.lk)
              (AffSh.mk [] (mergeSlotsAt hp g (sH1 + (1 + P.y.LamM) + 1)
                (if (g == 0) = true then base + slotsGated P else 0)).toList) true
            sFv := m - slotsMerge P.wsLay.lk + (1 + (2 * P.wsLay.lk + 1)), recs := recs } }

/-- **What stays is the closed form.** -/
theorem ownRecord_isClosedForm (hh : hearFl P hp g fo F t = some (o, G, u))
    (hL : HearLeft P hp g fo iU3 tab F G o) :
    ownRecordLessParts (ownSh o) =
      ownRecordClosedForm P hp g iU3 tab (heardAll fo) F.next G.next (o.wo.recs.map recSh) := by
  have N := hL.nums
  obtain ⟨f, f2, hd2, e5, b1, b2, r1, r2⟩ := gatedLayers_rowShapes hh
  have hf : f = F.next + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g) := by
    have := N.hdL
    omega
  have h2a := N.hd2
  rw [e5] at h2a
  have h2b : (hd2.sL, hd2.sR) = _ := Option.some.inj h2a
  have l1 := congrArg Prod.fst h2b
  have l2 := congrArg Prod.snd h2b
  have l1' : hd2.sL = F.next + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g) +
      (1 + (2 * P.rd.muH + (2 + 2))) + (1 + (2 * P.rd.muH2 + 2)) := l1
  have l2' : hd2.sR = F.next + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g) +
      (1 + (2 * P.rd.muH + (2 + 2))) + (1 + (2 * P.rd.muH2 + 2)) + 1 := l2
  have hf2 : f2 = F.next + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g) +
      (1 + (2 * P.rd.muH + (2 + 2))) := by omega
  have h2c := hL.hd2
  rw [e5] at h2c
  have l3 : hd2.r.size = P.rd.muH2 := Option.some.inj h2c
  have hw : o.wo.p.first = G.next - slotsMerge P.wsLay.lk := by
    have := hL.woFirst
    omega
  have hsH : o.K.sH1 = F.next + slotsNorms P + slotsTerms P + (1 + (2 * hp.lamS + 2)) + 1 := by
    rw [N.sH1, N.sA0]
  have hsV : o.K.sV = F.next + slotsNorms P + slotsTerms P + (1 + (2 * hp.lamS + 2)) + 1 +
      (1 + P.y.LamM) + 1 := by
    rw [N.sV, N.sB0, hsH]
  have hsE : o.sVE = if (g == 0) = true then F.next + slotsNorms P + slotsTerms P +
      slotsStack P hp.lamS (nclp hp g) + slotsGated P else 0 := by
    by_cases hg : (g == 0) = true
    · rw [if_pos hg]
      exact N.sVE hg
    · rw [if_neg hg]
      obtain ⟨-, -, -, -, H1, hd2', cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, -, -, -, -, -, mf,
        -⟩ := hear_parts hh
      unfold mergeFront at mf
      rw [if_neg hg] at mf
      exact mf.1
  have hms : mergeSlots hp g o = mergeSlotsAt hp g o.K.sV o.sVE := rfl
  unfold ownRecordLessParts ownRecordClosedForm ownSh levelSh mergeSh
  dsimp only
  rw [norms_isClosedForm hh hL, stack_isClosedForm hh hL, hL.v, e5, hL.hd, N.hdR, N.hdL, r1, hf,
      mergeSumcheck_openShape hh, hms,
    hw, hL.sFv, hw, N.rm, hsV, hsE, hsH]
  show _ = _
  simp only [Option.map_some, l1', l2', l3, r2, hf2, hsH]
  rfl

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.emptyForm
#print axioms OnBytes.Desc.First.K4.Rt.bareSumcheckShape
#print axioms OnBytes.Desc.First.K4.Rt.lookupRecordLessParts
#print axioms OnBytes.Desc.First.K4.Rt.normsLessParts
#print axioms OnBytes.Desc.First.K4.Rt.stackLessParts
#print axioms OnBytes.Desc.First.K4.Rt.ownRecordLessParts
#print axioms OnBytes.Desc.First.K4.Rt.normsClosedForm
#print axioms OnBytes.Desc.First.K4.Rt.norms_isClosedForm
#print axioms OnBytes.Desc.First.K4.Rt.stackClosedForm
#print axioms OnBytes.Desc.First.K4.Rt.stack_isClosedForm
#print axioms OnBytes.Desc.First.K4.Rt.mergeSlotsAt
#print axioms OnBytes.Desc.First.K4.Rt.ownRecordClosedForm
#print axioms OnBytes.Desc.First.K4.Rt.ownRecord_isClosedForm
