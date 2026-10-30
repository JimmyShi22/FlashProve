-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/NormsRun.lean: the norms' stretch of the layers' own rounds as A RUN OF THE
PER-POSITION BRIDGE (OnBytes/Desc/First/NormBridge/BridgeWorld.lean: `D6.Bridge.Run`): its letters
as functions of the public record, the ledger in front, the tape and what was heard; and the
premises on a run that the hearing pays. Definitions, statements and proofs.

  `sumsOf`, `rhoIOf`, `ledgerS`: the sums that round k0 sent; the point that round k0 + 1 drew; the
    ledger behind the sums.
  `hearNorms_at0`, `hearNorms_at`: `hearNorms_tape` with these functions in the place of its
    letters; the second of a record that differs from the stretch's own in the fields tT and KT
    alone, which the next stretch fills: the whole hearing returns such a record, so every
    statement below is typed of one.
  `norms_chain0`, `norms_chain`: the ledgers of the stretch, one later than the other, their arrays
    of the right sizes.
  `runD6`: the run.
  `runD6_formsTie`, `runD6_constsTie`: the two ties of NormsFormsZero.lean and NormsConsts.lean.
  `runD6_gp`, `runD6_om`: the two arrays of powers read as powers of the run's gam and om.
  `runD6_shapes`: `Run.Shapes`.
  `shownRun_get`, `sh_tape`: the products' end values as the run of claims reads them are what the
    tape's values round sent.
  `masksOf`, `runD6_ledger`: `Run.Ledger`, at the masks made of the mask entries at the slots'
    numbers.

One direction: from a return. No law of a sumcheck is applied here, no form is said to be worth 0,
and nothing is said of a bad draw.
-/
import OnBytes.Desc.First.K4.NormsTape
import Johnson.Road.K4.NormsConsts
import OnBytes.Desc.First.P1.Heard
import OnBytes.Desc.First.P1.OrderDefault

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled hideRun_ok)
open OnBytes.Desc.First.P1 (tapeEps tapeEps_cons tapeMu tapeMu2 levelRec levelMs levelY tscMs tscY
  levelIn_heard level_world tscIn_heard tsc_world own_slots tsc_walk levelWs tscWs levelVals
  tscVals level_shown tsc_shown)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ### What is read off the tape -/

/-- What round k0 has to send: the norms' sums. -/
def sumsOf (g : Nat) (t : Tape) : Array E :=
  (((t.drop (k0 g)).head?.map (·.sent)).getD []).toArray

/-- What round k0 + 1 drew: the point over the norms' numbers. -/
def rhoIOf (g : Nat) (t : Tape) : Array E :=
  (((t.drop (k0 g + 1)).head?.map (·.drawn)).getD []).toArray

/-- The ledger behind the sums. -/
def ledgerS (P : Pub) (g : Nat) (F : Fork) (t : Tape) : Fork :=
  (({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork).hideRun F.next (sumsOf g t)
    oneE).getD F

theorem sent_cons (nm : Option String) (z w : Nat) (s d : List E) (u : Tape) :
    (((⟨nm, z, w, s, d⟩ :: u : Tape).head?.map (·.sent)).getD []) = s := rfl

theorem drawn_cons (nm : Option String) (z w : Nat) (s d : List E) (u : Tape) :
    (((⟨nm, z, w, s, d⟩ :: u : Tape).head?.map (·.drawn)).getD []) = d := rfl

/-- **The norms' stretch, its letters read off the tape.** -/
theorem hearNorms_at0 {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H : Heard} (h : hearNorms engFl P g fo F t = some (H, G, u)) :
    ∃ (F7 F8 : Fork) (vP : Array E),
      H.PV.size = P.y.h.lt ∧ H.sW = F.next ∧
      (sumsOf g t).size = ledNS P.y.h.xl * P.y.NI ∧
      ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork).hideRun F.next (sumsOf g t)
        oneE = some (ledgerS P g F t) ∧
      H.gp = powers (tapeEps (t.drop (k0 g))) (ledNS P.y.h.xl) ∧
      (rhoIOf g t).size = P.rd.lNI ∧
      Fl.levelIn P.rd.muV (normsStart P.y H.sW H.gp (rhoIOf g t) H.PV).2
          (normsStart P.y H.sW H.gp (rhoIOf g t) H.PV).1 (orderDefault P.rd.muV)
          (ledgerS P g F t) (t.drop (k0 g + 2)) =
        some (H.wpl, F7, t.drop (k0 g + P.rd.muV + 6)) ∧
      vP.size = ledNP P.y.h.xl * P.y.NI ∧ H.sPv = F7.next ∧
      ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork).hideRun F7.next vP oneE =
        some F8 ∧
      H.omV = powers (tapeEps (t.drop (k0 g + P.rd.muV + 6))) (ledNP P.y.h.xl * P.y.NI) ∧
      Fl.tscIn H.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8 (t.drop (k0 g + P.rd.muV + 7)) =
        some (H.tV, G, u) := by
  obtain ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, e0, l0, hPV, e3, hvW, hsW, hF4, hgp,
    e5, lI, hrho, c7, e7, hvP, hsPv, hF8, hom, c10, _⟩ := hearNorms_tape h
  have s1 : sumsOf g t = vW := by
    unfold sumsOf
    rw [e3, sent_cons, Array.toArray_toList]
  have s2 : rhoIOf g t = rhoI := by
    unfold rhoIOf
    rw [e5, drawn_cons, hrho]
  have s3 : ledgerS P g F t = F4 := by
    unfold ledgerS
    rw [s1, hF4, Option.getD_some]
  have s4 : tapeEps (t.drop (k0 g)) = gam := by rw [e3, tapeEps_cons]
  have s5 : tapeEps (t.drop (k0 g + P.rd.muV + 6)) = om := by rw [e7, tapeEps_cons]
  rw [s1, s2, s3, s4, s5]
  refine ⟨F7, F8, vP, ?_, hsW, hvW, hF4, hgp, ?_, c7, hvP, hsPv, hF8, hom, c10⟩
  · rw [hPV]
    exact l0
  · rw [hrho]
    exact lI

/-- The same of a record H that differs from what the stretch returns in the two fields alone that
the next stretch fills. The whole hearing returns such a record. -/
theorem hearNorms_at {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H1 H : Heard} {a : Option Tsc} {b : Aff} (h : hearNorms engFl P g fo F t = some (H1, G, u))
    (hH : H = { H1 with tT := a, KT := b }) :
    ∃ (F7 F8 : Fork) (vP : Array E),
      H.PV.size = P.y.h.lt ∧ H.sW = F.next ∧
      (sumsOf g t).size = ledNS P.y.h.xl * P.y.NI ∧
      ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork).hideRun F.next (sumsOf g t)
        oneE = some (ledgerS P g F t) ∧
      H.gp = powers (tapeEps (t.drop (k0 g))) (ledNS P.y.h.xl) ∧
      (rhoIOf g t).size = P.rd.lNI ∧
      Fl.levelIn P.rd.muV (normsStart P.y H.sW H.gp (rhoIOf g t) H.PV).2
          (normsStart P.y H.sW H.gp (rhoIOf g t) H.PV).1 (orderDefault P.rd.muV)
          (ledgerS P g F t) (t.drop (k0 g + 2)) =
        some (H.wpl, F7, t.drop (k0 g + P.rd.muV + 6)) ∧
      vP.size = ledNP P.y.h.xl * P.y.NI ∧ H.sPv = F7.next ∧
      ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork).hideRun F7.next vP oneE =
        some F8 ∧
      H.omV = powers (tapeEps (t.drop (k0 g + P.rd.muV + 6))) (ledNP P.y.h.xl * P.y.NI) ∧
      Fl.tscIn H.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8 (t.drop (k0 g + P.rd.muV + 7)) =
        some (H.tV, G, u) := by
  subst hH
  exact hearNorms_at0 (H := H1) h

include ρ in
/-- **The ledgers of the stretch.** -/
theorem norms_chain0 {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H : Heard} (hF : Sized F) (h : hearNorms engFl P g fo F t = some (H, G, u)) :
    ∃ (F7 F8 : Fork),
      Sized (ledgerS P g F t) ∧ (ledgerS P g F t).next = F.next + ledNS P.y.h.xl * P.y.NI ∧
      Fl.levelIn P.rd.muV (normsStart P.y H.sW H.gp (rhoIOf g t) H.PV).2
          (normsStart P.y H.sW H.gp (rhoIOf g t) H.PV).1 (orderDefault P.rd.muV)
          (ledgerS P g F t) (t.drop (k0 g + 2)) =
        some (H.wpl, F7, t.drop (k0 g + P.rd.muV + 6)) ∧
      Sized F8 ∧ Fo.Later F7 F8 ∧ F8.next = F7.next + ledNP P.y.h.xl * P.y.NI ∧
      Fl.tscIn H.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8 (t.drop (k0 g + P.rd.muV + 7)) =
        some (H.tV, G, u) := by
  obtain ⟨F7, F8, vP, _, _, _, hF4, _, _, c7, _, _, hF8, _, c10⟩ := hearNorms_at0 h
  have hF' : Sized ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  obtain ⟨hSa, hS4, _, _⟩ := hideRun_ok _ _ F.next _ oneE hF' hF4
  obtain ⟨_, hS7, _, _⟩ := level_world ρ (fun _ => 0) (fun _ _ _ => 0) hS4 c7
  have hF7' : Sized ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork) := hS7
  have l0 : Fo.Later F7 ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork) :=
    ⟨by show F7.next ≤ F7.next + ledNP P.y.h.xl * P.y.NI; omega, rfl,
      fun _ hj => ⟨hj, rfl, rfl⟩⟩
  obtain ⟨hSb, hS8, _, _⟩ := hideRun_ok _ _ F7.next _ oneE hF7' hF8
  exact ⟨F7, F8, hS4, hSa.next, c7, hS8, l0.trans (Fo.hideRun_later hF7' hF8), hSb.next, c10⟩

include ρ in
/-- The same of a record that differs in the two fields alone that the next stretch fills. -/
theorem norms_chain {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H1 H : Heard} {a : Option Tsc} {b : Aff} (hF : Sized F)
    (h : hearNorms engFl P g fo F t = some (H1, G, u)) (hH : H = { H1 with tT := a, KT := b }) :
    ∃ (F7 F8 : Fork),
      Sized (ledgerS P g F t) ∧ (ledgerS P g F t).next = F.next + ledNS P.y.h.xl * P.y.NI ∧
      Fl.levelIn P.rd.muV (normsStart P.y H.sW H.gp (rhoIOf g t) H.PV).2
          (normsStart P.y H.sW H.gp (rhoIOf g t) H.PV).1 (orderDefault P.rd.muV)
          (ledgerS P g F t) (t.drop (k0 g + 2)) =
        some (H.wpl, F7, t.drop (k0 g + P.rd.muV + 6)) ∧
      Sized F8 ∧ Fo.Later F7 F8 ∧ F8.next = F7.next + ledNP P.y.h.xl * P.y.NI ∧
      Fl.tscIn H.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8 (t.drop (k0 g + P.rd.muV + 7)) =
        some (H.tV, G, u) := by
  subst hH
  exact norms_chain0 ρ (H := H1) hF h

/-! ### The run -/

/-- The run of the per-position bridge that the norms' stretch has heard. F: the ledger in front;
o: what was heard, with the caller's environment; sh: the products' end values as the run of claims
reads them off its ledger. What was shown for the squares' two end values is read off the tape. -/
def runD6 (P : Pub) (g : Nat) (F : Fork) (t : Tape) (o : Own) (sh : Array E) : D6.Bridge.Run where
  PE := o.H.PV.toList
  sW := o.H.sW
  gam := tapeEps (t.drop (k0 g))
  zsS := (normsStart P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV).2.toList
  half := invE (ofNat 2)
  S :=
    { p := levelRec P.rd.muV (normsStart P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV).2
        (normsStart P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV).1 (orderDefault P.rd.muV)
        (ledgerS P g F t) (t.drop (k0 g + 2))
      mu := tapeMu (t.drop (k0 g + 2))
      ms := levelMs P.rd.muV (normsStart P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV).2
        (orderDefault P.rd.muV) (t.drop (k0 g + 2))
      y := levelY P.rd.muV (t.drop (k0 g + 2))
      S0 := mulE ((levelVals P.rd.muV (t.drop (k0 g + 2))).getD 0 zeroE)
        ((levelVals P.rd.muV (t.drop (k0 g + 2))).getD 1 zeroE) }
  sL := o.H.wpl.sL
  shS := fun e => (levelVals P.rd.muV (t.drop (k0 g + 2))).getD e zeroE
  XS := XSof P o.v o.H
  sPv := o.H.sPv
  om := tapeEps (t.drop (k0 g + P.rd.muV + 6))
  sCl := o.H.tV.sCl
  Pr :=
    { p := o.H.tV.p
      mu := tapeMu2 (t.drop (k0 g + P.rd.muV + 7))
      ms := tscMs o.H.PV P.y.h.lt (t.drop (k0 g + P.rd.muV + 7))
      y := tscY o.H.PV P.y.h.lt 2 (t.drop (k0 g + P.rd.muV + 7))
      S0 := rowsSummand P.y o.H sh }
  sE := o.H.tV.sEnd
  shP := fun e => sh.getD e zeroE
  D := digitsOr o.v "P_V"
  D' := digitsOr o.v "r_tV"
  eps := epsOf o.v.y
  two := twoM o.v

include ρ in
/-- **The tie of NormsFormsZero.lean.** -/
theorem runD6_formsTie {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {o : Own} (sh : Array E) (hF : Sized F)
    {H1 : Heard} {a : Option Tsc} {b : Aff}
    (h : hearNorms engFl P g fo F t = some (H1, G, u)) (hH : o.H = { H1 with tT := a, KT := b }) :
    FormsTie (runD6 P g F t o sh) P o sh := by
  obtain ⟨F7, F8, hS4, _, c7, hS8, l78, _, c10⟩ := norms_chain ρ hF h hH
  obtain ⟨_, _, _, hw⟩ := level_world ρ (fun _ => 0) (fun _ _ _ => 0) hS4 c7
  obtain ⟨l8G, _⟩ := tsc_world ρ (fun _ => 0) (fun _ _ _ => 0) hS8 c10
  have hrow := (hw G (l78.trans l8G)).2.2.1
  have s0 := level_shown hS4 c7 G (l78.trans l8G) 0 (by omega)
  have s1 := level_shown hS4 c7 G (l78.trans l8G) 1 (by omega)
  rw [Nat.add_zero] at s0
  rw [s0, s1] at hrow
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsR, _⟩ := levelIn_heard c7
  exact { sW := rfl, sL := rfl, sR := hsR, rowS := hrow.symm, XS := rfl, sPv := rfl, sCl := rfl,
          rowP := rfl, sE := rfl, D := rfl, D' := rfl, eps := rfl, two := rfl }

include ρ in
/-- **The tie of NormsConsts.lean.** -/
theorem runD6_constsTie {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {o : Own} (sh : Array E) (hF : Sized F)
    {H1 : Heard} {a : Option Tsc} {b : Aff}
    (h : hearNorms engFl P g fo F t = some (H1, G, u)) (hH : o.H = { H1 with tT := a, KT := b }) :
    ConstsTie (runD6 P g F t o sh) P o sh (rhoIOf g t) := by
  obtain ⟨F7, F8, _, _, c7, _, _, _, c10⟩ := norms_chain ρ hF h hH
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hstart, _⟩ := levelIn_heard c7
  obtain ⟨_, _, _, _, _, _, _, _, _, hst, hsCl, _⟩ := tscIn_heard c10
  have hP : o.H.tV.p.start = Aff.slot o.H.tV.sCl := by rw [hst, hsCl]
  exact { half := rfl, sW := rfl, startS := hstart, startP := hP, endS := rfl, endP := rfl,
          shP := rfl, eps := rfl, two := rfl }

/-- The first array of powers reads as the powers of the run's gam. -/
theorem runD6_gp {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}
    (sh : Array E) {H1 : Heard} {a : Option Tsc} {b : Aff}
    (h : hearNorms engFl P g fo F t = some (H1, G, u)) (hH : o.H = { H1 with tT := a, KT := b }) :
    ∀ s, s < ledNS P.y.h.xl →
      ρ.val (o.H.gp.getD s zeroE) = ρ.val (runD6 P g F t o sh).gam ^ s := by
  obtain ⟨_, _, _, _, _, _, _, hgp, _⟩ := hearNorms_at h hH
  intro s hs
  rw [hgp]
  exact P1.powers_val ρ _ _ _ hs

/-- The second array of powers reads as the powers of the run's om. -/
theorem runD6_om {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}
    (sh : Array E) {H1 : Heard} {a : Option Tsc} {b : Aff}
    (h : hearNorms engFl P g fo F t = some (H1, G, u)) (hH : o.H = { H1 with tT := a, KT := b }) :
    ∀ m, m < ledNP P.y.h.xl * P.y.NI →
      ρ.val (o.H.omV.getD m zeroE) = ρ.val (runD6 P g F t o sh).om ^ m := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hom, _⟩ := hearNorms_at h hH
  intro m hm
  rw [hom]
  exact P1.powers_val ρ _ _ _ hm

/-! ### Shapes -/

theorem getD_three_mid {α : Type} (A B C : List α) (d : α) (i : Nat) (h : i < B.length) :
    ((A ++ B) ++ C).getD (A.length + i) d = B.getD i d := by
  rw [P1.getD_append_left _ _ _ _ (by rw [List.length_append]; omega), P1.getD_append_right]

theorem getD_three_last {α : Type} (A B C : List α) (d : α) (i : Nat) :
    ((A ++ B) ++ C).getD (A.length + B.length + i) d = C.getD i d := by
  have e : A.length + B.length = (A ++ B).length := by rw [List.length_append]
  rw [e, P1.getD_append_right]

/-- The squares' point: rhoI, then lPd times the half, then PV. -/
theorem normsStart_point (y : Lay) (sW : Nat) (gp rhoI PV : Array E) :
    (normsStart y sW gp rhoI PV).2.toList =
      (rhoI.toList ++ List.replicate y.lPd (invE (ofNat 2))) ++ PV.toList := by
  simp [normsStart]

/-- **`Run.Shapes`.** The three conditions tie the data's sizes to the public record's. -/
theorem runD6_shapes {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}
    (sh : Array E) (c : D6.Bridge.Data K) (hF : Sized F)
    {H1 : Heard} {a : Option Tsc} {b : Aff}
    (h : hearNorms engFl P g fo F t = some (H1, G, u)) (hH : o.H = { H1 with tT := a, KT := b })
    (hlt : c.lt = P.y.h.lt) (hlNI : c.lNI = P.rd.lNI)
    (hmu : P.rd.muV = P.rd.lNI + P.y.lPd + P.y.h.lt) :
    (runD6 P g F t o sh).Shapes ρ c P.y.lPd := by
  obtain ⟨_, _, _, hPV, _, _, _, _, hrho, _⟩ := hearNorms_at h hH
  obtain ⟨F7, F8, _, _, c7, _, _, _, c10⟩ := norms_chain ρ hF h hH
  obtain ⟨_, _, _, a1, hy, _, hlens, hvars, hr, hclaim, _⟩ := levelIn_heard c7
  obtain ⟨_, b1, by1, _, blens, bvars, br, bclaim, _⟩ := tscIn_heard c10
  have hPVl : o.H.PV.toList.length = P.y.h.lt := hPV
  have hrhol : (rhoIOf g t).toList.length = P.rd.lNI := hrho
  have hpt := normsStart_point P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV
  have hsize : (normsStart P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV).2.size = P.rd.muV := by
    show (normsStart P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV).2.toList.length = P.rd.muV
    rw [hpt, List.length_append, List.length_append, List.length_replicate, hrhol, hPVl, hmu]
  have hws := P1.levelWs_default P.rd.muV _ hsize
  have hmap : (runD6 P g F t o sh).zsS.map ρ.val =
      ((rhoIOf g t).toList.map ρ.val ++ List.replicate P.y.lPd (ρ.val (invE (ofNat 2)))) ++
        o.H.PV.toList.map ρ.val := by
    show ((normsStart P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV).2.toList).map ρ.val = _
    rw [hpt, List.map_append, List.map_append, List.map_replicate]
  have hA : ((rhoIOf g t).toList.map ρ.val).length = c.lNI := by
    rw [List.length_map, hrhol, hlNI]
  have hB : (List.replicate P.y.lPd (ρ.val (invE (ofNat 2)))).length = P.y.lPd :=
    List.length_replicate
  have htake : o.H.PV.toList.take P.y.h.lt = o.H.PV.toList :=
    List.take_of_length_le (le_of_eq hPVl)
  refine { lenP := ?_, lenS := ?_, mid := ?_, last := ?_, sq := ?_, pr := ?_ }
  · show o.H.PV.toList.length = c.lt
    rw [hPVl, hlt]
  · show (normsStart P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV).2.toList.length = _
    rw [hpt, List.length_append, List.length_append, List.length_replicate, hrhol, hPVl, hlNI,
      hlt]
  · intro j hj
    show ((runD6 P g F t o sh).zsS.map ρ.val).getD (c.lNI + j) 0 = ρ.val (invE (ofNat 2))
    rw [hmap, ← hA, getD_three_mid _ _ _ _ _ (by rw [hB]; exact hj),
      P1.getD_replicate' _ _ _ _ hj]
  · intro j _
    show ((runD6 P g F t o sh).zsS.map ρ.val).getD (c.lNI + P.y.lPd + j) 0 =
      (o.H.PV.toList.map ρ.val).getD j 0
    have e := getD_three_last ((rhoIOf g t).toList.map ρ.val)
      (List.replicate P.y.lPd (ρ.val (invE (ofNat 2)))) (o.H.PV.toList.map ρ.val) 0 j
    rw [hA, hB] at e
    rw [hmap]
    exact e
  · rw [hws] at hvars
    exact { weights := a1.trans hws, further := hy, lengths := hlens, vars := hvars, chals := hr,
            claim := hclaim }
  · rw [htake] at b1 bvars
    exact { weights := b1, further := by1, lengths := blens, vars := bvars, chals := br,
            claim := bclaim }

/-! ### The ledger -/

/-- Member e of a run of shown values is what the ledger shows under slot first + e. -/
theorem shownRun_get {F : Fork} {first n : Nat} {sh : Array E}
    (h : ((Array.range n).mapM fun i => F.shown (first + i)) = some sh) {e : Nat} (he : e < n) :
    F.shown (first + e) = some (sh.getD e zeroE) := by
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at h
  cases hl : (List.range n).mapM (fun i => F.shown (first + i)) with
  | none =>
    rw [hl] at h
    simp at h
  | some L =>
    rw [hl] at h
    have hL : L.toArray = sh := by simpa using h
    obtain ⟨b, hb, gb⟩ := mapM_range_get _ hl he
    rw [hb, ← hL]
    simp [Array.getD_eq_getD_getElem?, gb]

include ρ in
/-- The products' end values, as the run of claims reads them off a ledger later than the hearing's,
are what the tape's values round sent. -/
theorem sh_tape {P : Pub} {g : Nat} {fo : Forest.Heard} {F G G1 : Fork} {t u : Tape}
    {H1 H : Heard} {a : Option Tsc} {b : Aff} {sh : Array E} (hF : Sized F)
    (h : hearNorms engFl P g fo F t = some (H1, G, u)) (hH : H = { H1 with tT := a, KT := b })
    (lG : Fo.Later G G1)
    (hsh : ((Array.range (4 * P.y.NI)).mapM fun i => G1.shown (H.tV.sEnd + i)) = some sh)
    (hNO : ledNO P.y.h.xl = 4) :
    ∀ e, e < 4 * P.y.NI → sh.getD e zeroE =
      (tscVals H.PV P.y.h.lt (t.drop (k0 g + P.rd.muV + 7))).getD e zeroE := by
  obtain ⟨F7, F8, _, _, _, hS8, _, _, c10⟩ := norms_chain ρ hF h hH
  intro e he
  rw [(P1.shown_some (shownRun_get hsh he)).2.2]
  exact tsc_shown hS8 c10 G1 lG e (by rw [hNO]; exact he)

/-- The mask entries beneath the two sumchecks, at the slots' numbers. -/
def masksOf (mask : ℕ → K) (H : Heard) (first : Nat) : D6.Bridge.Masks K where
  hS := fun i => mask (first + i)
  mS := fun e => mask (H.wpl.sL + e)
  hP := fun i => mask (H.tV.p.first + i)
  mP := fun e => mask (H.tV.sEnd + e)

/-- **`Run.Ledger`.** G: the ledger behind the hearing. G1, G2: the ledgers in front of and behind
the step that makes the products' row. Hl: a ledger later than G2. sh: what G1 shows under the
products' end values' slots. -/
theorem runD6_ledger (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) {P : Pub} {g : Nat}
    {fo : Forest.Heard} {F G G1 G2 Hl : Fork} {t u : Tape} {o : Own} {sh : Array E}
    (c : D6.Bridge.Data K) (hF : Sized F)
    {H1 : Heard} {a : Option Tsc} {b : Aff}
    (h : hearNorms engFl P g fo F t = some (H1, G, u)) (hH : o.H = { H1 with tT := a, KT := b })
    (lG : Fo.Later G G1) (hG1 : Sized G1)
    (hrow : G1.hideRun o.H.tV.p.first (Array.replicate o.H.tV.p.walk.1.length zeroE)
      (subE zeroE oneE) = some G2)
    (lH : Fo.Later G2 Hl)
    (hsh : ((Array.range (4 * P.y.NI)).mapM fun i => G1.shown (o.H.tV.sEnd + i)) = some sh)
    (hNI : c.NI = P.y.NI)
    (hNO : ledNO P.y.h.xl * P.y.NI = 4 * c.NI)
    (hmu : P.rd.muV = P.rd.lNI + P.y.lPd + P.y.h.lt) :
    (runD6 P g F t o sh).Ledger ρ c
      (masksOf mask o.H (F.next + ledNS P.y.h.xl * P.y.NI)) (Hl.worldOf ρ mask entry) := by
  obtain ⟨_, _, _, hPV, _, _, _, _, hrho, _⟩ := hearNorms_at h hH
  obtain ⟨F7, F8, hS4, hn4, c7, hS8, l78, _, c10⟩ := norms_chain ρ hF h hH
  obtain ⟨_, _, _, hw⟩ := level_world ρ mask entry hS4 c7
  obtain ⟨l8G, _, _, _, _, _, hfill, hv⟩ := tsc_world ρ mask entry hS8 c10
  obtain ⟨l12, _, hown⟩ := own_slots ρ mask entry hG1 hrow
  have lGH : Fo.Later G Hl := (lG.trans l12).trans lH
  obtain ⟨w1, w2, _, _⟩ := hw Hl ((l78.trans l8G).trans lGH)
  obtain ⟨_, v2⟩ := hv Hl lGH
  have hPVl : o.H.PV.toList.length = P.y.h.lt := hPV
  have hrhol : (rhoIOf g t).toList.length = P.rd.lNI := hrho
  have hpt := normsStart_point P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV
  have hsize : (normsStart P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV).2.size = P.rd.muV := by
    show (normsStart P.y o.H.sW o.H.gp (rhoIOf g t) o.H.PV).2.toList.length = P.rd.muV
    rw [hpt, List.length_append, List.length_append, List.length_replicate, hrhol, hPVl, hmu]
  have hws := P1.levelWs_default P.rd.muV _ hsize
  have htake : o.H.PV.toList.take P.y.h.lt = o.H.PV.toList :=
    List.take_of_length_le (le_of_eq hPVl)
  have hwalk := tsc_walk c10
  rw [htake] at hwalk
  refine { hidS := ?_, hidP := ?_, shownS := ?_, shownP := ?_ }
  · intro i hi
    have e := w1 i (by rw [hws]; exact hi)
    rw [hn4] at e
    exact e
  · intro i hi
    exact hown Hl lH i (by rw [hwalk]; exact hi)
  · intro e he
    show ρ.val ((levelVals P.rd.muV (t.drop (k0 g + 2))).getD e zeroE) = _
    rw [← level_shown hS4 c7 Hl ((l78.trans l8G).trans lGH) e he]
    exact w2 e he
  · intro e he
    have k := v2 e (by rw [hNO]; exact he)
    have k1 := lG.keep _ (hfill e (by rw [hNO]; exact he))
    have k2 := (l12.trans lH).keep _ k1.1
    show ρ.val (sh.getD e zeroE) = _
    rw [(P1.shown_some (shownRun_get hsh (by rw [← hNI]; exact he))).2.2, ← k2.2.1]
    exact k

end OnBytes.Desc.First.K4
