-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/HearFills.lean: BEHIND K4's HEARING, EVERY SLOT THAT A FORM OF K4's TWO RUNS
OF CLAIMS NAMES LIES IN ONE OF THE RUN's OWN WINDOWS OR IS FILLED, in the ledger G that the hearing
hands on and so in every ledger U that keeps what G has filled: FOR "back" OUTRIGHT; FOR "front"
UNDER THREE NAMED PREMISES ON THE LOOKUP's RECORD. Two definitions, and statements with their
proofs: the hearing's chain of calls (`hear_parts`, OnBytes/Desc/First/K4/MergeClaims.lean;
`hearNorms_calls`, `hearTerms_calls`, `hearTerms_keeps`, `hearNorms_public`, same folder), the
calls' laws (Fills.lean, FillsMore.lean), "a plain function leads to a later ledger" (the class
`Grows`, OnBytes/Desc/First/FlGrows.lean, K4/HearGrows.lean) and the structure (FrontBack.lean) laid
together.

  `SFront o U j`: j lies in the window of the row products' token sumcheck or of the lookup's
    leaves' sumcheck (first ≤ j < first + length), or is filled in U. `SBack o U j`: in the merge's
    window, or filled in U.
  `norms_fills`, `terms_fills`, `gated_fills`, `front_fills`: what each stretch of the hearing
  fills.
  `Fills7`, `hear_fills`: these laid together: where `hear` returned (o, G, u) from a ledger with
    arrays of the right sizes: the list of what is filled in G.
  `own_fo`: the lookup's record inside what the hearing returns is the one that it was handed.
  **`hs_back`**: every slot that a form of `back o …` names has `SBack o U`. NO FURTHER PREMISE.
  **`hs_front`**: every slot that a form of `front rows P g o …` names (at any shown values sh) has
    `SFront o U`, under k3, hBit, hLv.
  **`hsh`**: the 4 · NI end values' slots of the row products' token sumcheck are filled in U.
The three bear the names of the premises hs, hs, hsh of «link for proof file»'s K4Values.lean
(`back_values`, `front_values`, `front_forms`), whose `InWin`, `winOf`, `frontWins` stand written
out in `SBack`, `SFront`. That file is not imported here.

Limits. THE THREE PREMISES THAT STAY, each at U, ALL ON THE LOOKUP's RECORD fo, which is heard in
front of K4's stretch: `k3` (the slots of its own claims, if they are listed) · `hBit` (its bit's
slot) · `hLv` (the slots of its leaves' sumcheck's start form). NOTHING HERE SHOWS THEM; at an
arbitrary record fo the fact is false. One direction, from a return. Nothing on entries, on what
lies under a slot, or on soundness.
-/
import Johnson.Road.K4.Slots.FrontBack
import Johnson.Road.K4.Slots.FillsMore
import OnBytes.Desc.First.K4.MergeClaims
import OnBytes.Desc.First.K4.HearGrows
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Desc.First.K4.NormsPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard HeardStack nEndT)
open OnBytes.PscRun (Sized Filled Later)
open OnBytes.Desc.First.Grow (Grows)

/-- In one of the two windows of "front", or filled in U. -/
def SFront (o : Own) (U : Fork) (j : ℕ) : Prop :=
  (∃ w ∈ [(o.H.tV.p.first, o.H.tV.p.walk.1.length),
      (o.H.fo.leaves.first, o.H.fo.leaves.walk.1.length)], w.1 ≤ j ∧ j < w.1 + w.2) ∨ Filled U j

/-- In the window of "back", or filled in U. -/
def SBack (o : Own) (U : Fork) (j : ℕ) : Prop :=
  (o.wo.toWsMerged.p.first ≤ j ∧ j < o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length) ∨
    Filled U j

/-! ### What each stretch of the hearing fills -/

/-- The norms' stretch. -/
theorem norms_fills {P : Pub} {g : ℕ} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {H : Heard}
    (hF : Sized F) (h : hearNorms engFl P g fo F t = some (H, G, u)) :
    Sized G ∧ (∀ j, Filled F j → Filled G j) ∧
      (∀ i, i < ledNS P.y.h.xl * P.y.NI → Filled G (H.sW + i)) ∧
      Filled G H.wpl.sL ∧ Filled G H.wpl.sR ∧ SlotsIn (Filled G) H.wpl.row ∧
      (∀ i, i < ledNP P.y.h.xl * P.y.NI → Filled G (H.sPv + i)) ∧
      Filled G H.tV.sCl ∧ (∀ i, i < ledNO P.y.h.xl * P.y.NI → Filled G (H.tV.sEnd + i)) ∧
      SlotsIn (Filled G) H.tV.p.start := by
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, p1, p2, p3, _, cW,
    bW, rhoI, pI, cL, cP, bP, cT, _⟩ := hearNorms_calls h
  have L1 : Later F F1 := Grows.later p1
  have L2 : Later F1 F2 := Grows.later p2
  have L3 : Later F2 F3 := Grows.later p3
  have L03 := (L1.trans L2).trans L3
  obtain ⟨s4, k4, fW⟩ := claimsIn_fills (L03.sized hF) cW
  have L46 : Later F4 F6 := (Grows.later bW : Later F4 F5).trans (Grows.later pI)
  obtain ⟨s7, k7, l7, r7, row7⟩ := level_fills (L46.sized s4) cL
  obtain ⟨s8, k8, fP⟩ := claimsIn_fills s7 cP
  have L89 : Later F8 F9 := Grows.later bP
  obtain ⟨sG, kG, cl, en, st⟩ := tsc_fills (L89.sized s8) cT
  have k8G : ∀ j, Filled F8 j → Filled G j := fun j hj => kG j (L89.keep j hj).1
  have k7G : ∀ j, Filled F7 j → Filled G j := fun j hj => k8G j (k8 j hj)
  have k4G : ∀ j, Filled F4 j → Filled G j := fun j hj => k7G j (k7 j (L46.keep j hj).1)
  exact ⟨sG, fun j hj => k4G j (k4 j (L03.keep j hj).1), fun i hi => k4G _ (fW i hi), k7G _ l7,
    k7G _ r7, slotsIn_mono k7G row7, fun i hi => k8G _ (fP i hi), cl, en, st⟩

/-- The second token sumcheck's stretch. -/
theorem terms_fills {P : Pub} {H H' : Heard} {F G : Fork} {t u : Tape} (hF : Sized F)
    (h : hearTerms engFl P H F t = some (H', G, u)) :
    Sized G ∧ (∀ j, Filled F j → Filled G j) ∧
      ∀ tT, H'.tT = some tT → ∀ i, i < nEndT P.y → Filled G (tT.sEnd + i) := by
  obtain ⟨tT, G1, u1, row, p', c, _, r, rfl⟩ := hearTerms_calls h
  obtain ⟨s1, k1, _, en, _⟩ := tsc_fills hF c
  have L : Later G1 G := Grows.later r
  refine ⟨L.sized s1, fun j hj => (L.keep j (k1 j hj)).1, fun tT' e i hi => ?_⟩
  obtain rfl := Option.some.inj e
  exact (L.keep _ (en i hi)).1

/-- The gated products' stretch. -/
theorem gated_fills {P : Pub} {H : Heard} {K : HeardStack} {F G : Fork} {t u : Tape}
    {hd hd2 : Level} (hF : Sized F) (h : hearGated engFl P H K F t = some ((hd, hd2), G, u)) :
    Sized G ∧ (∀ j, Filled F j → Filled G j) ∧
      (SlotsIn (Filled G) hd.row ∧ Filled G hd.sL ∧ Filled G hd.sR) ∧
      (SlotsIn (Filled G) hd2.row ∧ Filled G hd2.sL ∧ Filled G hd2.sR) := by
  unfold hearGated at h
  obtain ⟨hd', G1, u1, c1, k1⟩ := P1.bind_some.mp h
  obtain ⟨tT, A1, a1, c2, k2⟩ := P1.bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := P1.need_some.mp c2
  obtain ⟨rhoM, G2, u2, c3, k3⟩ := P1.bind_some.mp k2
  obtain ⟨hd2', G3, u3, c4, k4⟩ := P1.bind_some.mp k3
  obtain ⟨e5, rfl, rfl⟩ := P1.pure_some.mp k4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e5
  obtain ⟨s1, q1, l1, r1, row1⟩ := level_fills hF (L := hd') (G := G1) (u := u1) c1
  have L : Later G1 G2 := Grows.later c3
  obtain ⟨s3, q3, l3, r3, row3⟩ := level_fills (L.sized s1) (L := hd2') (G := G3) (u := u3) c4
  have q13 : ∀ j, Filled G1 j → Filled G3 j := fun j hj => q3 j (L.keep j hj).1
  exact ⟨s3, fun j hj => q13 j (q1 j hj), ⟨slotsIn_mono q13 row1, q13 _ l1, q13 _ r1⟩,
    row3, l3, r3⟩

/-- Between the gated layers and the merge. -/
theorem front_fills {g : ℕ} {o : Own} {G4 G5 : Fork} {u4 u5 : Tape} (h4 : Sized G4)
    (h : mergeFront g o G4 u4 G5 u5) :
    Sized G5 ∧ (∀ j, Filled G4 j → Filled G5 j) ∧ ((g == 0) = true → Filled G5 o.sVE) := by
  unfold mergeFront at h
  by_cases hg : (g == 0) = true
  · rw [if_pos hg] at h
    obtain ⟨s, k, f⟩ := claimsIn_fills h4 h
    exact ⟨s, k, fun _ => by simpa using f 0 (by omega)⟩
  · rw [if_neg hg] at h
    obtain ⟨_, rfl, _⟩ := h
    exact ⟨h4, fun _ hj => hj, fun e => absurd e hg⟩

/-- **What is filled behind the hearing.** -/
structure Fills7 (P : Pub) (hp : HPlan2) (g : ℕ) (o : Own) (G : Fork) : Prop where
  sW : ∀ i, i < ledNS P.y.h.xl * P.y.NI → Filled G (o.H.sW + i)
  wplL : Filled G o.H.wpl.sL
  wplR : Filled G o.H.wpl.sR
  wplRow : SlotsIn (Filled G) o.H.wpl.row
  sPv : ∀ i, i < ledNP P.y.h.xl * P.y.NI → Filled G (o.H.sPv + i)
  tVCl : Filled G o.H.tV.sCl
  tVEnd : ∀ i, i < ledNO P.y.h.xl * P.y.NI → Filled G (o.H.tV.sEnd + i)
  tVStart : SlotsIn (Filled G) o.H.tV.p.start
  tT : ∀ tT, o.H.tT = some tT → ∀ i, i < nEndT P.y → Filled G (tT.sEnd + i)
  stack : ∀ i, i < 2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0)) →
    Filled G (o.K.sA0 + i)
  sB0 : o.K.sB0 = o.K.sA0 + 1 + (1 + P.y.LamM)
  sV : o.K.sV = o.K.sA0 + (2 + (1 + P.y.LamM))
  rowS : SlotsIn (Filled G) o.K.rowS
  hd : SlotsIn (Filled G) o.hd.row ∧ Filled G o.hd.sL ∧ Filled G o.hd.sR
  hd2 : ∀ x, o.hd2 = some x → SlotsIn (Filled G) x.row ∧ Filled G x.sL ∧ Filled G x.sR
  sVE : (g == 0) = true → Filled G o.sVE

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G U : Fork} {t0 u : Tape}

theorem hear_fills (hF : Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u)) :
    Fills7 P hp g o G := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, hN, hT, hS, hG, e2, hM,
    _, _, hE⟩ := hear_parts h
  obtain ⟨s1, _, a1, a2, a3, a4, a5, a6, a7, a8⟩ := norms_fills hF hN
  obtain ⟨s2, k2, b1⟩ := terms_fills s1 hT
  obtain ⟨s3, k3, c1, _, c3, c4, c2⟩ := stack_fills s2 hS
  obtain ⟨s4, k4, d1, d2⟩ := gated_fills s3 hG
  obtain ⟨s5, k5, e1⟩ := front_fills s4 hM
  have L : Later G5 G := Grows.later hE
  have q5 : ∀ j, Filled G5 j → Filled G j := fun j hj => (L.keep j hj).1
  have q4 : ∀ j, Filled G4 j → Filled G j := fun j hj => q5 j (k5 j hj)
  have q3 : ∀ j, Filled G3 j → Filled G j := fun j hj => q4 j (k4 j hj)
  have q2 : ∀ j, Filled G2 j → Filled G j := fun j hj => q3 j (k3 j hj)
  have q1 : ∀ j, Filled G1 j → Filled G j := fun j hj => q2 j (k2 j hj)
  obtain ⟨_, _, _, _, _, w1, _, w2, w3, _, w4⟩ := hearTerms_keeps hT
  exact
    { sW := fun i hi => by rw [w1]; exact q1 _ (a1 i hi)
      wplL := by rw [w2]; exact q1 _ a2
      wplR := by rw [w2]; exact q1 _ a3
      wplRow := by rw [w2]; exact slotsIn_mono q1 a4
      sPv := fun i hi => by rw [w3]; exact q1 _ (a5 i hi)
      tVCl := by rw [w4]; exact q1 _ a6
      tVEnd := fun i hi => by rw [w4]; exact q1 _ (a7 i hi)
      tVStart := by rw [w4]; exact slotsIn_mono q1 a8
      tT := fun tT e i hi => q2 _ (b1 tT e i hi)
      stack := fun i hi => q3 _ (c1 i hi)
      sB0 := c3
      sV := c4
      rowS := slotsIn_mono q3 c2
      hd := ⟨slotsIn_mono q4 d1.1, q4 _ d1.2.1, q4 _ d1.2.2⟩
      hd2 := fun x e => by
        rw [e2] at e
        obtain rfl := Option.some.inj e
        exact ⟨slotsIn_mono q4 d2.1, q4 _ d2.2.1, q4 _ d2.2.2⟩
      sVE := fun hg => q5 _ (e1 hg) }

/-- The lookup's record inside what the hearing returns is the one that it was handed. -/
theorem own_fo (h : hear engFl P hp g fo F t0 = some (o, G, u)) : o.H.fo = fo := by
  obtain ⟨_, H1, G1, u1, G2, u2, h1, h2, _⟩ := hear_calls h
  obtain ⟨_, _, _, _, _, _, _, e1⟩ := hearNorms_public h1
  exact (hearTerms_keeps h2).1.trans e1

/-- The three numbers of a row of five limbs, where K4's text covers the plan. -/
theorem covers_nums (hc : covers P = true) :
    ledNS P.y.h.xl = 9 ∧ ledNP P.y.h.xl = 7 ∧ ledNO P.y.h.xl = 4 ∧ P.y.h.p3 = true := by
  unfold covers at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hx, p3⟩, _⟩, _⟩, _⟩ := hc
  refine ⟨by rw [hx]; rfl, by rw [hx]; rfl, by rw [hx]; rfl, p3⟩

/-- **UNDER k3, hBit, hLv (on the lookup's record): every slot that a form of "front" names lies in
one of its two windows or is filled.** -/
theorem hs_front (hF : Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hU : ∀ j, Filled G j → Filled U j) {rows : Bool}
    (k3 : rows = true → ∀ f ∈ o.H.fo.rows.toList, SlotsIn (Filled U) f)
    (hBit : Filled U o.H.fo.sBit) (hLv : SlotsIn (Filled U) o.H.fo.leaves.start) (sh : Array E)
    {pp : Aff × List Aff} (hpp : planesParts o.v o.H.fo = some pp) {l : List Aff}
    (hl : front rows P g o (o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {})
      (o.H.fo.leaves.rowForm oneE pp.1) = some l) :
    ∀ f ∈ l, ∀ x ∈ f.slots.toList, SFront o U x.1 := by
  obtain ⟨hc, hy, _⟩ := hear_parts h
  obtain ⟨n9, n7, n4, p3⟩ := covers_nums hc
  have A := hear_fills hF h
  have up : ∀ j, Filled G j → SFront o U j := fun j hj => Or.inr (hU j hj)
  have inr : ∀ j, Filled U j → SFront o U j := fun j hj => Or.inr hj
  have eT : nEndT P.y = P.y.NN * P.y.Lam + P.y.LamM + P.y.LamM * P.y.h.NE := by
    unfold nEndT
    rw [if_pos p3, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  refine front_slots (S := SFront o U) ?_ sh hpp hl
  exact
    { k3 := fun hr f hf => slotsIn_mono inr (k3 hr f hf)
      wplRow := slotsIn_mono up A.wplRow
      wplL := up _ A.wplL
      wplR := up _ A.wplR
      tVCl := up _ A.tVCl
      tVEnd := fun j h1 h2 => up j (stretch A.tVEnd j h1 (by rw [n4, ← hy]; exact h2))
      tVWin := fun i hi => Or.inl ⟨_, List.mem_cons_self, Nat.le_add_right _ _,
        Nat.add_lt_add_left hi _⟩
      tVStart := slotsIn_mono up A.tVStart
      sPvB := fun j h1 h2 => up j (stretch A.sPv j h1 h2)
      sPv7 := fun j h1 h2 => up j (stretch A.sPv j h1 (by rw [n7, ← hy]; exact h2))
      sW := fun j h1 h2 => up j (stretch A.sW j h1 (by rw [n9, ← hy]; exact h2))
      tT := fun tT e j h1 h2 => up j (stretch (A.tT tT e) j h1 (by rw [eT, ← hy]; exact h2))
      hdRow := slotsIn_mono up A.hd.1
      hdL := up _ A.hd.2.1
      hdR := up _ A.hd.2.2
      hd2 := fun x e => ⟨slotsIn_mono up (A.hd2 x e).1, up _ (A.hd2 x e).2.1, up _ (A.hd2 x e).2.2⟩
      sBit := Or.inr hBit
      lvWin := fun i hi => Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
        Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩
      lvStart := slotsIn_mono inr hLv
      sVE := fun hg => up _ (A.sVE hg) }

/-- **Every slot that a form of "back" names lies in the merge's window or is filled**, where the
hearing returned from a ledger with arrays of the right sizes. -/
theorem hs_back (hF : Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hU : ∀ j, Filled G j → Filled U j) :
    ∀ f ∈ back o (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {}), ∀ x ∈ f.slots.toList,
      SBack o U x.1 := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, _, _, hS, _, _, _, _, _,
    hE⟩ := hear_parts h
  have A := hear_fills hF h
  have up : ∀ j, Filled G j → SBack o U j := fun j hj => Or.inr (hU j hj)
  obtain ⟨hA, hB⟩ := stack_fin (S := SBack o U) hS
  obtain ⟨rho, hst⟩ := merge_start _ _ _ _ _ _ _ _ hE
  refine back_slots (S := SBack o U) ?_
  refine
    { rowS := slotsIn_mono up A.rowS
      sA0 := up _ (by simpa using A.stack 0 (by omega))
      sB0 := ?_
      Alin := hA
      Blin := hB
      mWin := fun i hi => Or.inl ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩
      mStart := ?_ }
  · rw [A.sB0, Nat.add_assoc]
    exact up _ (A.stack _ (by omega))
  · rw [hst]
    refine slotsIn_wsForkStart _ _ fun j hj => ?_
    unfold mergeSlots at hj
    rw [Array.toList_append, List.mem_append] at hj
    rcases hj with hj | hj
    · simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [A.sV, Nat.add_assoc]
      exact up _ (A.stack _ (by omega))
    · by_cases hg : (g == 0) = true
      · rw [if_pos hg] at hj
        have e : j = o.sVE := by simpa using hj
        rw [e]
        exact up _ (A.sVE hg)
      · rw [if_neg hg] at hj
        simp at hj

/-- **The end values' slots of the row products' token sumcheck are filled.** -/
theorem hsh (hF : Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hU : ∀ j, Filled G j → Filled U j) : ∀ i, i < 4 * P.y.NI → Filled U (o.H.tV.sEnd + i) := by
  obtain ⟨hc, _⟩ := hear_parts h
  obtain ⟨_, _, n4, _⟩ := covers_nums hc
  exact fun i hi => hU _ ((hear_fills hF h).tVEnd i (by rw [n4]; exact hi))

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.hear_fills
#print axioms OnBytes.Desc.First.K4.Slots.own_fo
#print axioms OnBytes.Desc.First.K4.Slots.hs_front
#print axioms OnBytes.Desc.First.K4.Slots.hs_back
#print axioms OnBytes.Desc.First.K4.Slots.hsh
