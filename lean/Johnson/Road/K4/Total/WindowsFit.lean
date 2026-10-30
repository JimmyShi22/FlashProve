-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/WindowsFit.lean: FOUR PARTS OF THE LAW "BEHIND K4's HEARING ITS TWO RUNS OF
CLAIMS RETURN" (the statement: Total/Returns.lean): the marks and the place of the row products'
token sumcheck's window; its end values shown; and THE LEDGER THAT THE HEARING LEAVES HAS `Fit`.
Statements (the parts' own words) and proofs.

  `tsc_ready`: behind a token sumcheck's hearing its sumcheck has the four marks (`tscIn_flags`,
    `tscIn_heard`). **`readyV_part`** : `ReadyVPart`.
  `tsc_free`: behind a token sumcheck's hearing, from a sized ledger whose slots from its next free
    number on are free: no slot of its window is filled (it fills one slot in front of the window
    and a run behind it).
  **`apart_part`** : `ApartPart`: what was heard of the lookup is what was handed in; the window
    lies from F's next free number on, and ends in front of the merge's.
  **`shown_part`** : `ShownPart` (`hear_fills`: the end values are filled behind the hearing).
  `merge_first_lt`: the merge's first slot lies below the number of slots.
  **`fit_behind`** : `FitBehind`.

Limits. From a return of the hearing. "Free from the next free number on" and "the lookup's leaves'
window is there and free, below that number" are premises of `FitBehind`: the first is the table of
joints' item freeAbove, the second the lookup's law's. Nothing on what a form is worth. K04_law, the
law of K4's block itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Total.BackReturns
import OnBytes.Desc.First.P1.TscEnded

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.PscRun (Sized Filled Later)
open OnBytes.Psc (Weight)
open OnBytes.Desc.First.Grow (Grows)
open OnBytes.Desc.First.P1 (tscIn_flags tscIn_heard tscWs)
open OnBytes.Desc.First.K4.Slots (Spares Fresh SameAt run_same win_three tsc_win hear_fills own_fo
  covers_nums hear_fresh hear_wins)
open VerifiableInference.Desc.First.MergeLaw (hear_of_flat mergeHear_inv)

/-- Behind a token sumcheck's hearing its sumcheck has the four marks. -/
theorem tsc_ready {P : Array E} {lt n dY : ℕ} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) : Ready o.p := by
  obtain ⟨hs, _, hm⟩ := tscIn_flags h
  obtain ⟨_, hms, _, _, _, hvars, hr, _⟩ := tscIn_heard h
  have a : o.p.vars.toList.length = (tscWs (P.toList.take lt)).length + 1 := by
    rw [hvars]
    simp
  have b : o.p.r.toList.length = (tscWs (P.toList.take lt)).length + 1 := by
    rw [hr, ← hms]
    simp
  have a' : o.p.vars.size = (tscWs (P.toList.take lt)).length + 1 := by simpa using a
  have b' : o.p.r.size = (tscWs (P.toList.take lt)).length + 1 := by simpa using b
  refine ⟨hm, hs, ?_, by rw [a', b']⟩
  cases e : o.p.vars.isEmpty with
  | false => rfl
  | true =>
    exfalso
    have := Array.isEmpty_iff.mp e
    rw [this] at a'
    simp at a'

/-- Behind a token sumcheck's hearing, from a sized ledger that is free from its next free number
on, no
slot of its window is filled. -/
theorem tsc_free {P : Array E} {lt n dY : ℕ} {F G : Fork} {t u : Tape} {o : Tsc} (hF : Sized F)
    (hfree : ∀ j, F.next ≤ j → ¬ Filled F j) (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    ∀ i, i < o.p.walk.1.length → ¬ Filled G (o.p.first + i) := by
  obtain ⟨_, _, _, _, _, hvars, _, _, _, _, _, _, _, v, G0, r0, _, hfirst, hsEnd, hvn, r1⟩ :=
    tscIn_heard h
  have h3 : ∀ w ∈ tscWs (P.toList.take lt), w.d = 3 := fun w hw => by
    unfold tscWs at hw
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw
    rfl
  have hl : (tscWs (P.toList.take lt)).length = (P.toList.take lt).length := by
    unfold tscWs
    rw [List.length_map]
  have hw := win_three _ _ dY h3 hvars
  rw [hl] at hw
  obtain ⟨s0, n0, q0⟩ := run_same (show Sized ({ F with next := F.next + 1 } : Fork) from hF) r0
  obtain ⟨_, _, q1⟩ := run_same (show Sized ({ G0 with
    next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork) from s0) r1
  have n0' : G0.next = F.next + 1 := n0
  intro i hi hfil
  have a : SameAt F G0 (o.p.first + i) := q0 _ (Or.inr (by
    show F.next + 1 ≤ o.p.first + i
    omega))
  have b : SameAt G0 G (o.p.first + i) := q1 _ (Or.inl (by omega))
  exact hfree (o.p.first + i) (by omega) ((a.trans b).1.mp hfil)

theorem readyV_part : ReadyVPart := by
  intro P hp g fo F G t u o h
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, hN, hT, _⟩ :=
    hear_parts h
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, _, _, _, _, _,
    _, rhoI, _, _, _, _, cT, _⟩ := hearNorms_calls hN
  have eV : o.H.tV = H1.tV := (hearTerms_keeps hT).2.2.2.2.2.2.2.2.2.2
  rw [eV]
  exact tsc_ready cT

/-- The stages' ledgers: what the proofs below read of the hearing. -/
theorem stages {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork}
    {t u : Tape} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    ∃ (F9 G1 G5 : Fork) (t9 u1 u5 : Tape) (PV : Array E) (n : ℕ) (cl : Array WsClaim)
      (sv : Array ℕ),
      Sized F9 ∧ Fresh F F9 ∧ Fl.tscIn PV P.y.h.lt n 2 F9 t9 = some (o.H.tV, G1, u1) ∧
      Sized G1 ∧ Sized G5 ∧ Fresh G1 G5 ∧ flatForkEnd P.wsLay cl sv G5 u5 = some (o.wo, G, u) := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, hN, hT, hS, hG, _, hM,
    _, _, hE⟩ := hear_parts h
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, p1, p2, p3, _, cW,
    bW, rhoI, pI, cL, cP, bP, cT, _⟩ := hearNorms_calls hN
  obtain ⟨a1, b1⟩ := Spares.fresh p1 hF
  obtain ⟨a2, b2⟩ := Spares.fresh p2 a1
  obtain ⟨a3, b3⟩ := Spares.fresh p3 a2
  obtain ⟨a4, b4⟩ := Spares.fresh cW a3
  obtain ⟨a5, b5⟩ := Spares.fresh bW a4
  obtain ⟨a6, b6⟩ := Spares.fresh pI a5
  obtain ⟨a7, b7⟩ := Spares.fresh cL a6
  obtain ⟨a8, b8⟩ := Spares.fresh cP a7
  obtain ⟨a9, b9⟩ := Spares.fresh bP a8
  obtain ⟨s1, _⟩ := Spares.fresh cT a9
  obtain ⟨s2, f2⟩ := Spares.fresh hT s1
  obtain ⟨s3, f3⟩ := Spares.fresh hS s2
  obtain ⟨s4, f4⟩ := Spares.fresh hG s3
  obtain ⟨s5, f5⟩ : Sized G5 ∧ Fresh G4 G5 := by
    unfold mergeFront at hM
    by_cases hg : (g == 0) = true
    · rw [if_pos hg] at hM
      exact Spares.fresh hM s4
    · rw [if_neg hg] at hM
      obtain ⟨_, rfl, _⟩ := hM
      exact ⟨s4, Fresh.refl _⟩
  have eV : o.H.tV = H1.tV := (hearTerms_keeps hT).2.2.2.2.2.2.2.2.2.2
  have cT' : Fl.tscIn H1.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F9 t9 = some (o.H.tV, G1, u1) := by
    rw [eV]
    exact cT
  exact ⟨F9, G1, G5, t9, u1, u5, H1.PV, _, _, _, a9,
    (((((((b1.trans b2).trans b3).trans b4).trans b5).trans b6).trans b7).trans b8).trans b9, cT',
    s1, s5, ((f2.trans f3).trans f4).trans f5, hE⟩

theorem apart_part : ApartPart := by
  intro P hp g fo F G t u o hF h
  obtain ⟨F9, G1, G5, t9, u1, u5, PV, n, cl, sv, s9, f9, cT, s1, s5, f15, hE⟩ := stages hF h
  obtain ⟨_, _, w1, w2⟩ := tsc_win s9 cT
  obtain ⟨m1, _⟩ := Slots.merge_next s5 hE
  have a := f9.next
  have b := f15.next
  exact ⟨own_fo h, by omega, by omega⟩

theorem shown_part : ShownPart := by
  intro P hp g fo F G Fb t u o hF h hL hb i hi
  obtain ⟨hc, _⟩ := hear_parts h
  have e4 : ledNO P.y.h.xl = 4 := (covers_nums hc).2.2.1
  have hf : Filled G (o.H.tV.sEnd + i) := (hear_fills hF h).tVEnd i (by rw [e4]; exact hi)
  have hf' : Filled Fb (o.H.tV.sEnd + i) := (hL.keep _ hf).1
  have hlt : o.H.tV.sEnd + i < Fb.ns := by
    rw [← hb.2.2]
    by_contra hc'
    have : Fb.gotF.getD (o.H.tV.sEnd + i) false = false := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    have hf2 : Fb.gotF.getD (o.H.tV.sEnd + i) false = true := hf'
    rw [this] at hf2
    cases hf2
  refine ⟨Fb.vp.getD (o.H.tV.sEnd + i) zeroE, ?_⟩
  unfold Fork.shown
  have hf2 : Fb.gotF.getD (o.H.tV.sEnd + i) false = true := hf'
  rw [if_pos (by simp [hlt, hf2])]

/-- The merge's first slot lies below the number of slots. -/
theorem merge_first_lt {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    wo.toWsMerged.p.first < G.ns := by
  obtain ⟨_, _, _, _, beta, v, _, _, _, _, qs, hq, _, _, _, _, _, _, _, _, _, hsF, hh, hsh, _, hv,
    hfirst, _⟩ := mergeHear_inv (hear_of_flat h)
  have hns : wo.sFv < G.ns := by
    unfold Fork.shown at hsh
    by_cases c : (decide (wo.sFv < G.ns) && G.gotF.getD wo.sFv false) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at c
      exact c.1
    · rw [if_neg c] at hsh
      cases hsh
  show wo.p.first < G.ns
  rw [hfirst]
  omega

theorem fit_behind : FitBehind := by
  intro P hp g fo F G t u o hF hfree hwL hbelow h
  obtain ⟨F9, G1, G5, t9, u1, u5, PV, n, cl, sv, s9, f9, cT, s1, s5, f15, hE⟩ := stages hF h
  obtain ⟨efo, _, hap⟩ := apart_part P hp g fo F G t u o hF h
  have fG := hear_fresh hF h
  have hL : Later F G := hearFl_later (P := P) (hp := hp) (g := g) (fo := fo) h
  have sG : Sized G := hL.sized hF
  obtain ⟨_, _, w1, w2⟩ := tsc_win s9 cT
  obtain ⟨s6, f56⟩ := Spares.fresh hE s5
  have hm := merge_first_lt hE
  refine ⟨sG, Later.refl G, fun i hi => ⟨by omega, fun hfil => ?_⟩, fun i hi => ?_,
    back_win_free hF hfree h⟩
  · have free9 : ∀ j, F9.next ≤ j → ¬ Filled F9 j := fun j hj hf =>
      hfree j (Nat.le_trans f9.next hj) ((f9.same j (Or.inr hj)).1.mp hf)
    have k := (f15.trans f56).same (o.H.tV.p.first + i) (Or.inl (by omega))
    exact tsc_free s9 free9 cT i hi (k.1.mp hfil)
  · rw [efo] at hi ⊢
    obtain ⟨a, b⟩ := hwL i hi
    refine ⟨by rw [hL.ns]; exact a, fun hfil => b ?_⟩
    exact ((fG.same (fo.leaves.first + i) (Or.inl (by omega))).1.mp hfil)

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.readyV_part
#print axioms OnBytes.Desc.First.K4.Total.apart_part
#print axioms OnBytes.Desc.First.K4.Total.shown_part
#print axioms OnBytes.Desc.First.K4.Total.fit_behind
