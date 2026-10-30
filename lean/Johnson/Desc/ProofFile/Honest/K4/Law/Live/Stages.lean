-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/Stages.lean: CONDITIONAL. THE STRETCHES OF THE FUNCTION
THAT READS THE LAYERS' OWN ROUNDS (sub-protocol K4; `hear`, OnBytes/Desc/First/K4/Hear.lean), ONE BY
ONE, WHERE THEY RETURN FROM A TAPE THAT MEETS `TapeLive`: WHICH STATES ARE LIVE, AND THE NUMBER OF
EVERY SLOT THAT THE STRETCH TAKES.

What is here. A LAW ON THE VERIFIER's TEXT: the honest prover is not in it. Four statements, each
from a return of a stretch, a ledger F with arrays of the right sizes and a tape that meets
`TapeLive` (Law/Live/PscLive.lean). Each states: every slot field of what is returned, as F's next
free number plus numbers of the plan; that each sumcheck's state is `PscLive`, with its first slot
and its window's length; that the ledger left has arrays of the right sizes, with its next free
number; that the tape left meets `TapeLive`. The proofs call `level_live` and `tsc_live`
(Law/Live/Heard.lean) along the library's lemmas on where each stretch stands on the tape
(OnBytes/Desc/First/K4/NormsTape.lean, HearCalls.lean); `gated_stage` unfolds `hearGated`
(OnBytes/Desc/First/K4/Hear.lean) itself, and `front_stage`, which has no sumcheck, starts from
`mergeFront` (OnBytes/Desc/First/K4/MergeClaims.lean).

  `norms_stage`: the sums, the squares' layer, the row products and their token sumcheck. The
      squares' layer's own claim is its state's `rowForm`. Of its start form only this: it names
      slots that are filled in the ledger in front of the layer. Of the token sumcheck's: it is the
      slot of the claimed sum. That the row products' batching element reads as not 0.
  `terms_stage`: the second token sumcheck: its start form is the slot of its claimed sum; its
      product P reads as 1; and the form KT is its own claim divided by minus its joining element.
  `gated_stage`: the two gated layers, with their start forms (a slot; `start2`,
      Johnson/Road/Rows/GatedEnds.lean), and the point rhoM between them: one coordinate, which
      reads as neither 0 nor 1.
  `front_stage`: between the gated layers and the merge: in the first group the embedding's
      value takes one slot; else none.
  `TapeLive.drop`, `TapeLive.of_putBack`: a tape less its first rounds meets the clause; so does
      a tape from whose first round elements still to be sent are taken.

Kin. THE LIBRARY HAS THE SLOTS' NUMBERS ALREADY. From the two premises of `norms_stage` on ledger
and return, `norms_slots0` (Johnson/Road/K4/NormsWorld.lean) has six of its numbers (sW, wpl.sL,
sPv, tV.sCl, tV.p.first, tV.sEnd), without the three premises on limbs. From a return of the whole
`hear`: `hear_slots` and `hear_slots_right` (Johnson/Road/K4/HearSlots.lean), eighteen slot fields
up to the gated layers; `hear_end_first` and `hear_end_later` (Johnson/Road/K4/HearSlotsEnd.lean),
the embedding's slot. Where a stretch is shown to return, `NormsLeft`, `TermsLeft` and `GatedLeft`
(Johnson/Desc/First/K4/Returns/Norms.lean, Terms.lean, Gated.lean) state the same numbers. BY
READING the numbers agree; no proof here calls one of these laws. None of them speaks of `PscLive`
or `TapeLive`.

Not shown here. THAT ANY TAPE MEETS `TapeLive`. That a stretch returns. `gated_stage` takes hll: the
point rhoM has ONE coordinate (ll - 1 = 1): a round that draws several elements is outside what
`TapeLive` speaks of. Nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.Heard
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.StartK
import Johnson.Road.Rows.GatedEnds
import OnBytes.Desc.First.K4.NormsTape
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Desc.First.K4.MergeClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Heard HeardStack Own nEndT)
open OnBytes.PscRun (Sized)
open OnBytes.Road.Rows (start2)
open OnBytes.Desc.First.K4 (engFl hearNorms hearTerms hearGated hearNorms_tape hearTerms_calls k0
  mergeFront)
open OnBytes.Desc.First.K4.Slots (run_same fresh_run Fresh Spares)
open OnBytes.Desc.First.P1 (bind_some pure_some need_some point_spec pscRow_spec claimsIn_spec
  putBack)

/-- Where a tape meets the clause, so does the tape less its first k rounds. -/
theorem TapeLive.drop {t : Tape} (h : TapeLive t) (k : ℕ) : TapeLive (t.drop k) :=
  h.sub fun _ hr => List.mem_of_mem_drop hr

/-- Elements laid back in front of what the first round still has to send turn nothing that the
clause reads. -/
theorem TapeLive.of_putBack {l : List E} : ∀ {u : Tape}, TapeLive (putBack l u) → TapeLive u
  | [], _ => fun _ hr => by cases hr
  | ⟨nm, z, w, s, d⟩ :: t, h => fun r hr e he => by
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h ⟨nm, z, w, l ++ s, d⟩ List.mem_cons_self e he
    · exact h r (List.mem_cons_of_mem _ hr) e he

/-- CONDITIONAL. **The norms' stretch.** n9, n7, n4: how many sums, products and end values a norm's
row has where an element of the stream has five limbs. -/
theorem norms_stage {P : Layer.Pub} {g : ℕ} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H : Heard}
    (hF : Sized F) (h : hearNorms engFl P g fo F t = some (H, G, u)) (T : TapeLive t)
    (n9 : ledNS P.y.h.xl = 9) (n7 : ledNP P.y.h.xl = 7) (n4 : ledNO P.y.h.xl = 4) :
    ∃ (p : Psc) (S0 om : E) (F4 : Fork), H.sW = F.next ∧ Sized F4 ∧ Fresh F F4 ∧
      F4.next = F.next + 9 * P.y.NI ∧ PscLive p ∧ Fo.FilledA F4 p.start ∧ p.first = F4.next ∧
      p.walk.1.length = 1 + 2 * P.rd.muV + 2 ∧ H.wpl.row = p.rowForm S0 {} ∧
      H.wpl.sL = F4.next + 1 + 2 * P.rd.muV + 2 ∧ H.wpl.sR = H.wpl.sL + 1 ∧
      H.sPv = H.wpl.sL + 2 ∧ H.omV = powers om (7 * P.y.NI) ∧ Reading.gl.val om ≠ 0 ∧
      PscLive H.tV.p ∧ H.tV.sCl = H.sPv + 7 * P.y.NI ∧ H.tV.p.start = Aff.slot H.tV.sCl ∧
      H.tV.p.first = H.tV.sCl + 1 ∧ H.tV.p.walk.1.length = 1 + 2 * P.y.h.lt + 2 ∧
      H.tV.sEnd = H.tV.sCl + 1 + 1 + 2 * P.y.h.lt + 2 ∧ Sized G ∧
      G.next = H.tV.sEnd + 4 * P.y.NI ∧ TapeLive u := by
  obtain ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, -, -, -, -, hvW, hsW, hrW, -, -, -, -,
    hL, hom, hvP, hsPv, hrP, homV, hT, -⟩ := hearNorms_tape h
  rw [n9] at hrW
  rw [n7] at hrP homV hom
  rw [n4] at hT
  obtain ⟨s4, e4, -⟩ :=
    run_same (show Sized ({ F with next := F.next + 9 * P.y.NI } : Fork) from hF) hrW
  have e4' : F4.next = F.next + 9 * P.y.NI := e4
  have f4 : Fresh F F4 := (fresh_run hF hrW (Nat.le_refl _) (by
    rw [n9] at hvW
    omega)).2
  obtain ⟨p, S0, L1, a1, a2, a3, a4, a5, a6, a7, s7, e7, -⟩ := level_live s4 hL (T.drop _)
  obtain ⟨s8, e8, -⟩ :=
    run_same (show Sized ({ F7 with next := F7.next + 7 * P.y.NI } : Fork) from s7) hrP
  have e8' : F8.next = F7.next + 7 * P.y.NI := e8
  obtain ⟨L2, b1, b2, b3, b4, b5, sG, eG, TG⟩ := tsc_live s8 hT (T.drop _)
  have hm0 : (⟨some RoundName.batSigma.name, 0, 7 * P.y.NI, vP.toList, [om]⟩ : FlatRound) ∈
      t.drop (k0 g + P.rd.muV + 6) := by
    rw [hom]
    exact List.mem_cons_self
  have hmem := List.mem_of_mem_drop hm0
  have c1 : H.sPv = H.wpl.sL + 2 := by rw [hsPv, e7, a5]
  have c2 : H.tV.sCl = H.sPv + 7 * P.y.NI := by rw [b1, e8', hsPv]
  refine ⟨p, S0, om, F4, hsW, s4, f4, e4', L1, by rw [a1]; exact a7, a2, a3, a4, a5, a6, c1, homV,
    T.at_ hmem, L2,
    c2, by rw [b2, b1], by rw [b3, b1], b4, by rw [b5, b1], sG, ?_, TG⟩
  rw [eG, b5]

/-- CONDITIONAL. **The second token sumcheck's stretch.** p: its state as the own claim is made of
it. -/
theorem terms_stage {P : Layer.Pub} {H H' : Heard} {F G : Fork} {t u : Tape} (hF : Sized F)
    (h : hearTerms engFl P H F t = some (H', G, u)) (T : TapeLive t) :
    ∃ (tT : Tsc) (p : Psc), H'.tT = some tT ∧
      H'.KT = (p.rowForm zeroE {}).scale (negE (invE p.eps)) ∧ PscLive p ∧
      Reading.gl.val p.walk.2 = 1 ∧ tT.sCl = F.next ∧ p.start = Aff.slot F.next ∧
      p.first = F.next + 1 ∧ p.walk.1.length = 1 + 2 * P.y.h.lt + 1 ∧
      tT.sEnd = F.next + 1 + 1 + 2 * P.y.h.lt + 1 ∧ Sized G ∧
      G.next = F.next + 1 + 1 + 2 * P.y.h.lt + 1 + nEndT P.y ∧ TapeLive u := by
  obtain ⟨tT, G1, u1, row, p', hc, -, hr, rfl⟩ := hearTerms_calls h
  obtain ⟨L, b1, b2, b3, b4, b5, s1, e1, T1⟩ := tsc_live hF hc T
  obtain ⟨rfl, rfl, hrun⟩ := pscRow_spec hr
  obtain ⟨s2, e2, -⟩ := run_same s1 hrun
  exact ⟨{ tT with p := p' }, tT.p, rfl, rfl, L, tsc_walk2 hc, b1, b2, b3, b4, b5, s2,
    e2.trans e1, T1⟩

/-- CONDITIONAL. **The two gated layers.** hll: the point between them has one coordinate. -/
theorem gated_stage {P : Layer.Pub} {H : Heard} {K : HeardStack} {F G : Fork} {t u : Tape}
    {hd hd2 : Level} (hF : Sized F) (h : hearGated engFl P H K F t = some ((hd, hd2), G, u))
    (T : TapeLive t) (hll : P.y.h.ll - 1 = 1) :
    ∃ (p1 p2 : Psc) (S1 S2 : E) (rhoM : Array E) (Ga : Fork),
      PscLive p1 ∧ p1.start = Aff.slot K.sH1 ∧ p1.first = F.next ∧
      p1.walk.1.length = 1 + 2 * P.rd.muH + 2 ∧ hd.row = p1.rowForm S1 {} ∧
      hd.sL = F.next + 1 + 2 * P.rd.muH + 2 ∧ hd.sR = hd.sL + 1 ∧ Sized Ga ∧ Fresh F Ga ∧
      Ga.next = hd.sL + 2 ∧ rhoM.size = 1 ∧
      (∀ e ∈ rhoM.toList, Reading.gl.val e ≠ 0 ∧ Reading.gl.val e ≠ 1) ∧
      PscLive p2 ∧ p2.start = start2 P.y.LamM K.sH1 rhoM ∧ Fo.FilledA Ga p2.start ∧
      p2.first = Ga.next ∧ p2.walk.1.length = 1 + 2 * P.rd.muH2 + 2 ∧ hd2.row = p2.rowForm S2 {} ∧
      hd2.sL = Ga.next + 1 + 2 * P.rd.muH2 + 2 ∧ hd2.sR = hd2.sL + 1 ∧ Sized G ∧
      G.next = hd2.sL + 2 ∧ TapeLive u := by
  unfold hearGated at h
  obtain ⟨hd', G1, u1, c1, k1⟩ := bind_some.mp h
  obtain ⟨tT, A1, a1, c2, k2⟩ := bind_some.mp k1
  obtain ⟨-, rfl, rfl⟩ := need_some.mp c2
  obtain ⟨rhoM, G2, u2, c3, k3⟩ := bind_some.mp k2
  have c3' : Fl.point .join (P.y.h.ll - 1) G1 u1 = some (rhoM, G2, u2) := c3
  obtain ⟨rfl, w, d, hu1, hdl, rfl⟩ := point_spec c3'
  obtain ⟨hd2', A4, a4, c4, k4⟩ := bind_some.mp k3
  obtain ⟨e, rfl, rfl⟩ := pure_some.mp k4
  obtain rfl : hd' = hd := congrArg Prod.fst e
  obtain rfl : hd2' = hd2 := congrArg Prod.snd e
  obtain ⟨p1, S1, L1, x1, x2, x3, x4, x5, x6, -, s1, e1, T1⟩ := level_live hF c1 T
  have T2 : TapeLive u2 := T1.sub fun r hr => by
    rw [hu1]
    exact List.mem_cons_of_mem _ hr
  obtain ⟨p2, S2, L2, y1, y2, y3, y4, y5, y6, y7, s2, e2, T3⟩ := level_live s1 c4 T2
  rw [hll] at hdl
  obtain ⟨r0, rfl⟩ : ∃ r0, d = [r0] := List.length_eq_one_iff.1 hdl
  have hm : (⟨some RoundName.join.name, 0, w, [], [r0]⟩ : FlatRound) ∈ u1 := by
    rw [hu1]
    exact List.mem_cons_self
  refine ⟨p1, p2, S1, S2, [r0].toArray, G1, L1, x1, x2, x3, x4, x5, x6, s1,
    (Spares.fresh c1 hF).2, by rw [e1, x5], rfl,
    ?_, L2, y1, by rw [y1]; exact y7, y2, y3, y4, y5, y6, s2, by rw [e2, y5], T3⟩
  intro e he
  obtain rfl : e = r0 := by simpa using he
  exact ⟨T1.at_ hm, T1.ne_one_join hm⟩

/-- CONDITIONAL. **Between the gated layers and the merge**: in the first group the embedding's
value is sent. -/
theorem front_stage {g : ℕ} {o : Own} {G4 G5 : Fork} {u4 u5 : Tape} (hF : Sized G4)
    (h : mergeFront g o G4 u4 G5 u5) (T : TapeLive u4) :
    Sized G5 ∧ TapeLive u5 ∧ (((g == 0) = true ∧ o.sVE = G4.next ∧ G5.next = G4.next + 1) ∨
      ((g == 0) = false ∧ G5.next = G4.next)) := by
  unfold mergeFront at h
  by_cases hg : (g == 0) = true
  · rw [if_pos hg] at h
    obtain ⟨e, v, -, ht, -, hrun⟩ := claimsIn_spec h
    obtain ⟨s, n, -⟩ :=
      run_same (show Sized ({ G4 with next := G4.next + 1 } : Fork) from hF) hrun
    exact ⟨s, TapeLive.of_putBack (ht ▸ T), Or.inl ⟨hg, e, n⟩⟩
  · rw [if_neg hg] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact ⟨hF, T, Or.inr ⟨by simpa using hg, rfl⟩⟩

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.TapeLive.drop
#print axioms ProofFile.Honest.K4.Live.TapeLive.of_putBack
#print axioms ProofFile.Honest.K4.Live.norms_stage
#print axioms ProofFile.Honest.K4.Live.terms_stage
#print axioms ProofFile.Honest.K4.Live.gated_stage
#print axioms ProofFile.Honest.K4.Live.front_stage
