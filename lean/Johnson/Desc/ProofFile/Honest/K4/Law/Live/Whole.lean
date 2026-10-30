-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/Whole.lean: CONDITIONAL. EVERY SLOT THAT THE LAYERS' OWN
ROUNDS (sub-protocol K4) TAKE, BUT THE MERGE's END VALUE's, IS LIVE IN K4's TWO LISTS OF CLAIMS.

What is here. A LAW ON THE VERIFIER's TEXT: the honest prover is not in it. o is what the function
that reads K4's own rounds (`hear`, OnBytes/Desc/First/K4/Hear.lean) returned from a ledger F and a
tape t; G is the ledger that it left. "Live at j": the test `liveAt`
(Johnson/Desc/K9/Honest/SlotsLive.lean) says true at j of `plainOf lf ++ layersBack o`
(Johnson/Desc/K8/Honest/FallLayers.lean), lf the forms of `K4Values.frontForms`: some claim of the
list that is batched under its own number (eqFirst = none) names j with a coefficient that is not 0.
Statements and proofs.

  `k4_live`: **three ends.** (1) EVERY slot j from F's next free number up to, and without,
      o.wo.sFv (the slot of the merge's end value) is live. (2) Every slot on which the lookup's end
      form cEnd has a coefficient that is not 0 is live. (3) G's next free number is o.wo.sFv + 1:
      so what K4's rounds take (the numbers from F's next free one up to G's) is that interval and
      that slot, and no more (the library's `hear_next`, Johnson/Road/K4/Slots/RunsSpare.lean, and
      `sFv_at`, Johnson/Road/K4/Total/NotFree.lean).
  `k4_live_planes`, `planes_bit`: a slot on which the lookup's leaves' sumcheck's own claim has
      a coefficient that is not 0, whatever is kept that has none there, is live; and so is the slot
      of the lookup's bit. It takes no return of `hear`.
  `liveF`, `liveB`, `one_ne`, `below_of`, `ne_of_below`, `rowBatch_pv`, `wsForkStart_mem`,
      `mergeSlots_toList`: the kit.

THE STRETCHES TILE THE INTERVAL OF (1): the proof goes through them in the order in which they are
taken, by the numbers of Law/Live/Stages.lean and Law/Live/Heard.lean. Which claim makes which
stretch live:

  the sums: their carries
  a sumcheck's window: its own claim
  the end values of a gated layer and of a token sumcheck, and the batched sumcheck's A0 and
      B0: the claims that set them against the reads
  the squares' layer's two end values: the claim that sets them against each other
  the row products, and the claimed sum of their token sumcheck: the products' batch
  the second token sumcheck's claimed sum and window, and the slots of (2): the batched
      sumcheck's own claim, through its start form
  the never-sent vectors' values: the two gated layers' own claims, through theirs
  the weight claims' values and the embedding's: the merge's own claim, through its.

`set_option maxHeartbeats 1600000` at `k4_live`: one proof that goes through the stretches one by
one (the comments number them), each closed by linear arithmetic over all the stages' numbers.

Kin. THE THIRD END OF `k4_live` IS THE LIBRARY's `merge_last` (Johnson/Road/K4/MergeBelow.lean) WITH
THE EQUATION's SIDES EXCHANGED, under two of `k4_live`'s hypotheses (hF, h): it stands here as an
end so that the three can be taken together. For the output head's claims
Honest/K6/GoodLaw/Coef.lean has the tools of the like end (`live_own`, `live_lead`, `live_var`); for
a lookup's own slots Honest/K3/Good/Live/Forms.lean. Law/Live/Coef.lean's head names the kits of
rules on coefficients that its writers know of; Law/Live/Stages.lean's the library's laws on the
slots' numbers. `below_of` and `ne_of_below` share their short names with other statements of the
library (OnBytes/Desc/First/P1/ChBelow.lean, OnBytes/Tie/Pv/Tail/ClosedRec.lean,
Johnson/Top/H/KeyHeldMaps.lean; Johnson/P5J/L0/PlanCore.lean), `liveB` with two definitions
(Johnson/Desc/K1/Law/CallsG.lean, Johnson/Desc/K8/Honest/EqTailToy.lean): other namespaces.

Not shown here. THE HYPOTHESES ARE PAID NOWHERE HERE: h: the return of `hear` · hF · hfree · N, as
in Law/Live/Unnamed.lean (of N the field on cEnd alone is spent here) · T: THE TAPE MEETS `TapeLive`
(Law/Live/PscLive.lean): every round of one drawn element reads as not 0, and as not 1 where its
name is "BAT-sigma" or "JOIN": IT ASKS MORE THAN THIS PROOF SPENDS, and it speaks of the whole of t,
what `hear` leaves of it among it: that file's head says what · hll: the point between the two gated
layers has one coordinate · hLam: at most two layers of a group have routed experts: both are
numbers of the plan, not of the full size alone: the law holds at every plan that has them;
Law/Live/AtFull.lean has them at the full size · hy · hlf, as in Unnamed.lean · hfo
(`k4_live_planes` alone): fo is the lookup's state inside o · (2)'s and `k4_live_planes`' premises
on the lookup's own forms: the lookup's law is to pay them: `cEnd_sc`, `planes_sc` and `sBit_sc`
(Honest/K3/Good/Live/Forms.lean) have such coefficients, in their authors' letters and under their
own clause on the lookup's samples; they are not called in this file. TWO STRETCHES ARE MADE LIVE
HERE THROUGH A DRAWN ELEMENT THOUGH, BY READING, A CLAIM WITH PUBLIC COEFFICIENTS NAMES THEM TOO:
the row products (the eight lines of each norm's row) and the embedding's value (its own claim): so
T is spent there without need. Of the slots below F's next free number (the lookup's) nothing but
what is named. Nothing on o.wo.sFv: that no claim names it is Unnamed.lean's, under hlv beside
hypotheses of this law. Nothing on what a form is worth. This file gives no example of the
hypotheses together; its writers know of none that has been through Lean.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.Stages
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.Groups
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.Unnamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (HPlan2 Own Heard nEndT)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Road.K4 (joinStart_startOf)
open OnBytes.Desc.First.K4 (hear engFl rowBatchForm front_some hear_parts
  hearTerms_keeps mergeSlots planesParts)
open OnBytes.Desc.First.K4.Slots (SlotsIn slotsIn_mono slotsIn_empty slotsIn_slot Fresh Spares
  covers_nums stack_fin sl_U3at sl_planesAt planesParts_slots hear_next)
open OnBytes.Desc.First.K4.Total (filled_below sFv_at)
open VerifiableInference.Desc.K4Values (frontForms backForms)
open VerifiableInference.Desc.K9H (liveAt liveAt_append)
open VerifiableInference.Desc.First

variable {o : Own} {lf : List Aff}

/-- A form of "front" with a coefficient on j that is not 0 makes j live in the two lists. -/
theorem liveF {f : Aff} {j : ℕ} (hf : f ∈ lf) (h : cf Reading.gl f j ≠ 0) :
    liveAt (K8.Honest.plainOf lf ++ K8.Honest.layersBack o) j = true := by
  rw [liveAt_append, live_of_cf hf h, Bool.true_or]

/-- The like for a form of "back". -/
theorem liveB {f : Aff} {j : ℕ} (hf : f ∈ backForms o) (h : cf Reading.gl f j ≠ 0) :
    liveAt (K8.Honest.plainOf lf ++ K8.Honest.layersBack o) j = true := by
  have e : liveAt (K8.Honest.layersBack o) j = true := live_of_cf hf h
  rw [liveAt_append, e, Bool.or_true]

/-- What is 1 is not 0. -/
theorem one_ne {x : Cb.Gl.E} (h : x = 1) : x ≠ 0 := by
  rw [h]
  exact one_ne_zero

/-- A form that names slots filled in a ledger Fk alone names slots below Fk's next free number, if
Fk is fresh from a ledger F in which nothing is filled from its next free number on. -/
theorem below_of {F Fk : Fork} (hfree : ∀ j, F.next ≤ j → ¬ Filled F j) (f : Fresh F Fk) {C : Aff}
    (A : Fo.FilledA Fk C) : SlotsIn (fun i => i < Fk.next) C :=
  fun x hx => filled_below hfree f _ (A x hx).2

/-- A form that names slots below n alone names no slot from n on. -/
theorem ne_of_below {C : Aff} {n j : ℕ} (h : SlotsIn (fun i => i < n) C) (hj : n ≤ j) :
    SlotsIn (fun i => i ≠ j) C :=
  slotsIn_mono (fun i (hi : i < n) => by omega) h

/-- The batch of the row products: on the slot of a product its coefficient is not 0. hom: the
batching words are the powers of om; h0: om reads as not 0; hne: the slot is not that of the token
sumcheck's claimed sum. -/
theorem rowBatch_pv (y : Layer.Lay) (H : Heard) {om : E} {n : ℕ} (hn : ledNP y.h.xl * y.NI = n)
    (hom : H.omV = powers om n) (h0 : Reading.gl.val om ≠ 0) {i : ℕ} (hi : i < n)
    (hne : H.tV.sCl ≠ H.sPv + i) : cf Reading.gl (rowBatchForm y H) (H.sPv + i) ≠ 0 := by
  unfold rowBatchForm
  rw [hn]
  have hnd : ((List.range n).map fun l => H.sPv + l).Nodup :=
    (List.nodup_range).map fun a b e => by omega
  rw [cf_fold_one Reading.gl (fun l => H.sPv + l) (fun l => negE (H.omV.getD l zeroE))
    (List.range n) (Aff.slot H.tV.sCl) (List.mem_range.2 hi) hnd, cf_slot_ne Reading.gl hne,
    zero_add, Cb.Fo.PlaneClaims.neg_val Reading.gl, hom]
  exact neg_ne_zero.2 (powersArr_ne h0 hi)

/-- The merge's start form, at a member of its list of slots. -/
theorem wsForkStart_mem {sv : Array ℕ} (hn : sv.toList.Nodup) {x : E}
    (hx : Reading.gl.val x ≠ 0) {j : ℕ} (hj : j ∈ sv.toList) :
    cf Reading.gl (wsForkStart sv (powers x sv.size)) j ≠ 0 := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hj
  have hi' : i < sv.size := by simpa using hi
  have h := wsForkStart_live hn hx hi'
  have e1 : sv.getD i 0 = j := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some, ← e,
      Array.getElem_toList]
  rw [e1] at h
  exact h

/-- The merge's list of slots, as a list. -/
theorem mergeSlots_toList (hp : HPlan2) (g : ℕ) (o : Own) :
    (mergeSlots hp g o).toList =
      (List.range (hp.NCL - (if (g == 0) = true then 1 else 0))).map (o.K.sV + ·) ++
        (if (g == 0) = true then [o.sVE] else []) := by
  unfold mergeSlots
  rw [Array.toList_append, Array.toList_map, Array.toList_range]
  split <;> rfl

variable {P Q : Layer.Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G U : Fork} {t u : Tape}
  {rows : Bool}

/-- The lookup's claim on its bit stands among the planes' parts; what it sets the bit against names
no slot. After Johnson/Road/K4/Slots/Groups.lean's `planesParts_slots`. -/
theorem planes_bit {v : Layer.Env} {pp : Aff × List Aff} (h : planesParts v fo = some pp) :
    ∃ a1, (∀ S : ℕ → Prop, SlotsIn S a1) ∧ (Aff.slot fo.sBit - a1) ∈ pp.2 := by
  unfold planesParts at h
  obtain ⟨tB0, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tB1, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tP, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨at0, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨at1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨count, -, h⟩ := Option.bind_eq_some_iff.mp h
  have e := Option.some.inj h
  have hcol : ∀ (S : ℕ → Prop) (t x : ℕ) (a : Aff),
      (if x < v.y.kbm then v.U3at t x else none) = some a → SlotsIn S a := by
    intro S t x a ha
    split at ha
    · exact sl_U3at ha
    · cases ha
  rw [← e]
  exact ⟨at1, fun S => sl_planesAt (fun e x a ha => hcol S _ x a ha) h1, List.mem_cons_self⟩

/-- CONDITIONAL on hfo, hlf and hJ. **THE LOOKUP's SLOTS THAT K4's "front" NAMES THROUGH THE PLANES'
CLAIMS.** hfo: fo is the lookup's state that o holds (behind a hearing: the library's `own_fo`,
Johnson/Road/K4/Slots/HearFills.lean). hlf: `frontForms` returns. hJ: what
the lookup's own law is to give at the slot J: the leaves' sumcheck's own claim has a coefficient
that is not 0 there, whatever is kept that has none; or J is the bit's slot. -/
theorem k4_live_planes (hfo : o.H.fo = fo) (hlf : frontForms rows Q g o U = some lf) {J : ℕ}
    (hJ : (∀ kept, cf Reading.gl kept J = 0 →
      cf Reading.gl (fo.leaves.rowForm oneE kept) J ≠ 0) ∨ J = fo.sBit) :
    liveAt (K8.Honest.plainOf lf ++ K8.Honest.layersBack o) J = true := by
  obtain ⟨sh, pp, hpp, hfr⟩ := frontForms_some hlf
  obtain ⟨-, -, -, -, -, -, -, mL, m11, -⟩ := OnBytes.Desc.First.K4.mem_front hfr
  rcases hJ with hJ | rfl
  · refine liveF mL ?_
    rw [hfo]
    exact hJ _ (cf_of_slotsIn Reading.gl (planesParts_slots hpp).1)
  · obtain ⟨a1, ha1, hm⟩ := planes_bit hpp
    refine liveF (m11 _ hpp _ hm) ?_
    rw [hfo, cf_slot_sub Reading.gl (ha1 _)]
    exact one_ne_zero

set_option maxHeartbeats 1600000 in
/-- CONDITIONAL on all nine hypotheses. **EVERY SLOT FROM F's NEXT FREE NUMBER UP TO, AND WITHOUT,
THE MERGE's END VALUE's IS LIVE IN K4's TWO LISTS**; so is every slot on which the lookup's end form
cEnd has a coefficient that is not 0; and the ledger that the hearing leaves has the slot behind the
merge's end value's as its next free one: the hearing takes that interval, that slot, and no
more. -/
theorem k4_live (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (N : _root_.Fo.Tp.PadNames fo F) (h : hear engFl P hp g fo F t = some (o, G, u))
    (T : TapeLive t) (hll : P.y.h.ll - 1 = 1) (hLam : P.y.LamM ≤ 2) (hy : Q.y = P.y)
    (hlf : frontForms rows Q g o U = some lf) :
    (∀ j, F.next ≤ j → j < o.wo.sFv →
        liveAt (K8.Honest.plainOf lf ++ K8.Honest.layersBack o) j = true) ∧
      (∀ j, cf Reading.gl fo.cEnd j ≠ 0 →
        liveAt (K8.Honest.plainOf lf ++ K8.Honest.layersBack o) j = true) ∧
      G.next = o.wo.sFv + 1 := by
  obtain ⟨hc, hy0, -, -, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, hN, hT, hS, hG, e2,
    hM, -, -, hE⟩ := hear_parts h
  obtain ⟨n9, n7, n4, p3⟩ := covers_nums hc
  -- the stretches
  obtain ⟨pW, SW, om, F4, a1, s4, f4, a4, LW, aF, a7, a8, a9, a10, a11, a12, a13, a14, LV, a16, a17,
    a18, a19, a20, s1, a22, T1⟩ := norms_stage hF hN T n9 n7 n4
  obtain ⟨-, -, -, -, -, ksW, -, kwpl, ksPv, komV, ktV⟩ := hearTerms_keeps hT
  rw [← ksW] at a1
  rw [← kwpl] at a9 a10 a11 a12
  rw [← ksPv] at a12 a16
  rw [← komV] at a13
  rw [← ktV] at LV a16 a17 a18 a19 a20 a22
  obtain ⟨tT, pT, b1, b2, LT, b4, b5, b6, b7, b8, b9, s2, b11, T2⟩ := terms_stage s1 hT T1
  obtain ⟨pK, SK, x, C, LK, c1, c2, c3, c4, c5, hx0, hx1, c8, c9, c10, c11, cF, s3, c14, T3⟩ :=
    stack_live s2 hS T2
  obtain ⟨p1, p2, S1, S2, rhoM, Ga, L1, d1, d2, d3, d4, d5, d6, sa, fa, d9, d10, d11, L2, d13, dF,
    d15, d16, d17, d18, d19, s4', d21, T4⟩ := gated_stage s3 hG T3 hll
  obtain ⟨s5, T5, hfr5⟩ := front_stage s4' hM T4
  obtain ⟨xm, LM, m1, hxm, m3, m4, m5, mF⟩ := merge_live hE T5
  -- the ledgers are fresh from F
  have f1 : Fresh F G1 := (Spares.fresh hN hF).2
  have f2 : Fresh F G2 := f1.trans (Spares.fresh hT s1).2
  have f3 : Fresh F G3 := f2.trans (Spares.fresh hS s2).2
  have fa' : Fresh F Ga := f3.trans fa
  have f4' : Fresh F G4 := f3.trans (Spares.fresh hG s3).2
  have f5 : Fresh F G5 := by
    unfold OnBytes.Desc.First.K4.mergeFront at hM
    by_cases hg : (g == 0) = true
    · rw [if_pos hg] at hM
      exact f4'.trans (Spares.fresh hM s4').2
    · rw [if_neg hg] at hM
      obtain ⟨-, rfl, -⟩ := hM
      exact f4'
  -- the lists
  obtain ⟨sh, pp, hpp, hfr⟩ := frontForms_some hlf
  obtain ⟨g2, g46, g7, g89, g10, g11, g12, q1, q2, q3, q4, -, -, -, -⟩ := front_some hfr
  obtain ⟨mm2, mmB, mmV, mm46, mm7, mm89, -, -, -, -⟩ := OnBytes.Desc.First.K4.mem_front hfr
  obtain ⟨r1, r2⟩ := norms_hit q1
  obtain ⟨o2, ho2, r3, r4, r5, r6, r7, r8⟩ := gated_hit q4
  obtain rfl : hd2 = o2 := Option.some.inj (e2.symm.trans ho2)
  obtain ⟨r9, r10, r11, r12⟩ := back_hit o (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {})
    (fun S => (stack_fin (S := S) hS).1) (fun S => (stack_fin (S := S) hS).2)
  -- the start form of the batched sumcheck
  obtain ⟨weighed, parts, laid, tT', -, hparts, -, -, -, hT', hC, -, -⟩ := joinStart_startOf c5
  obtain rfl : tT = tT' := Option.some.inj (b1.symm.trans hT')
  have hpc : ∀ S : ℕ → Prop, ∀ f ∈ parts, SlotsIn S f := fun S => parts_clear hparts S
  have n1 := f1.next
  have hcE : SlotsIn (fun i => i < tT.sCl) o.H.fo.cEnd := by
    rw [OnBytes.Desc.First.K4.Slots.own_fo h]
    exact slotsIn_mono (fun i (hi : i < F.next) => by omega)
      (below_of hfree (Fresh.refl F) N.cEnd.filledA)
  have hNI : o.v.y.NI = P.y.NI := by rw [hy0]
  have eT : nEndT P.y = o.v.y.NN * o.v.y.Lam + o.v.y.LamM + o.v.y.LamM * o.v.y.h.NE := by
    rw [hy0]
    unfold nEndT
    rw [if_pos p3, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  have hnQ : ledNP Q.y.h.xl * Q.y.NI = 7 * P.y.NI := by rw [hy, n7]
  have hsv : (mergeSlots hp g o).toList.Nodup := by
    rw [mergeSlots_toList]
    refine List.Nodup.append ((List.nodup_range).map fun a b e => by omega) ?_ ?_
    · split
      · exact List.nodup_singleton _
      · exact List.nodup_nil
    · intro a ha hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      have hi' := List.mem_range.1 hi
      rcases hfr5 with ⟨hg, e5, -⟩ | ⟨hg, -⟩
      · have hs1 : (if (g == 0) = true then 1 else 0) = 1 := if_pos hg
        rw [if_pos hg] at hb
        have e6 : o.K.sV + i = o.sVE := List.mem_singleton.1 hb
        omega
      · rw [if_neg (by rw [hg]; exact Bool.false_ne_true)] at hb
        cases hb
  have eG := hear_next hF h
  have eS := sFv_at h
  refine ⟨?_, fun j hcj => ?_, by omega⟩
  swap
  -- 0 a slot that the lookup's end form names: it lies below F's next free number
  · have hj : j < F.next := by
      by_contra hge
      exact hcj (cf_of_slotsIn Reading.gl
        (ne_of_below (below_of hfree (Fresh.refl F) N.cEnd.filledA) (by omega)))
    refine liveB r9 ?_
    rw [c4]
    refine live_start LK SK (Or.inl (by omega)) slotsIn_empty ?_
    rw [c1, hC, startK_cEnd b1 hpc b2 (by rw [b6, b5]) (by omega) (by omega),
      OnBytes.Desc.First.K4.Slots.own_fo h]
    exact neg_ne_zero.2 hcj
  intro j h1 h2
  -- 1 the sums
  rcases Nat.lt_or_ge j F4.next with k | k
  · obtain ⟨f, hf, c⟩ := rows_hit_carry q2 (i := (j - F.next) / 9) (s := (j - F.next) % 9)
      (by rw [hNI]; omega) (by omega)
    have ej : o.H.sW + 9 * ((j - F.next) / 9) + (j - F.next) % 9 = j := by omega
    rw [ej] at c
    exact liveF (mm46 _ q2 f hf) (one_ne c)
  -- 2 the squares' layer: its window
  rcases Nat.lt_or_ge j o.H.wpl.sL with k2 | k2
  · refine liveF (mm2 _ q1 _ r1) ?_
    rw [a9]
    exact live_win LW SW (by omega) (by omega) (ne_of_below (below_of hfree f4 aF) (by omega))
      slotsIn_empty
  -- 3 its two end values
  rcases Nat.lt_or_ge j o.H.sPv with k3 | k3
  · refine liveF (mm2 _ q1 _ r2) ?_
    rw [cf_sub]
    rcases Nat.lt_or_ge j o.H.wpl.sR with k3' | k3'
    · obtain rfl : j = o.H.wpl.sL := by omega
      rw [cf_slot_self, cf_slot_ne Reading.gl (by omega), sub_zero]
      exact one_ne_zero
    · obtain rfl : j = o.H.wpl.sR := by omega
      rw [cf_slot_self, cf_slot_ne Reading.gl (by omega), zero_sub]
      exact neg_ne_zero.2 one_ne_zero
  -- 4 the row products
  rcases Nat.lt_or_ge j o.H.tV.sCl with k4 | k4
  · have ej : o.H.sPv + (j - o.H.sPv) = j := by omega
    have := rowBatch_pv Q.y o.H hnQ a13 a14 (i := j - o.H.sPv) (by omega) (by omega)
    rw [ej] at this
    exact liveF mmB this
  -- 5 the claimed sum of their token sumcheck
  rcases Nat.lt_or_ge j o.H.tV.p.first with k5 | k5
  · obtain rfl : j = o.H.tV.sCl := by omega
    exact liveF mmB (one_ne (rowBatch_cl Q.y o.H fun i hi => by rw [hnQ] at hi; omega))
  -- 6 its window
  rcases Nat.lt_or_ge j o.H.tV.sEnd with k6 | k6
  · exact liveF mmV (live_win LV _ k5 (by omega) (by rw [a17]; exact slotsIn_slot (by omega))
      slotsIn_empty)
  -- 7 its end values
  rcases Nat.lt_or_ge j G1.next with k7 | k7
  · obtain ⟨f, hf, c⟩ := rows_hit_end q2 (i := (j - o.H.tV.sEnd) / 4) (k := (j - o.H.tV.sEnd) % 4)
      (by rw [hNI]; omega) (by omega)
    have ej : o.H.tV.sEnd + 4 * ((j - o.H.tV.sEnd) / 4) + (j - o.H.tV.sEnd) % 4 = j := by omega
    rw [ej] at c
    exact liveF (mm46 _ q2 f hf) (one_ne c)
  -- 8 the second token sumcheck's claimed sum
  rcases Nat.lt_or_ge j pT.first with k8 | k8
  · obtain rfl : j = tT.sCl := by omega
    refine liveB r9 ?_
    rw [c4]
    refine live_start LK SK (Or.inl (by omega)) slotsIn_empty ?_
    rw [c1, hC, startK_cl b1 hpc b2 LT b4 (by rw [b6, b5]) (by omega) hcE]
    exact sub_ne_zero.2 hx1
  -- 9 its window
  rcases Nat.lt_or_ge j tT.sEnd with k9 | k9
  · refine liveB r9 ?_
    rw [c4]
    refine live_start LK SK (Or.inl (by omega)) slotsIn_empty ?_
    rw [c1, hC]
    exact startK_win b1 hpc b2 LT (by rw [b6, b5]) (by omega) hcE hx0 k8 (by omega)
  -- 10 its end values
  rcases Nat.lt_or_ge j G2.next with k10 | k10
  · obtain ⟨f, hf, c⟩ := terms_hit q3 b1 (x := j - tT.sEnd) (by omega)
    have ej : tT.sEnd + (j - tT.sEnd) = j := by omega
    rw [ej] at c
    exact liveF (mm7 _ q3 f hf) (one_ne c)
  -- 11 the batched sumcheck's window
  rcases Nat.lt_or_ge j o.K.sA0 with k11 | k11
  · refine liveB r9 ?_
    rw [c4]
    exact live_win LK SK (by omega) (by omega)
      (by rw [c1]; exact ne_of_below (below_of hfree f2 cF) (by omega)) slotsIn_empty
  -- 12 A0
  rcases Nat.lt_or_ge j o.K.sH1 with k12 | k12
  · obtain rfl : j = o.K.sA0 := by omega
    obtain ⟨f, hf, c⟩ := r11
    exact liveB hf (one_ne c)
  -- 13 the first never-sent vector's value
  rcases Nat.lt_or_ge j (o.K.sH1 + 1) with k13 | k13
  · obtain rfl : j = o.K.sH1 := by omega
    refine liveF (mm89 _ q4 _ r3) ?_
    rw [d4]
    refine live_start L1 S1 (Or.inl (by omega)) slotsIn_empty ?_
    rw [d1, cf_slot_self]
    exact one_ne_zero
  -- 14 the routed layers' never-sent vectors' values
  rcases Nat.lt_or_ge j o.K.sB0 with k14 | k14
  · refine liveF (mm89 _ q4 _ r4) ?_
    rw [d17]
    refine live_start L2 S2 (Or.inl (by omega)) slotsIn_empty ?_
    have ej : o.K.sH1 + 1 + (j - (o.K.sH1 + 1)) = j := by omega
    have := start2_live P.y.LamM o.K.sH1 rhoM d11 (lm := j - (o.K.sH1 + 1)) (by omega)
      (by
        rw [d10]
        show _ < 2
        omega)
    rw [ej] at this
    rw [d13]
    exact this
  -- 15 B0
  rcases Nat.lt_or_ge j o.K.sV with k15 | k15
  · obtain rfl : j = o.K.sB0 := by omega
    obtain ⟨f, hf, c⟩ := r12
    exact liveB hf (one_ne c)
  -- 16 the weight claims' values
  rcases Nat.lt_or_ge j G3.next with k16 | k16
  · refine liveB r10 (live_start LM _ (Or.inl (by
      rcases hfr5 with ⟨-, -, e5⟩ | ⟨-, e5⟩ <;> omega)) slotsIn_empty ?_)
    rw [m1]
    refine wsForkStart_mem hsv hxm ?_
    rw [mergeSlots_toList]
    refine List.mem_append_left _ (List.mem_map.2 ⟨j - o.K.sV, List.mem_range.2 (by omega), by
      show o.K.sV + (j - o.K.sV) = j
      omega⟩)
  -- 17 the first gated layer's window
  rcases Nat.lt_or_ge j o.hd.sL with k17 | k17
  · refine liveF (mm89 _ q4 _ r3) ?_
    rw [d4]
    exact live_win L1 S1 (by omega) (by omega) (by rw [d1]; exact slotsIn_slot (by omega))
      slotsIn_empty
  -- 18 its two end values
  rcases Nat.lt_or_ge j Ga.next with k18 | k18
  · rcases Nat.lt_or_ge j o.hd.sR with k18' | k18'
    · obtain rfl : j = o.hd.sL := by omega
      obtain ⟨f, hf, c⟩ := r5
      exact liveF (mm89 _ q4 f hf) (one_ne c)
    · obtain rfl : j = o.hd.sR := by omega
      obtain ⟨f, hf, c⟩ := r6
      exact liveF (mm89 _ q4 f hf) (one_ne c)
  -- 19 the second gated layer's window
  rcases Nat.lt_or_ge j hd2.sL with k19 | k19
  · refine liveF (mm89 _ q4 _ r4) ?_
    rw [d17]
    exact live_win L2 S2 (by omega) (by omega) (ne_of_below (below_of hfree fa' dF) (by omega))
      slotsIn_empty
  -- 20 its two end values
  rcases Nat.lt_or_ge j G4.next with k20 | k20
  · rcases Nat.lt_or_ge j hd2.sR with k20' | k20'
    · obtain rfl : j = hd2.sL := by omega
      obtain ⟨f, hf, c⟩ := r7
      exact liveF (mm89 _ q4 f hf) (one_ne c)
    · obtain rfl : j = hd2.sR := by omega
      obtain ⟨f, hf, c⟩ := r8
      exact liveF (mm89 _ q4 f hf) (one_ne c)
  -- 21 in the first group: the embedding's value
  rcases Nat.lt_or_ge j G5.next with k21 | k21
  · rcases hfr5 with ⟨hg, e5, e5'⟩ | ⟨-, e5⟩
    · obtain rfl : j = o.sVE := by omega
      refine liveB r10 (live_start LM _ (Or.inl (by omega)) slotsIn_empty ?_)
      rw [m1]
      refine wsForkStart_mem hsv hxm ?_
      rw [mergeSlots_toList, if_pos hg, if_pos hg]
      exact List.mem_append_right _ List.mem_cons_self
    · omega
  -- 22 the merge's window
  · exact liveB r10 (live_win LM _ (by omega) (by omega)
      (by rw [m1]; exact ne_of_below (below_of hfree f5 mF) (by omega)) slotsIn_empty)

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.liveF
#print axioms ProofFile.Honest.K4.Live.liveB
#print axioms ProofFile.Honest.K4.Live.one_ne
#print axioms ProofFile.Honest.K4.Live.below_of
#print axioms ProofFile.Honest.K4.Live.ne_of_below
#print axioms ProofFile.Honest.K4.Live.rowBatch_pv
#print axioms ProofFile.Honest.K4.Live.wsForkStart_mem
#print axioms ProofFile.Honest.K4.Live.mergeSlots_toList
#print axioms ProofFile.Honest.K4.Live.planes_bit
#print axioms ProofFile.Honest.K4.Live.k4_live_planes
#print axioms ProofFile.Honest.K4.Live.k4_live
