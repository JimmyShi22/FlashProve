-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearMid.lean: what the routines for the middle of a layers' sub-proof's own
messages have heard, with what their records hold of it: the products' scalars and the first token
sumcheck, the terms, the draw that combines and the batched sumcheck.

From the success of the calls in OnBytes/Model/Layer.lean (the end of hearNorms; hearTerms;
hearStack) to the list of stages that were heard (`HeardL`, OnBytes/Tie/Pv/Lay/HearL.lean), in the
order of the chain of Cb/Pv/Lay/Own.lean, each sumcheck with its record.

Main names:
  `TokSaid`, `tok_heard`: one token sumcheck (tscIn, OnBytes/Model/Tsc.lean): one scalar rides in
    the first message; the sizes of what was heard; the record (`Ended`,
    OnBytes/Tie/Pv/Psc/Run/PscSeam.lean), whose start form is the slot of that scalar alone; the
    slots; what stands under them.
  `rows_heard`: the three calls at the end of hearNorms: the products' scalars with the round that
    batches them, then the first token sumcheck.
  `hearTerms_ran`, `terms_heard`: hearTerms where some call has terms: the second token sumcheck;
    a step that leaves the channel (the test on the drawn coefficient, two notes); what is handed
    on: the row without a summand, times -1 over the coefficient. `terms_coin`: if no test on
    values is marked as failed behind hearTerms, on a view, the coefficient that the sumcheck drew
    is not 0.
  `Quiet` with `Quiet.bind`, `quiet_form`, `quiet_mustAs`, `quiet_shown`, `quiet_mapM`,
    `quiet_shownRun`, `quiet_joinStart`: routines that, where they succeed, leave state and
    context as they were.
  `seam_gap`: a sumcheck's parts with a step between the first round and the others that turns
    notes or mark alone: the parts were heard as if that step came last
    (OnBytes/Tie/Pv/Lay/Slides.lean, HearMark.lean). The context that it names behind the parts is
    none of the run's: the statement is of the listeners as functions.
  `hearStack_ran`: the calls of hearStack that hear or that turn the state, where the terms were
    heard. `StackFin`: what else its success says: the two tests on public numbers, the slots of
    the shown values, and that the two sides' values at the end point are `stackEnd` of what was
    shown.
  `StackSaid`, `stack_heard`: the round that draws one element for two rows; the batched sumcheck,
    of plain variables; its record, with the public part of the start form that joinStart returns;
    the challenges in reversed order; the slot of the first end value; the row; what stands under
    the slots; and `StackFin`.

Limits: one direction: from the routines' success, from a state whose arrays on slots have their
length. A routine's success does not say that its tests on values held: `Blk.check` marks a failed
test in the context and goes on; that no mark is set at the end of a run is a premise of
`terms_coin` and is shown nowhere here. The two tests inside joinStart are not kept. What the
start form, the rows and the slots are worth is not said here. A sub-proof without terms is not
covered.
-/
import OnBytes.Tie.Pv.Lay.HearMark
import OnBytes.Tie.Pv.Psc.Run.PscToken
import OnBytes.Tie.Pv.Psc.Run.PscRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open OnBytes.Psc (Weight hearMany hearOne hidingEntries)
open OnBytes.Tie.Pv.Att (PscH batch_ok claimsIn_said)

/-! ### A token sumcheck -/

/-- What one token sumcheck has said: the sizes of what was heard, the record, the state. x: the
scalar that rides in the first message: the claimed sum, under its mask. -/
structure TokSaid (P : Array E) (lt shown dY : Nat) (F G : Fork) (t : Tsc) (x : E) (H : PscH) :
    Prop where
  len : lt ≤ P.size
  rounds : H.rs.length = lt
  sizes : ∀ y ∈ (tokenWeights P lt).zip H.rs, y.2.1.length + 1 = y.1.d
  sentY : H.sentY.length = dY
  vals : H.v.length = shown
  eps : t.p.eps = H.eps
  /-- the sumcheck's record: its start form is the slot of the claimed sum alone -/
  psc : Ended t.p (Aff.slot F.next) (addE zeroE (mulE oneE x)) H.mu H.eps (F.next + 1)
    (tokenWeights P lt) H.rs dY H.sentY H.beta
  sCl : t.sCl = F.next
  r : t.r.toList = H.rs.map (·.2)
  sEnd : t.sEnd = t.p.first + hidingEntries (tokenWeights P lt ++ [Weight.atZero (dY + 1)])
  /-- the claimed sum stands under its slot with the factor 1, the end values under theirs with
  the factor beta -/
  fill : ∃ F1 : Fork, Filled (taken F 1) F1 F.next [x] oneE ∧
    Filled (taken F1 (1 + 2 * lt + dY + shown)) G t.sEnd H.v H.beta
  sized : Sized G

/-- One token sumcheck. -/
theorem tok_heard (P : Array E) (lt shown dY : Nat) (F G : Fork) (c c' : Ctx) (t : Tsc)
    (h : tscIn P lt shown dY F c = .ok ((t, G), c')) (hs : Sized F) :
    ∃ (x : E) (H : PscH), HeardL [.sum [x] (tokenWeights P lt) dY H] c c' ∧
      TokSaid P lt shown dY F G t x H := by
  obtain ⟨x, mu, rs, sentY, beta, v, F1, c1, a1, a2, a3, a4, _, a6, a7, _, _, a10, a11, a12, _,
    a14, a15, a16⟩ := tscIn_seam P lt shown dY F G c c' t h hs
  exact ⟨x, ⟨mu, t.p.eps, rs, sentY, beta, v⟩, ⟨c1, c', a1, rfl⟩,
    ⟨a2, a3, a4, a6, a7, rfl, a10, a11, a12, a14, ⟨F1, a15, a16⟩, a16.sized⟩⟩

/-! ### The products' scalars and the first token sumcheck -/

/-- From the three calls at the end of hearNorms: what was heard. -/
theorem rows_heard (np : Nat) (PV : Array E) (lt shown : Nat) (F5 F6 F7 F8 : Fork)
    (c5 c6 c7 c8 : Ctx) (sPv : Nat) (omV : Array E) (tV : Tsc)
    (h1 : SubM.claimsIn np F5 c5 = .ok ((sPv, F6), c6))
    (h2 : SubM.batch np F6 c6 = .ok ((omV, F7), c7))
    (h3 : tscIn PV lt shown 2 F7 c7 = .ok ((tV, F8), c8)) (hs : Sized F5) :
    ∃ (vP : List E) (x xCl : E) (H : PscH),
      HeardL [.bat vP np x, .sum [xCl] (tokenWeights PV lt) 2 H] c5 c8 ∧
      vP.length = np ∧ sPv = F5.next ∧ Filled (taken F5 np) F6 F5.next vP oneE ∧
      omV = powers x np ∧ TokSaid PV lt shown 2 F6 F8 tV xCl H := by
  obtain ⟨vP, a1, a2, a3, a4, a5⟩ := claimsIn_said np F5 F6 c5 c6 sPv h1 hs
  obtain ⟨e, x, b1, b2⟩ := batch_heardL np F6 F7 c6 c7 omV h2 vP c5 (by rw [a2]; exact a1)
  rw [e] at h3
  obtain ⟨xCl, H, d1, d2⟩ := tok_heard PV lt shown 2 F6 F8 c7 c8 tV h3 a5
  exact ⟨vP, x, xCl, H, HeardL.append [_] [_] c5 c7 c8 b1 d1, a2, a3, a4, b2, d2⟩

/-! ### The terms -/

/-- The calls of hearTerms, where some call has terms. -/
theorem hearTerms_ran (P : Pub) (H H' : Heard) (F G : Fork) (c c' : Ctx)
    (hne : P.rd.tscCalls.isEmpty = false) (h : hearTerms P H F c = .ok ((H', G), c')) :
    ∃ (tT : Tsc) (F1 : Fork) (c1 c2 : Ctx) (row : Aff) (p : Psc),
      tscIn H.ztF P.y.h.lt (nEndT P.y) 1 F c = .ok ((tT, F1), c1) ∧ Still c1 c2 ∧
      pscRow tT.p zeroE {} F1 c2 = .ok (((row, p), G), c2) ∧ Still c2 c' ∧
      H' = { H with tT := some { tT with p := p }, KT := row.scale (negE (invE tT.p.eps)) } := by
  simp only [hearTerms, hne, Bool.false_eq_true, if_false] at h
  obtain ⟨tT, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨_, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨e2, s2⟩ := check_still _ _ _ _ _ _ _ h2
  obtain ⟨⟨row, p⟩, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨_, F4, c4, h4, k4⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨e4, s4⟩ := note_still _ _ _ _ _ _ _ h4
  obtain ⟨_, F5, c5, h5, k5⟩ := (bind_ok _ _ _ _ _).1 k4
  obtain ⟨e5, s5⟩ := note_still _ _ _ _ _ _ _ h5
  obtain ⟨e6, e7, e8⟩ := (pure_ok _ _ _ _ _ _).1 k5
  have e3 : c3 = c2 := (pscRow_ok _ _ _ _ _ _ _ _ _ h3).1
  rw [e2, e3] at h3
  rw [e3] at s4
  rw [e8]
  refine ⟨tT, F1, c1, c2, row, p, h1, s2, ?_, s4.trans s5, e6⟩
  rw [e7, e5, e4]
  exact h3

/-- The test on the drawn coefficient. If no test on values is marked as failed behind hearTerms,
on a view, the coefficient that the terms' sumcheck drew is not 0. -/
theorem terms_coin (P : Pub) (H H' : Heard) (F G : Fork) (c c' : Ctx)
    (hne : P.rd.tscCalls.isEmpty = false) (h : hearTerms P H F c = .ok ((H', G), c'))
    (hm : c'.failed = none) (hv : c'.ch.dry = false) :
    ∃ tT : Tsc, H'.tT = some tT ∧ isZeroE tT.p.eps = false := by
  simp only [hearTerms, hne, Bool.false_eq_true, if_false] at h
  obtain ⟨tT, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨_, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨⟨row, p⟩, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨_, F4, c4, h4, k4⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨_, F5, c5, h5, k5⟩ := (bind_ok _ _ _ _ _).1 k4
  obtain ⟨e6, _, e8⟩ := (pure_ok _ _ _ _ _ _).1 k5
  obtain ⟨e3, _, ep, _⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h3
  have n4 : c4.failed = c3.failed ∧ c4.ch = c3.ch := by
    have y := ((lift_ok _ _ _ _ _ _).1 h4).1
    unfold Blk.note at y
    rw [← (Prod.mk.inj (Except.ok.inj y)).2]
    split <;> exact ⟨rfl, rfl⟩
  have n5 : c5.failed = c4.failed ∧ c5.ch = c4.ch := by
    have y := ((lift_ok _ _ _ _ _ _).1 h5).1
    unfold Blk.note at y
    rw [← (Prod.mk.inj (Except.ok.inj y)).2]
    split <;> exact ⟨rfl, rfl⟩
  rw [e8, n5.1, n4.1, e3] at hm
  rw [e8, n5.2, n4.2, e3] at hv
  refine ⟨{ tT with p := p }, by rw [e6], ?_⟩
  show isZeroE p.eps = false
  rw [ep]
  show isZeroE tT.p.eps = false
  have y := ((lift_ok _ _ _ _ _ _).1 h2).1
  unfold Blk.check at y
  split at y
  · rename_i hb
    have e2 := (Prod.mk.inj (Except.ok.inj y)).2
    rw [← e2] at hm hv
    rw [hv, hm] at hb
    simpa using hb
  · have e2 := (Prod.mk.inj (Except.ok.inj y)).2
    rw [← e2] at hm
    cases hm

/-- What hearTerms has heard, with its record. -/
theorem terms_heard (P : Pub) (H H' : Heard) (F G : Fork) (c c' : Ctx)
    (hne : P.rd.tscCalls.isEmpty = false) (h : hearTerms P H F c = .ok ((H', G), c'))
    (hs : Sized F) :
    ∃ (tT : Tsc) (F1 : Fork) (xCl : E) (H3 : PscH) (p : Psc),
      HeardL [.sum [xCl] (tokenWeights H.ztF P.y.h.lt) 1 H3, .idle] c c' ∧
      TokSaid H.ztF P.y.h.lt (nEndT P.y) 1 F F1 tT xCl H3 ∧
      p = { tT.p with rowMade := true } ∧
      Filled F1 G tT.p.first (List.replicate tT.p.walk.1.length zeroE) (subE zeroE oneE) ∧
      H' = { H with tT := some { tT with p := p },
                    KT := (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps)) } := by
  obtain ⟨tT, F1, c1, c2, row, p, a1, a2, a3, a4, a5⟩ := hearTerms_ran P H H' F G c c' hne h
  obtain ⟨xCl, H3, b1, b2⟩ := tok_heard _ _ _ _ F F1 c c1 tT a1 hs
  obtain ⟨_, d2, d3, d4⟩ := pscRow_filled _ _ _ _ _ _ _ _ _ a3 b2.sized
  refine ⟨tT, F1, xCl, H3, p, ?_, b2, d3, d4, ?_⟩
  · exact HeardL.append [_] [_] c c1 c' b1 (a2.trans a4).heard
  · rw [a5, d2]

/-! ### Routines that hear nothing and leave the state -/

/-- The routine, where it succeeds, leaves the state and the context as they were. -/
def Quiet {α : Type} (x : SubM α) : Prop :=
  ∀ F c a G c', x F c = .ok ((a, G), c') → G = F ∧ c' = c

theorem Quiet.bind {α β : Type} {x : SubM α} {f : α → SubM β} (hx : Quiet x)
    (hf : ∀ a, Quiet (f a)) : Quiet (x >>= f) := fun F c b G c' h => by
  obtain ⟨a, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨e1, e2⟩ := hx _ _ _ _ _ h1
  rw [e1, e2] at k1
  exact hf a _ _ _ _ _ k1

theorem quiet_pure {α : Type} (a : α) : Quiet (pure a : SubM α) :=
  fun _ _ _ _ _ h => ((pure_ok _ _ _ _ _ _).1 h).2

theorem quiet_form {α : Type} (x : Option α) : Quiet (form x) :=
  fun _ _ _ _ _ h => ((getS_ok _ _ _ _ _ _).1 h).2

theorem quiet_mustAs (name : String) (b : Bool) : Quiet (liftM (mustAs name b) : SubM Unit) :=
  fun _ _ _ _ _ h => by
    obtain ⟨m, e⟩ := (lift_ok _ _ _ _ _ _).1 h
    exact ⟨e, ((mustAs_ok _ _ _ _ _).1 m).2⟩

theorem quiet_shown (j : Nat) : Quiet (SubM.shown j) :=
  fun _ _ _ _ _ h => ((shownS_ok _ _ _ _ _ _).1 h).2

theorem quiet_mapM {α β : Type} (f : α → SubM β) (hf : ∀ a, Quiet (f a)) :
    ∀ l : List α, Quiet (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact quiet_pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (quiet_mapM f hf l).bind fun _ => quiet_pure _

theorem quiet_shownRun (first n : Nat) : Quiet (shownRun first n) := by
  unfold shownRun
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind]
  exact (quiet_mapM _ (fun _ => quiet_shown _) _).bind fun _ => quiet_pure _

theorem quiet_joinStart (v : Env) (H : Heard) (om : Array E) : Quiet (joinStart v H om) := by
  unfold joinStart
  refine (quiet_form _).bind fun _ => (quiet_form _).bind fun _ => (quiet_mustAs _ _).bind fun _ =>
    (quiet_form _).bind fun _ => Quiet.bind ?_ fun _ => quiet_pure _
  unfold Forest.paddingLaid
  exact quiet_mustAs _ _

/-! ### The draw that combines, and the batched sumcheck -/

/-- A sumcheck's parts with a step between the first round and the others that turns the kept notes
or the name of a failed test alone: the parts were heard as if that step came last. As `seam`
(OnBytes/Tie/Pv/Psc/Run/PscSeam.lean), without riders. -/
theorem seam_gap (C : Aff) (p0 p1 p2 : Psc) (ws : List Weight) (rs : List (List E × E))
    (dY n e : Nat) (F1 F2 F3 G : Fork) (c1 c2 c2' c3 c' : Ctx)
    (hb : pscBegin C F1 c1 = .ok ((p0, F2), c2)) (hg : Still c2 c2')
    (hm : (hearMany (ws.map fun w => w.d - 1)).Yields c2' rs c3) (hs : Stepped p0 p1 ws rs)
    (he : pscEnds p1 dY n F3 c3 = .ok (((e, p2), G), c')) (hz : Sized F3) :
    ∃ (τ mu : E) (sentY : List E) (beta : E) (v : List E) (d' : Ctx),
      F1.publicPart C = some τ ∧ F2 = taken F1 1 ∧
      Parts c1 c1 d' [] mu p0.eps ws rs dY sentY beta v ∧ Still d' c' ∧
      Ended p2 C τ mu p0.eps F1.next ws rs dY sentY beta ∧
      sentY.length = dY ∧ v.length = n ∧ e = F3.next + dY ∧
      Filled (taken F3 (dY + n)) G e v beta := by
  obtain ⟨τ, mu, pc, yc, hp0, Gc⟩ := pscBegin_ok C F1 F2 c1 c2 p0 hb
  obtain ⟨sentY, beta, v, c5, c6, y5, y6, y7, sv, _, _, _, sY, hp2, hE, HG⟩ :=
    pscEnds_ok p1 p2 dY n F3 G c3 c' e he
  have ran : Ran p1 C τ mu p0.eps F1.next ws rs := by
    have := (Ran.begun p0 C τ mu F1.next hp0).step hs
    simpa using this
  have lv : v.toList.length = n := by simpa using sv
  obtain ⟨nn, ff, rfl, hk⟩ := hg
  obtain ⟨d3, g3, rfl⟩ := slides_hearMany _ c2 nn ff _ _ hm
  obtain ⟨d5, g5, rfl⟩ := slides_hearOne _ _ _ _ d3 nn ff _ _ y5
  obtain ⟨d6, g6, rfl⟩ := slides_recvEs _ d5 nn ff _ _ y6
  obtain ⟨d7, g7, rfl⟩ := slides_closeEmpty _ d6 nn ff _ _ y7
  have em : d7.failed = c2.failed := by
    rw [keeps_mark (slides_closeEmpty _) g7, keeps_mark (slides_recvEs _) g6,
      keeps_mark (slides_hearOne _ _ _ _) g5, keeps_mark (slides_hearMany _) g3]
  exact ⟨τ, mu, sentY, beta, v.toList, d7, pc, Gc,
    ⟨c2, d3, d5, d6, recvEs_zero c1, yc, g3, g5, by rw [lv]; exact g6, g7⟩,
    ⟨nn, ff, rfl, fun hs => by rw [em] at hs ⊢; exact hk hs⟩,
    ran.ends dY sentY beta hp2, sY, lv, hE, hideRun_ok _ _ _ _ _ HG (sized_taken F3 _ hz)⟩

/-- What the batched sumcheck has said. C: its start form. -/
structure StackSaid (lamS n : Nat) (C : Aff) (F G : Fork) (K : HeardStack) (p : Psc) (H : PscH) :
    Prop where
  rounds : H.rs.length = lamS
  sizes : ∀ y ∈ (List.replicate lamS (Weight.plain 3)).zip H.rs, y.2.1.length + 1 = y.1.d
  sentY : H.sentY.length = 2
  vals : H.v.length = n
  /-- the sumcheck's record, with the public part of the start form -/
  psc : ∃ τ : E, F.publicPart C = some τ ∧
    Ended p C τ H.mu H.eps F.next (List.replicate lamS (Weight.plain 3)) H.rs 2 H.sentY H.beta
  /-- the challenges, by the bit that each belongs to -/
  rs : K.rs.toList = (H.rs.map (·.2)).reverse
  sA0 : K.sA0 = F.next + 1 + 2 * lamS + 2
  row : K.rowS = p.rowForm (mulE K.fin.As K.fin.Bs) {}

/-- What else hearStack's success says: the tests on public numbers, the slots, and how the two
sides' values at the end point are made from what was shown. -/
structure StackFin (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) (tT : Tsc) (K : HeardStack)
    (om : Array E) (F1 F4 : Fork) (c1 c5 : Ctx) : Prop where
  sH1 : K.sH1 = K.sA0 + 1
  sB0 : K.sB0 = K.sA0 + 1 + (1 + (if P.y.h.p3 then P.y.LamM else 0))
  sV : K.sV = K.sA0 + 1 + (1 + (if P.y.h.p3 then P.y.LamM else 0)) + 1
  fin : ∃ (shownT : Array E) (TS : List Nat) (pans : Panels) (xH xV : Array E) (a0 b0 : E),
    shownRun tT.sEnd (nEndT P.y) F1 c1 = .ok ((shownT, F1), c1) ∧ callsTS P = some TS ∧
    panelsT { v, e := H.fo.e, shownT, zt := H.ztF, stubO := stubO P.y } TS
      (panelsA { v, e := H.fo.e, shownT, zt := H.ztF, stubO := stubO P.y } {}) = some pans ∧
    ceilLog2 (placePanels pans.bl).2 = lamS ∧ pans.nextV = NCLp ∧
    shownRun (K.sA0 + 1) (1 + (if P.y.h.p3 then P.y.LamM else 0)) F4 c5 = .ok ((xH, F4), c5) ∧
    shownRun (K.sA0 + 1 + (1 + (if P.y.h.p3 then P.y.LamM else 0)) + 1) NCLp F4 c5 =
      .ok ((xV, F4), c5) ∧
    F4.shown K.sA0 = some a0 ∧
    F4.shown (K.sA0 + 1 + (1 + (if P.y.h.p3 then P.y.LamM else 0))) = some b0 ∧
    stackEnd P.y (placePanels pans.bl).1 K.rs lamS om xH xV a0 b0 = some K.fin

/-- The calls of hearStack that hear or that turn the state, where the terms were heard. -/
theorem hearStack_ran (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) (tT : Tsc)
    (hT : H.tT = some tT) (K : HeardStack) (F G : Fork) (c c' : Ctx)
    (h : hearStack P v H lamS NCLp F c = .ok ((K, G), c')) :
    ∃ (om : Array E) (C : Aff) (p0 : Psc) (st : Stack) (p2 p3 : Psc) (F1 F2 F3 F4 : Fork)
      (c1 c2 c3 c4 c5 : Ctx),
      SubM.batch 2 F c = .ok ((om, F1), c1) ∧
      joinStart v H om F1 c1 = .ok ((C, F1), c1) ∧
      pscBegin C F1 c1 = .ok ((p0, F2), c2) ∧ Still c2 c3 ∧
      stackRounds { lam := lamS, p := p0 } F2 c3 = .ok ((st, F3), c4) ∧
      pscEnds st.p 2 (2 + (1 + (if P.y.h.p3 then P.y.LamM else 0)) + NCLp) F3 c4 =
        .ok (((K.sA0, p2), F4), c5) ∧
      pscRow p2 (mulE K.fin.As K.fin.Bs) {} F4 c5 = .ok (((K.rowS, p3), G), c5) ∧ Still c5 c' ∧
      K.rs = st.rs ∧ StackFin P v H lamS NCLp tT K om F1 F4 c1 c5 := by
  simp only [hearStack, hT, Option.isSome_some, if_true] at h
  obtain ⟨om, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨shownT, Fa, ca, ha, ka⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨ea, ea'⟩ := quiet_shownRun _ _ _ _ _ _ _ ha
  obtain ⟨TS, Fb, cb, hb, kb⟩ := (bind_ok _ _ _ _ _).1 ka
  obtain ⟨vb, eb, eb'⟩ := (getS_ok _ _ _ _ _ _).1 hb
  obtain ⟨pans, Fd, cd, hd, kd⟩ := (bind_ok _ _ _ _ _).1 kb
  obtain ⟨vd, ed, ed'⟩ := (getS_ok _ _ _ _ _ _).1 hd
  obtain ⟨_, Fe, ce, he, ke⟩ := (bind_ok _ _ _ _ _).1 kd
  obtain ⟨ee, ee'⟩ := quiet_mustAs _ _ _ _ _ _ _ he
  have ve := ((mustAs_ok _ _ _ _ _).1 ((lift_ok _ _ _ _ _ _).1 he).1).1
  obtain ⟨C, Ff, cf, hf, kf⟩ := (bind_ok _ _ _ _ _).1 ke
  obtain ⟨ef, ef'⟩ := quiet_joinStart _ _ _ _ _ _ _ _ hf
  have gF : Fe = F1 := by rw [ee, ed, eb, ea]
  have gc : ce = c1 := by rw [ee', ed', eb', ea']
  rw [gF, gc] at hf
  rw [gF] at ef
  rw [gc] at ef'
  rw [ef, ef'] at hf kf
  obtain ⟨p0, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 kf
  obtain ⟨_, N1, d1, n1, j1⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨a1, s1⟩ := note_still _ _ _ _ _ _ _ n1
  obtain ⟨_, N2, d2, n2, j2⟩ := (bind_ok _ _ _ _ _).1 j1
  obtain ⟨a2, s2⟩ := note_still _ _ _ _ _ _ _ n2
  rw [a2, a1] at j2
  obtain ⟨st, F3, c4, h3, k3⟩ := (bind_ok _ _ _ _ _).1 j2
  obtain ⟨_, Fg, cg, hg, kg⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨eg, eg'⟩ := quiet_mustAs _ _ _ _ _ _ _ hg
  have vg := ((mustAs_ok _ _ _ _ _).1 ((lift_ok _ _ _ _ _ _).1 hg).1).1
  rw [eg, eg'] at kg
  obtain ⟨⟨sA0, p2⟩, F4, c5, h4, k4⟩ := (bind_ok _ _ _ _ _).1 kg
  obtain ⟨x1, Fh, ch, hh, kh⟩ := (bind_ok _ _ _ _ _).1 k4
  obtain ⟨eh, eh'⟩ := quiet_shownRun _ _ _ _ _ _ _ hh
  obtain ⟨x2, Fi, ci, hi, ki⟩ := (bind_ok _ _ _ _ _).1 kh
  obtain ⟨ei, ei'⟩ := quiet_shownRun _ _ _ _ _ _ _ hi
  obtain ⟨x3, Fj, cj, hj, kj⟩ := (bind_ok _ _ _ _ _).1 ki
  obtain ⟨vj, ej, ej'⟩ := (shownS_ok _ _ _ _ _ _).1 hj
  obtain ⟨x4, Fk, ck, hk, kk⟩ := (bind_ok _ _ _ _ _).1 kj
  obtain ⟨vk, ek, ek'⟩ := (shownS_ok _ _ _ _ _ _).1 hk
  obtain ⟨fin, Fl, cl, hl, kl⟩ := (bind_ok _ _ _ _ _).1 kk
  obtain ⟨vl, el, el'⟩ := (getS_ok _ _ _ _ _ _).1 hl
  have gF4 : Fl = F4 := by rw [el, ek, ej, ei, eh]
  have gc5 : cl = c5 := by rw [el', ek', ej', ei', eh']
  rw [gF4, gc5] at kl
  obtain ⟨⟨rowS, p3⟩, F5, c6, h5, k5⟩ := (bind_ok _ _ _ _ _).1 kl
  have e6 : c6 = c5 := (pscRow_ok _ _ _ _ _ _ _ _ _ h5).1
  obtain ⟨_, N3, d3, n3, j3⟩ := (bind_ok _ _ _ _ _).1 k5
  obtain ⟨a3, s3⟩ := note_still _ _ _ _ _ _ _ n3
  obtain ⟨_, N4, d4, n4, j4⟩ := (bind_ok _ _ _ _ _).1 j3
  obtain ⟨a4, s4⟩ := note_still _ _ _ _ _ _ _ n4
  obtain ⟨_, N5, d5, n5, j5⟩ := (bind_ok _ _ _ _ _).1 j4
  obtain ⟨a5, s5⟩ := note_still _ _ _ _ _ _ _ n5
  obtain ⟨g1, g2, g3⟩ := (pure_ok _ _ _ _ _ _).1 j5
  rw [e6] at h5 s3
  rw [ea, ea'] at ha
  rw [eh, eh'] at hh
  rw [ei, ei', eh, eh'] at hi
  rw [ei, eh] at vj
  rw [ej, ei, eh] at vk
  rw [g1, g2, g3, a5, a4, a3]
  exact ⟨om, C, p0, st, p2, p3, F1, F2, F3, F4, c1, c2, d2, c4, c5, h1, hf, h2, s1.trans s2,
    h3, h4, h5, (s3.trans s4).trans s5, rfl,
    ⟨rfl, rfl, rfl, shownT, TS, pans, x1, x2, x3, x4, ha, vb, vd, by simpa using ve,
      by simpa using vg, hh, hi, vj, vk, vl⟩⟩

/-- What hearStack has heard, with its record. -/
theorem stack_heard (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) (tT : Tsc)
    (hT : H.tT = some tT) (K : HeardStack) (F G : Fork) (c c' : Ctx)
    (h : hearStack P v H lamS NCLp F c = .ok ((K, G), c')) (hs : Sized F) :
    ∃ (x : E) (C : Aff) (p : Psc) (H4 : PscH) (F4 : Fork) (c1 c5 : Ctx),
      HeardL [.bat [] 2 x, .sum [] (List.replicate lamS (Weight.plain 3)) 2 H4, .idle] c c' ∧
      joinStart v H (powers x 2) F c1 = .ok ((C, F), c1) ∧
      StackSaid lamS (2 + (1 + (if P.y.h.p3 then P.y.LamM else 0)) + NCLp) C F G K p H4 ∧
      Filled (taken F (1 + 2 * lamS + (2 + (2 + (1 + (if P.y.h.p3 then P.y.LamM else 0)) + NCLp))))
        F4 K.sA0 H4.v H4.beta ∧
      Filled F4 G p.first (List.replicate p.walk.1.length zeroE) (subE zeroE oneE) ∧
      StackFin P v H lamS NCLp tT K (powers x 2) F F4 c1 c5 := by
  obtain ⟨om, C, p0, st, p2, p3, F1, F2, F3, F4, c1, c2, c3, c4, c5, h1, h2, h3, s3, h4, h5,
    h6, s6, e7, fn⟩ := hearStack_ran P v H lamS NCLp tT hT K F G c c' h
  obtain ⟨eF, x, b1, b2⟩ := batch_heardL 2 F F1 c c1 om h1 [] c (recvEs_zero c)
  rw [eF] at h2 h3 fn
  rw [b2] at h2 fn
  obtain ⟨rs, y4, st4, r4, _, G4⟩ := stackRounds_ok _ st F2 F3 c3 c4 h4
  obtain ⟨_, _, _, _, _, Gc⟩ := pscBegin_ok C F F2 c1 c2 p0 h3
  have hz : Sized F3 := by
    rw [G4, Gc]
    exact sized_taken _ _ (sized_taken _ _ hs)
  obtain ⟨τ, mu, sentY, beta, vv, d', a1, _, a3, a4, a5, a6, a7, a8, a9⟩ :=
    seam_gap C p0 st.p p2 (List.replicate lamS (Weight.plain 3)) rs 2 _ K.sA0 F F2 F3 F4 c1 c2 c3
      c4 c5 h3 s3 y4 st4 h5 hz
  obtain ⟨_, d2, _, d4⟩ := pscRow_filled p2 p3 _ _ _ F4 G c5 c5 h6 a9.sized
  have hn : F3.next = F.next + 1 + 2 * lamS := by
    rw [G4, Gc]
    rfl
  refine ⟨x, C, p2, ⟨mu, p0.eps, rs, sentY, beta, vv⟩, F4, c1, c5, ?_, h2,
    ⟨by rw [st4.len, List.length_replicate], st4.sizes, a6, a7, ⟨τ, a1, a5⟩, by rw [e7]; exact r4,
      by rw [a8, hn], d2⟩, ?_, d4, fn⟩
  · exact HeardL.append [_] [_, _] c c1 c' b1
      (HeardL.append [_] [_] c1 d' c' ⟨c1, d', a3, rfl⟩ (a4.trans s6).heard)
  · have e : taken F3 (2 + (2 + (1 + (if P.y.h.p3 then P.y.LamM else 0)) + NCLp)) =
        taken F (1 + 2 * lamS + (2 + (2 + (1 + (if P.y.h.p3 then P.y.LamM else 0)) + NCLp))) := by
      rw [G4, Gc, taken_taken, taken_taken]
      exact congrArg (taken F) (Nat.add_assoc 1 (2 * lamS) _).symm
    rw [← e]
    exact a9

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.tok_heard
#print axioms OnBytes.Tie.Pv.Lay.rows_heard
#print axioms OnBytes.Tie.Pv.Lay.hearTerms_ran
#print axioms OnBytes.Tie.Pv.Lay.terms_heard
#print axioms OnBytes.Tie.Pv.Lay.terms_coin
#print axioms OnBytes.Tie.Pv.Lay.quiet_joinStart
#print axioms OnBytes.Tie.Pv.Lay.seam_gap
#print axioms OnBytes.Tie.Pv.Lay.hearStack_ran
#print axioms OnBytes.Tie.Pv.Lay.stack_heard
