-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoMadeH.lean.
A record put together from runs of Head.hear and Head.tablesOf is made as Fo.MadeH says.

Fo.MadeH (OnBytes/Tie/Pv/Lookup/Ends/FoKeysH.lean) is the premise of all that is shown of the head's
key forms. This file shows it of a record whose fields x and t are what a run of Head.hear and a run
of Head.tablesOf returned, under what a caller knows of the public numbers.

States:
  testAs_view: a test on values, on a view, holds if the routine goes on.
  replyToken_ok: on a view the reply's token is an entry of the vocabulary; state and context are as
    before.
  hear_fields: a run of Head.hear from (F, c) on a view that returns the record x: Forest.pad
    returned x.g1 FROM (F.slots hp.ns, c); the merged point, the two calls' numbers and the checked
    tokens are what their routines give.
  made_of_run: so the record { h, L, b, hp, cov, x, t, iU3 } meets MadeH.
Premises of made_of_run: on the run: Head.hear returned x from a context ON A VIEW (not in the dry
run: there the test of the reply's token is idle, and MadeH's clause on it may fail); Head.tablesOf
returned t. On public numbers: the layout is Head.layout's; the covered positions are
Head.coveredOf's; the plan's list of matrices is Head.matsH's, and NM is its length.
Not tied: the state and the context in which Head.hear ends; those from which Head.tablesOf runs.
NOT SHOWN HERE: that the head's check (Head.runForkHidH2) runs the two routines with these arguments
and builds this record of what they return. No theorem of this file opens it: h_run_tied
(OnBytes/Tie/Pv/Lookup/Ends/FoTiedH.lean) does. No statement of this library draws this MadeH from
the check's own run (of another record of that name it is done: madeH_of_run,
Johnson/Road/HeadMade.lean).

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeysH
import OnBytes.Tie.Pv.Lookup.Ends.FoTabsH2

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- A test on values before a routine, on a view. -/
theorem testAs_view {β : Type} (name : String) (b : Bool) (f : Unit → SubM β) (F : Fork) (c : Ctx)
    (r : (β × Fork) × Ctx) (hd : c.ch.dry = false)
    (h : ((liftM (testAs name b) : SubM Unit) >>= f) F c = .ok r) :
    b = true ∧ f () F c = .ok r := by
  rw [bind_ok] at h
  obtain ⟨a, G, d, h1, h2⟩ := h
  obtain ⟨a', d', k1, k2⟩ := (lift_ok (testAs name b) F c _).1 h1
  have t1 : G = F := congrArg (fun y : (Unit × Fork) × Ctx => y.1.2) k2
  have t2 : d = d' := congrArg (fun y : (Unit × Fork) × Ctx => y.2) k2
  cases b with
  | false =>
    have z : (Except.error { name := name } : Except Failure (Unit × Ctx)) = .ok (a', d') := by
      have : testAs name false c = .error { name := name } := by
        have e : Blk.isDry c = .ok (false, c) := by
          unfold Blk.isDry
          rw [hd]
        show (Blk.isDry c >>= fun p => (if (false || p.1) = true then (pure () : Blk Unit)
          else refuse name) p.2) = _
        rw [e]
        rfl
      rw [← this]
      exact k1
    cases z
  | true =>
    have z : ((), c) = (a', d') := Except.ok.inj k1
    have z1 : c = d' := congrArg Prod.snd z
    rw [t1, t2, ← z1] at h2
    exact ⟨rfl, h2⟩

/-- On a view the reply's token is an entry of the vocabulary. -/
theorem replyToken_ok (plain : Array E) (V : ℕ) (F G : Fork) (c d : Ctx) (y : ℕ)
    (hd : c.ch.dry = false) (h : Head.replyToken plain V F c = .ok ((y, G), d)) :
    y < V ∧ G = F ∧ d = c := by
  unfold Head.replyToken at h
  dsimp only at h
  obtain ⟨_, h⟩ := bindMustAs_ok _ _ _ F c _ h
  obtain ⟨hb, h⟩ := testAs_view _ _ _ F c _ hd h
  have e := (pure_ok _ _ _ _).1 h
  have e0 : y = _ := congrArg (fun z : (ℕ × Fork) × Ctx => z.1.1) e
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨e0 ▸ hb.2, congrArg (fun z : (ℕ × Fork) × Ctx => z.1.2) e,
    congrArg (fun z : (ℕ × Fork) × Ctx => z.2) e⟩

/-- **What a run of Head.hear on a view puts into its record, as far as the key forms read it.** -/
theorem hear_fields (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (plain : Array E) (F G : Fork) (c c' : Ctx) (x : Head.Heard) (hd : c.ch.dry = false)
    (hr : Head.hear h L hp cov plain F c = .ok ((x, G), c')) :
    (∃ y, y < h.V ∧ x.win = Head.winOf cov h.T y) ∧
      (∃ F' c1, Forest.pad L.cl L.fs.pub h.LIDB (F.slots hp.ns) c = .ok ((x.g1, F'), c1)) ∧
      lastOf x.g1.zx h.la = .ok x.Zl ∧ Head.callNo L "NF" = some x.qN ∧
      Head.callNo L "HD0" = some x.qH := by
  unfold Head.hear at hr
  obtain ⟨y, A1, d1, h1, hr⟩ := (bind_ok _ _ F c _).1 hr
  obtain ⟨hy, s1, s2⟩ := replyToken_ok plain h.V F A1 c d1 y hd h1
  rw [s1, s2] at hr
  obtain ⟨_, A2, d2, h2, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  unfold SubM.slots at h2
  obtain ⟨G', hG, e2⟩ := (change_ok _ _ _ _).1 h2
  have hG' : F.slots hp.ns = G' := Option.some.inj hG
  have t1 : A2 = G' := congrArg (fun z : (Unit × Fork) × Ctx => z.1.2) e2
  have t2 : d2 = c := congrArg (fun z : (Unit × Fork) × Ctx => z.2) e2
  rw [t1, t2, ← hG'] at hr
  obtain ⟨g1, F', c1, hpad, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨Zl, A3, d3, h3, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  have hZ : lastOf g1.zx h.la = .ok Zl := by
    unfold Head.mergedPoint at h3
    obtain ⟨Z0, e3, h3⟩ := bindHeld_ok _ _ _ _ _ h3
    obtain ⟨_, A4, d4, _, h3⟩ := (bind_ok _ _ _ _ _).1 h3
    have e4 := (pure_ok _ _ _ _).1 h3
    have : Zl = Z0 := congrArg (fun z : (Array E × Fork) × Ctx => z.1.1) e4
    rw [this]
    exact e3
  obtain ⟨PV, A5, d5, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨⟨sW, gp, wpl⟩, A6, d6, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  dsimp only at hr
  obtain ⟨⟨sPv, omV, tV⟩, A7, d7, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  dsimp only at hr
  obtain ⟨qN, eN, hr⟩ := bindGetAs_ok _ _ _ _ _ _ hr
  obtain ⟨qH, eH, hr⟩ := bindGetAs_ok _ _ _ _ _ _ hr
  obtain ⟨tN, A8, d8, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨⟨tH, rs⟩, A9, d9, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  dsimp only at hr
  obtain ⟨_, B1, f1, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, B2, f2, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, B3, f3, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, B4, f4, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, B5, f5, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, B6, f6, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, B7, f7, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, B8, f8, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, B9, f9, _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, C1, g1', _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, C2, g2', _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, C3, g3', _, hr⟩ := (bind_ok _ _ _ _ _).1 hr
  have e9 := (pure_ok _ _ _ _).1 hr
  have ex : x = _ := congrArg (fun z : (Head.Heard × Fork) × Ctx => z.1.1) e9
  rw [ex]
  exact ⟨⟨y, hy, rfl⟩, ⟨F', c1, hpad⟩, hZ, eN, eH⟩

/-- **A record put together from the two runs meets MadeH.** -/
theorem made_of_run (h : Head.Shape) (L : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (cov : Head.Covered) (plain : Array E) (iU3 : ℕ) (F G : Fork) (c c' : Ctx) (x : Head.Heard)
    (hd : c.ch.dry = false) (hr : Head.hear h L hp cov plain F c = .ok ((x, G), c'))
    (F2 F3 : Fork) (c2 c3 : Ctx) (t : Head.Tables)
    (ht : Head.tablesOf h L hp cov x F2 c2 = .ok ((t, F3), c3))
    (hL : ∃ tau, Head.layout h tau = .ok L) (hC : ∃ so, Head.coveredOf so h.T h.V = .ok cov)
    (hM : ∃ gid sid, hp.tl.mats = Head.matsH h L b gid sid) (hNM : hp.tl.NM = hp.tl.mats.size) :
    MadeH { h := h, L := L, b := b, hp := hp, cov := cov, x := x, t := t, iU3 := iU3 } := by
  obtain ⟨hw, ⟨F', c1, hpad⟩, hZ, hN, hH⟩ := hear_fields h L hp cov plain F G c c' x hd hr
  exact ⟨hL, hC, hM, hNM, ⟨_, _, _, _, hpad⟩, hZ, hN, hH, hw, ⟨_, _, _, _, ht⟩⟩

end Fo
