-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookLayerMid.lean.
The layers' sub-proof: the claims that it adds between its lookup's two groups of claims are a list
that is fixed before the state.

Between `Forest.objects` and `Layer.claimsPlanes` the layers' check adds claims of its own. This
file names that stretch as one routine and states that the list of the claims which it adds is a
function, chosen before the state of the sub-proof, of two things: the arrays' numbers of columns,
and the values that are shown under the end slots of the first token sumcheck.

Main names:
  `shownArr F first n`: the values shown under the n slots from first on (the field vp), in the
    state F.
  `shownRun_ok`: a run of `Layer.shownRun` that returns turns nothing and returns `shownArr`; the
    slots are filled.
  `layerMid P o`: the stretch, in the program's order and words. That the layers' check runs it is
    not said here: see `layerMid_eq` (FoLookLayerTied) and `g_run_tied` (FoTiedG).
  `nShown P o`: the number of end slots that the norms' rows read: four or three for each norm.
  `layerMid_added`: there is a function A such that every run of `layerMid P o` that returns, from F
    to G, has added the list A (shownArr G ..) (colsOf F) (`Added`, FoAdded); G has F's numbers of
    columns, is a later state than F, and its arrays have their sizes.

Under: F has one coefficient for each slot, and its arrays have their sizes.

Limit: which claims stand in the list is not said. A is chosen behind the records P and o, so it can
hang on them: that o holds nothing that was drawn with or after theta is not said here. The other
limits of `Fixed` (FoFixed) hold of A too. The shown values are read in the state behind the
stretch; that they were laid there before theta was drawn, and so do not hang on it, is not said
here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixed
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsLayer
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsOf
import OnBytes.Tie.Pv.Lookup.Ends.FoLookLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun Cb.Fo

/-- The values shown under the n slots from first on (the field vp). -/
def shownArr (F : Fork) (first n : ℕ) : Array E :=
  ((List.range n).map fun i => F.vp.getD (first + i) zeroE).toArray

theorem shown_some {F : Fork} {j : ℕ} {y : E} (h : F.shown j = some y) :
    y = F.vp.getD j zeroE ∧ Filled F j := by
  unfold Fork.shown at h
  split at h
  · rename_i hb
    rw [Bool.and_eq_true] at hb
    exact ⟨(Option.some.inj h).symm, hb.2⟩
  · exact absurd h (by simp)

theorem mapM_shown (first : ℕ) : ∀ (l : List ℕ) (Fk : Fork) (c : Ctx) (r : (List E × Fork) × Ctx),
    (l.mapM fun i => SubM.shown (first + i)) Fk c = .ok r →
    r = ((l.map fun i => Fk.vp.getD (first + i) zeroE, Fk), c) ∧ ∀ i ∈ l, Filled Fk (first + i)
  | [], Fk, c, r, h => by
    rw [List.mapM_nil] at h
    exact ⟨(pure_ok _ _ _ _).1 h, fun _ hi => absurd hi List.not_mem_nil⟩
  | a :: l, Fk, c, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨y', e1, r1⟩ := (ask_ok _ _ _ _).1 h1
    simp only [Prod.mk.injEq] at r1
    obtain ⟨⟨ry, rF⟩, rc⟩ := r1
    rw [rF, rc] at k1
    obtain ⟨ys, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
    obtain ⟨e2, f2⟩ := mapM_shown first l Fk c _ h2
    simp only [Prod.mk.injEq] at e2
    obtain ⟨⟨sy, sF⟩, sc⟩ := e2
    have e3 := (pure_ok _ _ _ _).1 k2
    obtain ⟨v1, v2⟩ := shown_some e1
    refine ⟨?_, fun i hi => ?_⟩
    · rw [e3, ry, sy, sF, sc, v1]
      rfl
    · rcases List.mem_cons.mp hi with rfl | hi'
      · exact v2
      · exact f2 i hi'

/-- A run of `Layer.shownRun` that returns. -/
theorem shownRun_ok (first n : ℕ) (F : Fork) (c : Ctx) (r : (Array E × Fork) × Ctx)
    (h : Layer.shownRun first n F c = .ok r) :
    r = ((shownArr F first n, F), c) ∧ ∀ i, i < n → Filled F (first + i) := by
  unfold Layer.shownRun at h
  rw [Array.mapM_eq_mapM_toList, ← bind_pure_comp] at h
  obtain ⟨ys, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  rw [Array.toList_range] at h1
  obtain ⟨e1, f1⟩ := mapM_shown first _ F c _ h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨⟨sy, sF⟩, sc⟩ := e1
  have e3 := (pure_ok _ _ _ _).1 k1
  refine ⟨?_, fun i hi => f1 i (List.mem_range.mpr hi)⟩
  rw [e3, sy, sF, sc]
  rfl

/-- In a later state the same values stand under slots that were filled. -/
theorem shownArr_later {F G : Fork} (h : Later F G) (first n : ℕ)
    (hf : ∀ i, i < n → Filled F (first + i)) : shownArr G first n = shownArr F first n := by
  unfold shownArr
  refine congrArg List.toArray (List.map_congr_left fun i hi => ?_)
  exact (h.keep _ (hf i (List.mem_range.mp hi))).2.1

/-- A public test, the shown values, and a routine that is fixed at each array of values. -/
theorem fixed_shown (name : String) (b : Bool) (first n : ℕ) {f : Array E → SubM Unit}
    (hf : ∀ S, Fixed (f S)) :
    ∃ L : Array E → (ℕ → ℕ) → List Cl, ∀ (F : Fork) (c : Ctx) (a : Unit) (G : Fork) (c' : Ctx),
      (do mustAs name b; let sh ← Layer.shownRun first n; f sh : SubM Unit) F c =
        .ok ((a, G), c') → F.LS.size = F.ns →
      Added F G (L (shownArr F first n) (colsOf F)) ∧ colsOf G = colsOf F ∧
        ∀ i, i < n → Filled F (first + i) := by
  choose v L H using hf
  refine ⟨L, fun F c a G c' hr hs => ?_⟩
  obtain ⟨_, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, e1⟩ := (mustAs_ok _ _ _ _ _).1 h1
  simp only [Prod.mk.injEq] at e1
  obtain ⟨⟨_, rF⟩, rc⟩ := e1
  rw [rF, rc] at k1
  obtain ⟨S, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨e2, f2⟩ := shownRun_ok first n F c _ h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨sS, sF⟩, sc⟩ := e2
  rw [sS, sF, sc] at k2
  obtain ⟨_, a2, a3⟩ := H _ F c a G c' k2 hs
  exact ⟨a2, a3, f2⟩

theorem fixed_ledger5 (v : Layer.Env) (H : Layer.Heard) :
    ∃ L : Array E → (ℕ → ℕ) → List Cl, ∀ (F : Fork) (c : Ctx) (a : Unit) (G : Fork) (c' : Ctx),
      Layer.claimsLedger5 v H F c = .ok ((a, G), c') → F.LS.size = F.ns →
      Added F G (L (shownArr F H.tV.sEnd (4 * v.y.NI)) (colsOf F)) ∧ colsOf G = colsOf F ∧
        ∀ i, i < 4 * v.y.NI → Filled F (H.tV.sEnd + i) := by
  unfold Layer.claimsLedger5
  exact fixed_shown _ _ _ _ fun S => by fixed

theorem fixed_ledger4 (v : Layer.Env) (H : Layer.Heard) :
    ∃ L : Array E → (ℕ → ℕ) → List Cl, ∀ (F : Fork) (c : Ctx) (a : Unit) (G : Fork) (c' : Ctx),
      Layer.claimsLedger4 v H F c = .ok ((a, G), c') → F.LS.size = F.ns →
      Added F G (L (shownArr F H.tV.sEnd (3 * v.y.NI)) (colsOf F)) ∧ colsOf G = colsOf F ∧
        ∀ i, i < 3 * v.y.NI → Filled F (H.tV.sEnd + i) := by
  unfold Layer.claimsLedger4
  exact fixed_shown _ _ _ _ fun S => by fixed

theorem fixed_noteClaims (s : String) : Fixed (Layer.noteClaims s) :=
  Fixed.unit fun F c a G c' hr hs => by
    unfold Layer.noteClaims at hr
    obtain ⟨x, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 hr
    have e : ((F, F), c) = ((x, F1), c1) := Except.ok.inj h1
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨_, eF⟩, _⟩ := e
    have k2 : (StateT.lift (Blk.note ("layer: " ++ ("c0 after " ++ s)) x.c0) : SubM Unit) F1 c1 =
        .ok ((a, G), c') := k1
    obtain ⟨_, _, _, e2⟩ := (lift_ok _ _ _ _).1 k2
    have e3 : G = F1 := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e2
    rw [e3, ← eF]
    exact ⟨Added.refl hs, rfl⟩

/-- The layers' own claims between `Forest.objects` and `Layer.claimsPlanes`. -/
def layerMid (P : Layer.Pub) (o : Layer.Own) : SubM Unit := do
  Layer.noteClaims "the look-up's own claims"
  Layer.claimsNorms P o.v o.H
  Layer.noteClaims "the sums of squares"
  Layer.claimRowBatch P.y o.H
  (if P.y.h.xl == 5 then Layer.claimsLedger5 o.v o.H else Layer.claimsLedger4 o.v o.H)
  Layer.noteClaims "the norms' rows"
  Layer.claimsTerms o.v o.H
  Layer.noteClaims "the second token sum-check's shown values"
  Layer.claimsGated P o.v o.hd o.hd2
  Layer.noteClaims "the gated products"
  Layer.claimsOneHot o.v

/-- The number of end slots that the norms' rows read. -/
def nShown (P : Layer.Pub) (o : Layer.Own) : ℕ :=
  if P.y.h.xl == 5 then 4 * o.v.y.NI else 3 * o.v.y.NI

theorem fixed_ledger (P : Layer.Pub) (o : Layer.Own) :
    ∃ L : Array E → (ℕ → ℕ) → List Cl, ∀ (F : Fork) (c : Ctx) (a : Unit) (G : Fork) (c' : Ctx),
      (if P.y.h.xl == 5 then Layer.claimsLedger5 o.v o.H else Layer.claimsLedger4 o.v o.H) F c =
        .ok ((a, G), c') → F.LS.size = F.ns →
      Added F G (L (shownArr F o.H.tV.sEnd (nShown P o)) (colsOf F)) ∧ colsOf G = colsOf F ∧
        ∀ i, i < nShown P o → Filled F (o.H.tV.sEnd + i) := by
  unfold nShown
  split
  · exact fixed_ledger5 o.v o.H
  · exact fixed_ledger4 o.v o.H

/-- **The list of the layers' own claims in that stretch is fixed before the state.** -/
theorem layerMid_added (P : Layer.Pub) (o : Layer.Own) :
    ∃ A : Array E → (ℕ → ℕ) → List Cl, ∀ (F G : Fork) (c c' : Ctx),
      layerMid P o F c = .ok (((), G), c') → F.LS.size = F.ns → Sized F →
      Added F G (A (shownArr G o.H.tV.sEnd (nShown P o)) (colsOf F)) ∧ colsOf G = colsOf F ∧
        Later F G ∧ Sized G := by
  obtain ⟨_, L1, H1⟩ := fixed_noteClaims "the look-up's own claims"
  obtain ⟨_, L2, H2⟩ : Fixed (Layer.claimsNorms P o.v o.H) := by fixed
  obtain ⟨_, L3, H3⟩ := fixed_noteClaims "the sums of squares"
  obtain ⟨_, L4, H4⟩ : Fixed (Layer.claimRowBatch P.y o.H) := by fixed
  obtain ⟨L5, H5⟩ := fixed_ledger P o
  obtain ⟨_, L6, H6⟩ := fixed_noteClaims "the norms' rows"
  obtain ⟨_, L7, H7⟩ : Fixed (Layer.claimsTerms o.v o.H) := by fixed
  obtain ⟨_, L8, H8⟩ := fixed_noteClaims "the second token sum-check's shown values"
  obtain ⟨_, L9, H9⟩ : Fixed (Layer.claimsGated P o.v o.hd o.hd2) := by fixed
  obtain ⟨_, L10, H10⟩ := fixed_noteClaims "the gated products"
  obtain ⟨_, L11, H11⟩ : Fixed (Layer.claimsOneHot o.v) := by fixed
  refine ⟨fun S k => L1 k ++ (L2 k ++ (L3 k ++ (L4 k ++ (L5 S k ++ (L6 k ++ (L7 k ++ (L8 k ++
    (L9 k ++ (L10 k ++ L11 k))))))))), fun F G c c' hr hs hF => ?_⟩
  unfold layerMid at hr
  obtain ⟨_, F1, c1, r1, k1⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, a1, q1⟩ := H1 _ _ _ _ _ r1 hs
  obtain ⟨l1, s1⟩ := Keeps.of r1 hF (by keeps)
  obtain ⟨_, F2, c2, r2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨_, a2, q2⟩ := H2 _ _ _ _ _ r2 a1.sized
  obtain ⟨l2, s2⟩ := Keeps.of r2 s1 (by keeps)
  obtain ⟨_, F3, c3, r3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨_, a3, q3⟩ := H3 _ _ _ _ _ r3 a2.sized
  obtain ⟨l3, s3⟩ := Keeps.of r3 s2 (by keeps)
  obtain ⟨_, F4, c4, r4, k4⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨_, a4, q4⟩ := H4 _ _ _ _ _ r4 a3.sized
  obtain ⟨l4, s4⟩ := Keeps.of r4 s3 (by keeps)
  obtain ⟨_, F5, c5, r5, k5⟩ := (bind_ok _ _ _ _ _).1 k4
  obtain ⟨a5, q5, f5⟩ := H5 _ _ _ _ _ r5 a4.sized
  obtain ⟨l5, s5⟩ := Keeps.of r5 s4 (by keeps)
  obtain ⟨_, F6, c6, r6, k6⟩ := (bind_ok _ _ _ _ _).1 k5
  obtain ⟨_, a6, q6⟩ := H6 _ _ _ _ _ r6 a5.sized
  obtain ⟨l6, s6⟩ := Keeps.of r6 s5 (by keeps)
  obtain ⟨_, F7, c7, r7, k7⟩ := (bind_ok _ _ _ _ _).1 k6
  obtain ⟨_, a7, q7⟩ := H7 _ _ _ _ _ r7 a6.sized
  obtain ⟨l7, s7⟩ := Keeps.of r7 s6 (by keeps)
  obtain ⟨_, F8, c8, r8, k8⟩ := (bind_ok _ _ _ _ _).1 k7
  obtain ⟨_, a8, q8⟩ := H8 _ _ _ _ _ r8 a7.sized
  obtain ⟨l8, s8⟩ := Keeps.of r8 s7 (by keeps)
  obtain ⟨_, F9, c9, r9, k9⟩ := (bind_ok _ _ _ _ _).1 k8
  obtain ⟨_, a9, q9⟩ := H9 _ _ _ _ _ r9 a8.sized
  obtain ⟨l9, s9⟩ := Keeps.of r9 s8 (by keeps)
  obtain ⟨_, F10, c10, r10, k10⟩ := (bind_ok _ _ _ _ _).1 k9
  obtain ⟨_, a10, q10⟩ := H10 _ _ _ _ _ r10 a9.sized
  obtain ⟨l10, s10⟩ := Keeps.of r10 s9 (by keeps)
  obtain ⟨_, a11, q11⟩ := H11 _ _ _ _ _ k10 a10.sized
  obtain ⟨l11, s11⟩ := Keeps.of k10 s10 (by keeps)
  have e2 : colsOf F1 = colsOf F := q1
  have e3 : colsOf F2 = colsOf F := q2.trans e2
  have e4 : colsOf F3 = colsOf F := q3.trans e3
  have e5 : colsOf F4 = colsOf F := q4.trans e4
  have e6 : colsOf F5 = colsOf F := q5.trans e5
  have e7 : colsOf F6 = colsOf F := q6.trans e6
  have e8 : colsOf F7 = colsOf F := q7.trans e7
  have e9 : colsOf F8 = colsOf F := q8.trans e8
  have e10 : colsOf F9 = colsOf F := q9.trans e9
  have e11 : colsOf F10 = colsOf F := q10.trans e10
  have lG : Later F4 G :=
    l5.trans (l6.trans (l7.trans (l8.trans (l9.trans (l10.trans l11)))))
  rw [e2] at a2
  rw [e3] at a3
  rw [e4] at a4
  rw [e5, ← shownArr_later lG _ _ f5] at a5
  rw [e6] at a6
  rw [e7] at a7
  rw [e8] at a8
  rw [e9] at a9
  rw [e10] at a10
  rw [e11] at a11
  exact ⟨a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans (a8.trans
    (a9.trans (a10.trans a11))))))))), q11.trans e11,
    l1.trans (l2.trans (l3.trans (l4.trans lG))), s11⟩

end Fo
