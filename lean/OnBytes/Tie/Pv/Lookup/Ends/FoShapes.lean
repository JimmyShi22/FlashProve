-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoShapes.lean: at each of the four kinds of callers, the record of the
lookup's numbers that a run of Forest.pad lays down is the plan's own record, under a test on public
numbers.

The chain's plan of rounds at a lookup's place (linkRounds, OnBytes/Model/VerifySubproofs.lean) is
computed from Model.forestSize of the plan's record: X.y.fo, hp.tl.f9, a.fs, a.seam.tl.f9, X.HLy.fs,
X.H.tl.f9, where X is the verifier's record of public numbers (Verify.Public), hp one of its plans
for the layers and a one of its plans for attention. What is shown of a run speaks of g.shape, the
record that Forest.pad made anew. Here the two are tied, as far as the limits below say.

 - callsEq_of, shapeEq_of: what the tests callsEqB and shapeEqB pass is equal.
 - Made calls lid fs: Forest.shape calls lid returns some h0, and fs is h0 with fs's own numbers of
   padding keys. made_of_test: madeB (OnBytes/Tie/Pv/Lookup/Ends/FoShapesBDefs.lean) gives it.
 - shape_of_pad: if Forest.pad calls fs.pub lid returns g, and Made calls lid fs, then g.shape = fs.
   size_of_pad: so Model.forestSize g.shape = Model.forestSize fs.
 - g_shape_is: the layers: a run of Layer.hearLook y g that returns fo: fo.shape = y.fo.
 - a_shape_is: attention: a run of Attention.hear P that returns f: f.g.shape = P.fs.
 - h_shape_is: the head: a run of Head.hear h L hp cov plain that returns x: x.g1.shape = L.fs.
 - z_shape_is: the smallness test: a run of tl.transcriptF on a view (dry = false), from a state
   whose arrays have their sizes (Sized F), that returns r: r's smallness test keeps a record g
   (r.1.1.1.heard = some g), and g.shape = tl.f9.
 - g_size_is, a_size_is, h_size_is, z_size_is: the same for Model.forestSize.

Each under Made at the caller's own arguments; madeB is its test.
Not tied here: that the tl of a run of transcriptF has the z1, z2, lidb and f9 of the plan's tl;
that the y, P, h and L with which the other three routines run are those of the record X.
Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that the test is true
at any layout. By a run alone it is true at the nine lookups of the library's own example of a
parameter file (OnBytes/Model/TestConfig.lean); the file of that run, FoShapesTest.lean, is [not in
this library].

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoShapesBDefs
import OnBytes.Tie.Pv.Lookup.Ends.FoHearParts
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedLook
import OnBytes.Tie.Pv.Lookup.Ends.FoSiteOwn
import OnBytes.Tie.Pv.Lookup.Forest.FoPadShape
import OnBytes.Model.RoundSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem callsEq_of {a b : Array Call} (h : callsEqB a b = true) : a = b := by
  simp only [callsEqB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2⟩ := h
  apply Array.ext h1
  intro i hi1 hi2
  have e := callEq_of (h2 i hi1)
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi1,
    Array.getElem?_eq_getElem hi2] at e
  exact e

theorem shapeEq_of {a b : Forest.Shape} (h : shapeEqB a b = true) : a = b := by
  simp only [shapeEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  have h1' := callsEq_of h1
  cases a
  cases b
  dsimp only at h1' h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  subst h1' h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rfl

/-- The record fs is what Forest.shape makes of the calls, with fs's own padding numbers. -/
def Made (calls : Array Call) (lid : ℕ) (fs : Forest.Shape) : Prop :=
  ∃ h0, Forest.shape calls lid = .ok h0 ∧ fs = { h0 with pub := fs.pub }

theorem made_of_test {calls : Array Call} {lid : ℕ} {fs : Forest.Shape}
    (h : madeB calls lid fs = true) : Made calls lid fs := by
  unfold madeB at h
  cases e : Forest.shape calls lid with
  | error x => rw [e] at h; cases h
  | ok h0 =>
    rw [e] at h
    exact ⟨h0, e, shapeEq_of h⟩

/-- **The run's record is the plan's.** -/
theorem shape_of_pad {calls : Array Call} {lid : ℕ} {fs : Forest.Shape} {F F' : Fork} {c c' : Ctx}
    {g : Forest.Heard} (h : Forest.pad calls fs.pub lid F c = .ok ((g, F'), c'))
    (hM : Made calls lid fs) : g.shape = fs := by
  obtain ⟨M, P⟩ := pad_cut _ _ _ _ _ _ _ _ h
  obtain ⟨h0, e0, _, e1⟩ := pad_shapeOf P
  obtain ⟨h0', e0', e2⟩ := hM
  obtain rfl : h0 = h0' := Except.ok.inj (e0.symm.trans e0')
  rw [e1, ← e2]

theorem size_of_pad {calls : Array Call} {lid : ℕ} {fs : Forest.Shape} {F F' : Fork} {c c' : Ctx}
    {g : Forest.Heard} (h : Forest.pad calls fs.pub lid F c = .ok ((g, F'), c'))
    (hM : Made calls lid fs) : forestSize g.shape = forestSize fs := by
  rw [shape_of_pad h hM]

/-- The layers. -/
theorem g_shape_is (y : Layer.Lay) (g : ℕ) (F G : Fork) (c c' : Ctx) (fo : Forest.Heard)
    (h : Layer.hearLook y g F c = .ok ((fo, G), c')) (hM : Made y.cl y.h.lidb y.fo) :
    fo.shape = y.fo :=
  shape_of_pad (g_look_exact y g F G c c' fo h) hM

/-- Attention. -/
theorem a_shape_is (P : Attention.Plan) (F G : Fork) (c c' : Ctx) (f : Attention.First)
    (h : Attention.hear P F c = .ok ((f, G), c'))
    (hM : Made (P.S.calls.map (·.call)) P.lid P.fs) : f.g.shape = P.fs := by
  obtain ⟨F1, _, _, c1, _, _, hp, _⟩ := hear_parts P F G c c' f h
  exact shape_of_pad hp hM

/-- The head. -/
theorem h_shape_is (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (plain : Array E) (F G : Fork) (c c' : Ctx) (x : Head.Heard)
    (hr : Head.hear h L hp cov plain F c = .ok ((x, G), c')) (hM : Made L.cl h.LIDB L.fs) :
    x.g1.shape = L.fs := by
  obtain ⟨F', c1, hp', _⟩ := h_hear_exact h L hp cov plain F G c c' x hr
  exact shape_of_pad hp' hM

/-- The smallness test. -/
theorem z_shape_is (tl : HTailF2) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((HTailF2 × LinkCtx) × Fork) × Ctx) (h : tl.transcriptF L F c = .ok r) (hF : Sized F)
    (hd : c.ch.dry = false) (hM : Made #[tl.z1.call, tl.z2.call] tl.lidb tl.f9) :
    ∃ g, r.1.1.1.heard = some g ∧ g.shape = tl.f9 := by
  obtain ⟨_, F1, _, c1, g, _, _, hp, hg, _⟩ := site_Z_own tl L F c r h hF hd
  exact ⟨g, hg, shape_of_pad hp hM⟩

theorem g_size_is (y : Layer.Lay) (g : ℕ) (F G : Fork) (c c' : Ctx) (fo : Forest.Heard)
    (h : Layer.hearLook y g F c = .ok ((fo, G), c')) (hM : Made y.cl y.h.lidb y.fo) :
    forestSize fo.shape = forestSize y.fo := by
  rw [g_shape_is y g F G c c' fo h hM]

theorem a_size_is (P : Attention.Plan) (F G : Fork) (c c' : Ctx) (f : Attention.First)
    (h : Attention.hear P F c = .ok ((f, G), c'))
    (hM : Made (P.S.calls.map (·.call)) P.lid P.fs) :
    forestSize f.g.shape = forestSize P.fs := by
  rw [a_shape_is P F G c c' f h hM]

theorem h_size_is (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (plain : Array E) (F G : Fork) (c c' : Ctx) (x : Head.Heard)
    (hr : Head.hear h L hp cov plain F c = .ok ((x, G), c')) (hM : Made L.cl h.LIDB L.fs) :
    forestSize x.g1.shape = forestSize L.fs := by
  rw [h_shape_is h L hp cov plain F G c c' x hr hM]

theorem z_size_is (tl : HTailF2) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((HTailF2 × LinkCtx) × Fork) × Ctx) (h : tl.transcriptF L F c = .ok r) (hF : Sized F)
    (hd : c.ch.dry = false) (hM : Made #[tl.z1.call, tl.z2.call] tl.lidb tl.f9) :
    ∃ g, r.1.1.1.heard = some g ∧ forestSize g.shape = forestSize tl.f9 := by
  obtain ⟨g, hg, e⟩ := z_shape_is tl L F c r h hF hd hM
  exact ⟨g, hg, by rw [e]⟩

end Fo
