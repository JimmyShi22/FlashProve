-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsPlan.lean.
The tests on public numbers of the lookup on the digits, at the plan alone.

`ZTests tl2 tl3 Fs` (FoLookDigitsRun) speaks of two records and a state of a run. This file states
that what these tests read is what the plan's record and the state at the run's start hold, so that
the tests at the plan give the tests at the run.

Main names:
  `SameP a b`: b has a's tau, lidb, mz, f9, and what `SameRec` (FoAddTrees) names: the arrays'
    numbers, the blocks, the two calls, the matrices' arrays and their number.
  `withP a b`: b with these ten fields of a. `SameP.eq`: under `SameP a b` it is b.
  `sameP_closeFuns`, `sameP_transcriptF`, `sameP_objectsF` (with `sameP_linJoin9`, `sameP_linBits9`,
    `sameP_powersF`, `sameP_foldSums`, `sameP_weightsF`): what each routine returns has `SameP` with
    the record at which it ran; for `transcriptF` under `Sized F` and a context on a view.
  `zTests_with`: the ten tests read the ten fields alone: by unfolding.
  `zTests_frame`: of the state they read the arrays' number, numbers of rows and numbers of virtual
    rows alone (`Frame`, FoCoef).
  `zTests_run`: `ZTests a a Fp` gives `ZTests b c Fs` under `SameP a b`, `SameP a c`, `Frame Fp Fs`.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookDigitsRun
import OnBytes.Tie.Pv.Lookup.Ends.FoAddTrees
import OnBytes.Tie.Pv.Lookup.Ends.FoFramePass

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.DgP

/-- b has the ten fields of a that the tests read. -/
structure SameP (a b : HTailF2) : Prop where
  same : SameRec a b
  tau : b.tau = a.tau
  lidb : b.lidb = a.lidb
  mz : b.mz = a.mz
  f9 : b.f9 = a.f9

theorem SameP.refl (a : HTailF2) : SameP a a := ⟨SameRec.refl a, rfl, rfl, rfl, rfl⟩

theorem SameP.trans {a b c : HTailF2} (h : SameP a b) (k : SameP b c) : SameP a c :=
  ⟨h.same.trans k.same, k.tau.trans h.tau, k.lidb.trans h.lidb, k.mz.trans h.mz, k.f9.trans h.f9⟩

/-- b with the ten fields of a. -/
def withP (a b : HTailF2) : HTailF2 :=
  { b with tau := a.tau, lidb := a.lidb, mz := a.mz, NM := a.NM, gtTree := a.gtTree, ix := a.ix,
           blocks := a.blocks, z1 := a.z1, z2 := a.z2, f9 := a.f9 }

theorem SameP.eq {a b : HTailF2} (h : SameP a b) : b = withP a b := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9, h10⟩ := h
  unfold withP
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, ← h8, ← h9, ← h10]

/-! ### the routines -/

theorem sameP_closeFuns {tl tl' : HTailF2} {funs : Array HFun} (e : tl.closeFuns funs = some tl') :
    SameP tl tl' := by
  unfold HTailF2.closeFuns at e
  split at e
  · cases e
  · cases e
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem sameP_transcriptF {tl tl2 : HTailF2} {L Lt : LinkCtx} {F Gt : Fork} {c cr : Ctx}
    (hT : tl.transcriptF L F c = .ok (((tl2, Lt), Gt), cr)) (hF : Sized F)
    (hd : c.ch.dry = false) : SameP tl tl2 := by
  obtain ⟨tl', F5, F1, c5, c1, L6, g, e1, _, _, e4, _⟩ := site_Z tl L F c _ hT hF hd
  obtain ⟨_, eT⟩ := drawMatrixF_ok tl tl' F F5 c c5 e1
  have eR : tl2 = { tl' with
      foldDrawn := tl'.foldDrawn + 1, slotA := F.next, slotB := Gt.next, heard := some g } :=
    congrArg Prod.fst e4
  have k1 : SameP tl tl' := by
    rw [eT]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  have k2 : SameP tl' tl2 := by
    rw [eR]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  exact k1.trans k2

theorem sameP_linJoin9 (tl : HTailF2) : Yields tl.linJoin9 (SameP tl) := by
  unfold HTailF2.linJoin9
  repeat' first
    | exact Yields.pure ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
    | (refine Yields.bind fun _ => ?_)

theorem sameP_linBits9 (tl : HTailF2) : Yields tl.linBits9 (SameP tl) := by
  unfold HTailF2.linBits9
  repeat' first
    | exact Yields.pure ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
    | (refine Yields.bind fun _ => ?_)

theorem sameP_powersF {tl t : HTailF2} {F : Fork} (h : tl.powersF F = some t) : SameP tl t := by
  unfold HTailF2.powersF at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rw [← Option.some.inj h]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem sameP_foldSums {tl t : HTailF2} {mu : ℕ} (h : tl.foldSums mu = some t) : SameP tl t := by
  unfold HTailF2.foldSums at h
  dsimp only at h
  split_ifs at h <;>
    (rw [← Option.some.inj h]
     exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩)

theorem sameP_folds : ∀ (l : List ℕ) (a b : HTailF2),
    l.foldlM (fun (x : HTailF2) mu => x.foldSums mu) a = some b → SameP a b
  | [], a, b, h => by
    obtain rfl : a = b := Option.some.inj h
    exact SameP.refl a
  | mu :: l, a, b, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t, ht, h2⟩ := Option.bind_eq_some_iff.mp h
    exact (sameP_foldSums ht).trans (sameP_folds l t b h2)

theorem sameP_weightsF (tl : HTailF2) : Yields tl.weightsF (SameP tl) := by
  intro F c a G c' hr
  unfold HTailF2.weightsF at hr
  obtain ⟨t, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨t', e1, r1⟩ := (PscRun.ask_ok _ _ _ _).1 h1
  obtain rfl : t = t' := congrArg (fun x : (HTailF2 × Fork) × Ctx => x.1.1) r1
  obtain ⟨a', e2, r2⟩ := (get_ok _ _ _ _).1 h2
  obtain rfl : a = a' := congrArg (fun x : (HTailF2 × Fork) × Ctx => x.1.1) r2
  have k := sameP_folds _ _ _ e2
  exact (sameP_powersF e1).trans ⟨⟨k.same.ix, k.same.blocks, k.same.z1, k.same.z2, k.same.gtTree,
    k.same.NM⟩, k.tau, k.lidb, k.mz, k.f9⟩

theorem sameP_objectsF (tl : HTailF2) (funs : Array HFun) :
    Yields (tl.objectsF funs) (SameP tl) := by
  unfold HTailF2.objectsF
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind2 (sameP_linJoin9 tl) fun t1 h1 => ?_
  refine Yields.bind2 (sameP_linBits9 t1) fun t2 h2 => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  refine Yields.bind2 (sameP_weightsF t2) fun t3 h3 => ?_
  have e := (h1.trans h2).trans h3
  repeat' first
    | exact Yields.pure ⟨⟨e.same.ix, e.same.blocks, e.same.z1, e.same.z2, e.same.gtTree,
        e.same.NM⟩, e.tau, e.lidb, e.mz, e.f9⟩
    | (refine Yields.bind fun _ => ?_)

/-! ### the tests -/

/-- The ten tests read the ten fields alone. -/
theorem zTests_with {a : HTailF2} {Fs : Fork} (T : ZTests a a Fs) (b c : HTailF2) :
    ZTests (withP a b) (withP a c) Fs :=
  ⟨T.t1, T.t2, T.t3, T.t4, T.t5, T.t6, T.t7, T.t8, T.t9, T.t10⟩

theorem hasRow_frame {F G : Fork} (h : Frame F G) (t e : ℕ) : HasRow G t e ↔ HasRow F t e := by
  unfold HasRow
  rw [h.1, (h.2 t).2]

theorem coefTest_frame {F G : Fork} (h : Frame F G) (tl : HTailF2) :
    coefTest tl G = coefTest tl F := by
  unfold coefTest
  simp only [hasRow_frame h, (h.2 _).1]

/-- Of the state they read the arrays' numbers alone. -/
theorem zTests_frame {a b : HTailF2} {Fp Fs : Fork} (T : ZTests a b Fp) (h : Frame Fp Fs) :
    ZTests a b Fs :=
  ⟨T.t1, T.t2, T.t3, T.t4, T.t5, T.t6, T.t7, T.t8, by rw [coefTest_frame h]; exact T.t9,
    fun x hx => by rw [(h.2 _).1]; exact T.t10 x hx⟩

/-- **The tests at the plan give the tests at the run.** -/
theorem zTests_run {a b c : HTailF2} {Fp Fs : Fork} (T : ZTests a a Fp) (hb : SameP a b)
    (hc : SameP a c) (h : Frame Fp Fs) : ZTests b c Fs := by
  rw [hb.eq, hc.eq]
  exact zTests_with (zTests_frame T h) b c

end Fo
