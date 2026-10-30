-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFramePass.lean.
The arrays of a sub-proof's state keep their number, their numbers of rows and their numbers of
virtual rows through every step of a check.

`Frame F G` (FoCoef) says that of two states. This file states that each step on the state which
the routines use keeps it, so that it passes wherever `Passes` (FoPass) holds.

Main names:
  `frame_trees`: `Frame` from the equality of `treesFrame` (OnBytes/Model/HideLaws.lean).
  `frame_modify`: one array is turned by a function that keeps its two numbers.
  `frame_fillL`, `frame_slots`, `frame_fill`: `Fork.fillL`, `Fork.slots`, `t2FillL`.
  `primFrame F0`: to have `Frame` from F0, with the slots' arrays at their sizes and one coefficient
    for each slot, is kept by every step (`Prim`, FoInv).
  `Passes.frame`: so `Passes F G` gives `Frame F G`, from a state F with these sizes.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPass
import OnBytes.Tie.Pv.Lookup.Ends.FoInvInst
import OnBytes.Tie.Pv.Lookup.Ends.FoCoef
import OnBytes.Model.TreesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem getD_app {β : Type} (a : Array HTree) (t : ℕ) (φ : HTree → β) :
    φ (a.getD t {}) = ((a[t]?).map φ).getD (φ {}) := by
  rw [Array.getD_eq_getD_getElem?]
  cases a[t]? <;> rfl

/-- An array's number of rows and number of virtual rows. -/
def twoOf (X : HTree) : ℕ × ℕ := (X.R, X.rows.size)

/-- `Frame` reads the arrays' two numbers alone. -/
theorem frame_of {F G : Fork} (h1 : G.trees.size = F.trees.size)
    (h2 : ∀ t : ℕ, (G.trees[t]?).map twoOf = (F.trees[t]?).map twoOf) : Frame F G := by
  refine ⟨h1, fun t => ?_⟩
  have e : twoOf (G.trees.getD t {}) = twoOf (F.trees.getD t {}) := by
    rw [getD_app G.trees t twoOf, getD_app F.trees t twoOf, h2 t]
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

theorem frame_same {F G : Fork} (h : G.trees = F.trees) : Frame F G :=
  frame_of (by rw [h]) fun t => by rw [h]

/-- From the equality of what the arrays hold but for the weights. -/
theorem frame_trees {F G : Fork} (h : treesFrame G.trees = treesFrame F.trees) : Frame F G := by
  refine frame_of ?_ fun t => ?_
  · have e := congrArg Array.size h
    simpa [treesFrame] using e
  · have e := congrArg (fun a => (a[t]?).map fun p => (p.1.R, p.2.size)) h
    simp only [treesFrame, Array.getElem?_map, Option.map_map] at e
    have k : ((fun p : HTree × Array (HRow × ℕ) => (p.1.R, p.2.size)) ∘ HTree.frame) = twoOf := by
      funext X
      simp [HTree.frame, twoOf]
    rw [k] at e
    exact e

/-- One array is turned by a function that keeps its two numbers. -/
theorem frame_modify (F : Fork) (t : ℕ) (f : HTree → HTree)
    (hf : ∀ X, (f X).R = X.R ∧ (f X).rows.size = X.rows.size) :
    Frame F { F with trees := F.trees.modify t f } := by
  refine frame_of (by simp) fun t' => ?_
  show ((F.trees.modify t f)[t']?).map _ = _
  rw [Array.getElem?_modify]
  split
  · cases F.trees[t']? with
    | none => rfl
    | some X => simp [twoOf, (hf X).1, (hf X).2]
  · rfl

theorem frame_map (F : Fork) (f : HTree → HTree)
    (hf : ∀ X, (f X).R = X.R ∧ (f X).rows.size = X.rows.size) :
    Frame F { F with trees := F.trees.map f } := by
  refine frame_of (by simp) fun t' => ?_
  show ((F.trees.map f)[t']?).map _ = _
  rw [Array.getElem?_map]
  cases F.trees[t']? with
  | none => rfl
  | some X => simp [twoOf, (hf X).1, (hf X).2]

theorem frame_fillL (F : Fork) : Frame F F.fillL :=
  frame_map F _ fun X => ⟨rfl, by simp⟩

theorem frame_slots (F : Fork) (n : ℕ) : Frame F (F.slots n) := frame_same rfl

/-- What `t2FillL` does to one array. -/
def fillX (X : HTree) : HTree :=
  { X with rows := X.rows.map fun r =>
      if r.L.size != X.K then { r with L := Array.replicate X.K zeroE } else r }

theorem frame_fills (F : Fork) : ∀ (l : List ℕ) (G : Fork), Frame F G →
    Frame F { G with trees := l.foldl (fun trees ti => trees.modify ti fillX) G.trees }
  | [], _, hG => hG
  | a :: l, G, hG =>
    frame_fills F l { G with trees := G.trees.modify a fillX }
      (hG.trans (frame_modify G a fillX fun X => ⟨rfl, by simp [fillX]⟩))

theorem frame_fill (F : Fork) (T : Tail2) : Frame F (t2FillL F T) :=
  frame_fills F (List.range T.nt.size) F (Frame.refl F)

instance primFrame (F0 : Fork) :
    Prim (fun X => Frame F0 X ∧ (Sized X ∧ X.LS.size = X.ns)) where
  took := fun F n hI => ⟨hI.1.trans (frame_same rfl), primLS.took F n hI.2⟩
  hideRun := fun F G j v f h hI =>
    ⟨hI.1.trans (frame_same (by
      obtain ⟨hs, _⟩ := hideRun_ok _ _ _ _ _ hI.2.1 h
      rw [hs])), primLS.hideRun F G j v f h hI.2⟩
  push := fun F G w a h hI =>
    ⟨hI.1.trans (frame_trees
      (Fork.push_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G w a hI.2.2 h).2.2.2),
      primLS.push F G w a h hI.2⟩
  pushRuns := fun F G k runs h hI =>
    ⟨hI.1.trans (frame_trees
      (Fork.pushRuns_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G k runs h).2.2),
      primLS.pushRuns F G k runs h hI.2⟩
  rootTaken := fun F t w hI =>
    ⟨hI.1.trans (frame_modify F t _ fun X => ⟨rfl, rfl⟩), primLS.rootTaken F t w hI.2⟩
  fill := fun F T hI => ⟨hI.1.trans (frame_fill F T), primLS.fill F T hI.2⟩
  onRow := fun F t r f hI => ⟨hI.1.trans (frame_onRow F t r f), primLS.onRow F t r f hI.2⟩
  book := fun F G h hI => ⟨hI.1.trans (frame_same h.1), primLS.book F G h hI.2⟩

/-- **The arrays' numbers pass wherever the steps' properties pass.** -/
theorem Passes.frame {F G : Fork} (h : Passes F G) (hS : Sized F) (hl : F.LS.size = F.ns) :
    Frame F G :=
  (h (fun X => Frame F X ∧ (Sized X ∧ X.LS.size = X.ns)) ⟨Frame.refl F, hS, hl⟩).1

end Fo
