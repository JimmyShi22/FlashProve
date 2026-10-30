-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndDraw.lean: which fields of the smallness test's state three of its routines
set: the closing of the list of tables, the draw of the matrix, and the routine that reads the
test's messages (OnBytes/Model/Tail.lean: closeFuns, drawMatrixF, transcriptF).

Definitions, statements and proofs. OnBytes/Tie/Pv/Tail/EndSame.lean has the like for two later
routines.
Main names:
  `bindL_ok`, `subL_ok`, `pureL_ok`: what it says of a routine of a link (LinkM) that it has
    returned.
  `closeFuns_spec`: the list is closed and is the list given.
  `cfFirstOf`, `drawMatrixF_spec`: behind the draw the first columns are the running sums of the
    matrices' columns; of the other fields the drawn entries alone are set.
  `transcriptF_spec`: which fields transcriptF sets; it returns only if there is one shape for each
    matrix and the list of tables is closed.
  `fits_transcriptF`: `Fits` goes through transcriptF.
Limits: nothing on what the drawn entries are, or on what the routines do to the chain.
-/
import OnBytes.Tie.Pv.Tail.EndSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

/-! ## Runs in LinkM -/

theorem bindL_ok {α β : Type} (x : LinkM α) (f : α → LinkM β) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((β × LinkCtx) × Fork) × Ctx) :
    (x >>= f) L F c = .ok r ↔
      ∃ a L1 F1 c1, x L F c = .ok (((a, L1), F1), c1) ∧ f a L1 F1 c1 = .ok r := by
  show (StateT.bind x f) L F c = .ok r ↔ _
  simp only [StateT.bind]
  rw [bind_ok]
  constructor
  · rintro ⟨⟨a, L1⟩, F1, c1, h1, h2⟩; exact ⟨a, L1, F1, c1, h1, h2⟩
  · rintro ⟨a, L1, F1, c1, h1, h2⟩; exact ⟨(a, L1), F1, c1, h1, h2⟩

theorem subL_ok {α : Type} (x : SubM α) (L L' : LinkCtx) (F F' : Fork) (c c' : Ctx) (a : α) :
    LinkM.sub x L F c = .ok (((a, L'), F'), c') ↔ x F c = .ok ((a, F'), c') ∧ L' = L := by
  unfold LinkM.sub
  rw [bind_ok]
  constructor
  · rintro ⟨a1, F1, c1, h1, h2⟩
    obtain ⟨e1, rfl, rfl⟩ := (pure_ok _ _ _ _ _ _).1 h2
    cases e1
    exact ⟨h1, rfl⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨a, F', c', h1, (pure_ok _ _ _ _ _ _).2 ⟨rfl, rfl, rfl⟩⟩

theorem pureL_ok {α : Type} (a x : α) (L L' : LinkCtx) (F F' : Fork) (c c' : Ctx) :
    (pure a : LinkM α) L F c = .ok (((x, L'), F'), c') ↔ x = a ∧ L' = L ∧ F' = F ∧ c' = c := by
  show (Except.ok (((a, L), F), c) : Except Failure (((α × LinkCtx) × Fork) × Ctx)) = _ ↔ _
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

/-! ## Three routines, one by one -/

theorem closeFuns_spec (tl tl' : HTailF2) (funs : Array HFun) (h : tl.closeFuns funs = some tl') :
    tl' = { tl with funClosed := true, funs := funs } := by
  unfold HTailF2.closeFuns at h
  split at h
  · cases h
  · exact (Option.some.inj h).symm

/-- drawMatrixF's cfFirst: the running sums of the matrices' columns, with a last entry. -/
def cfFirstOf (tl : HTailF2) : Array Nat :=
  tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0]

theorem drawMatrixF_spec (tl tl' : HTailF2) (F F' : Fork) (c c' : Ctx)
    (h : tl.drawMatrixF F c = .ok ((tl', F'), c')) :
    tl' = { tl with cfF := tl'.cfF, cfFirst := cfFirstOf tl } := by
  unfold HTailF2.drawMatrixF at h
  simp only [bind_ok, pure_ok] at h
  obtain ⟨_, _, _, _, cf, _, _, _, rfl, _, _⟩ := h
  rfl

theorem transcriptF_spec (tl tl' : HTailF2) (L L' : LinkCtx) (F F' : Fork) (c c' : Ctx)
    (h : tl.transcriptF L F c = .ok (((tl', L'), F'), c')) :
    tl' = { tl with cfF := tl'.cfF, cfFirst := cfFirstOf tl, foldDrawn := tl.foldDrawn + 1,
                    slotA := tl'.slotA, slotB := tl'.slotB, heard := tl'.heard } ∧
      tl.shp.size = tl.NM ∧ tl.funClosed = true := by
  unfold HTailF2.transcriptF at h
  simp only [bindL_ok, pureL_ok, subL_ok, LinkM.mustAs, lift_ok, mustAs_ok] at h
  obtain ⟨_, _, _, _, ⟨⟨⟨hc, _⟩, _⟩, _⟩, _, _, _, _, ⟨⟨⟨hs, _⟩, _⟩, _⟩, _, _, _, _, _, _, _, _, _,
    _, tl2, _, _, _, ⟨hd, _⟩, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _, _⟩ := h
  have e := drawMatrixF_spec _ _ _ _ _ _ hd
  refine ⟨?_, by simpa using hs, hc⟩
  rw [e]

/-- `Fits` goes through transcriptF. -/
theorem fits_transcriptF (tl tl' : HTailF2) (L L' : LinkCtx) (F F' : Fork) (c c' : Ctx)
    (h : tl.transcriptF L F c = .ok (((tl', L'), F'), c')) (hf : Fits tl) : Fits tl' := by
  obtain ⟨e, _, _⟩ := transcriptF_spec tl tl' L L' F F' c c' h
  exact hf.of_same ((congrArg (fun t => t.NM) e).trans rfl)
    ((congrArg (fun t => t.shp) e).trans rfl) ((congrArg (fun t => t.mats) e).trans rfl)

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.drawMatrixF_spec
#print axioms OnBytes.Tie.Pv.Tail.Port.transcriptF_spec
#print axioms OnBytes.Tie.Pv.Tail.Port.fits_transcriptF
