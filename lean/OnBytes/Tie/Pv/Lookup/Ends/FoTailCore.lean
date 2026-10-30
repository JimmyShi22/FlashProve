-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailCore.lean.
Each of eight routines, of the plan and of a run, returns the record of a sub-proof's smallness test
with the list of matrices, their number and tau that the record had when it was given.

HTailF2.equationsF, the number of indices that the test's equations take, reads the matrices and tau
alone. So it is one number at the record given to such a routine and at the record returned.

Main names:
  `Core a b`: b has a's NM, mats and tau. `Core.refl`, `Core.trans`.
  `Core.size`: so b.NM = b.mats.size if a.NM = a.mats.size. `Core.equationsF`: so equationsF is the
    same at both.
  `stepF_pos`, `equationsF_inj`: stepF is not 0; equationsF at two numbers of reads is one number
    only if the two are one.
  `piecesF_core`: Core between the record given to HTailF2.piecesF and the record returned.
  `shapeF_size`: where tl.shapeF returns tl': tl'.NM = tl'.mats.size, tl'.mats is the list given,
    tl'.tau is tl's.
  `addTreesF_core`, `borderMeans_core`, `ownerIs_core` (the plan's steps); `closeFuns_core`,
    `drawMatrixF_core`, `transcriptF_core`, `objectsF_core` (a run's steps): Core between the record
    given and the record returned. ρ and W in `objectsF_core` are the letters of
    Port.objectsF_total; the statement does not read them.
Needs: OnBytes/Tie/Pv/Tail/EndSpread.lean and what it imports.
Does not say: which records a run of a sub-proof's check passes from one of these routines to the
next.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.BatRows
import OnBytes.Tie.Pv.Lookup.Ends.FoDoorRows
import OnBytes.Tie.Pv.Tail.EndSpread

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Tie.Pv.Tail.Port
open Fo.BatRows (bindE_ok ite_ok)

/-- b has a's number of matrices, list of matrices and tau. -/
def Core (a b : HTailF2) : Prop := b.NM = a.NM ∧ b.mats = a.mats ∧ b.tau = a.tau

theorem Core.refl (a : HTailF2) : Core a a := ⟨rfl, rfl, rfl⟩

theorem Core.trans {a b c : HTailF2} (h1 : Core a b) (h2 : Core b c) : Core a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem Core.size {a b : HTailF2} (h : Core a b) (ha : a.NM = a.mats.size) :
    b.NM = b.mats.size := by rw [h.1, h.2.1, ha]

theorem Core.equationsF {a b : HTailF2} (h : Core a b) (n : ℕ) :
    b.equationsF n = a.equationsF n := BatRows.equationsF_congr h.2.1 h.2.2 n

theorem stepF_pos (tl : HTailF2) : 0 < tl.stepF := Nat.pos_of_ne_zero (by
  unfold HTailF2.stepF
  exact Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide)))

theorem equationsF_inj (tl : HTailF2) {n n' : ℕ} (h : tl.equationsF n = tl.equationsF n') :
    n = n' := by
  unfold HTailF2.equationsF at h
  exact Nat.eq_of_mul_eq_mul_right (stepF_pos tl) (Nat.add_left_cancel h)

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

/-! ### the plan's steps -/

theorem piecesF_core {tl tl' : HTailF2} (e : tl.piecesF = .ok tl') : Core tl tl' := by
  unfold HTailF2.piecesF at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact ⟨rfl, rfl, rfl⟩

theorem shapeF_size {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (e : tl.shapeF m txOf f hasU tau = .ok tl') :
    tl'.NM = tl'.mats.size ∧ tl'.mats = m ∧ tl'.tau = tl.tau := by
  unfold HTailF2.shapeF at e
  dsimp only at e
  alive
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  alive
  obtain ⟨h1, h2, h3⟩ := piecesF_core e
  exact ⟨by rw [h1, h2], h2, h3⟩

theorem addTreesF_core {tl tl' : HTailF2} {F F' : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    Core tl tl' := by
  obtain ⟨-, -, e⟩ := addTreesF_fits tl tl' F F' T T' nU aTX hb hbLine h
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

theorem borderMeans_core {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (e : tl.borderMeans iF ownerNo index = .ok tl') : Core tl tl' := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      exact ⟨rfl, rfl, rfl⟩

theorem ownerIs_core (tl : HTailF2) (no : Nat) : Core tl (tl.ownerIs no) := ⟨rfl, rfl, rfl⟩

/-! ### a run's steps -/

theorem closeFuns_core {tl tl' : HTailF2} {funs : Array HFun} (e : tl.closeFuns funs = some tl') :
    Core tl tl' := by
  unfold HTailF2.closeFuns at e
  split at e
  · cases e
  · cases e
    exact ⟨rfl, rfl, rfl⟩

theorem drawMatrixF_core {tl tl' : HTailF2} {F G : Fork} {c c' : Ctx}
    (h : tl.drawMatrixF F c = .ok ((tl', G), c')) : Core tl tl' := by
  unfold HTailF2.drawMatrixF at h
  rw [PscRun.bind_ok] at h
  obtain ⟨_, _, _, -, h⟩ := h
  rw [PscRun.bind_ok] at h
  obtain ⟨_, _, _, -, h⟩ := h
  rw [PscRun.pure_ok] at h
  obtain ⟨⟨rfl, -⟩, -⟩ := by simpa [Prod.ext_iff] using h
  exact ⟨rfl, rfl, rfl⟩

theorem transcriptF_core {tl tl' : HTailF2} {L L' : LinkCtx} {F G : Fork} {c c' : Ctx}
    (h : tl.transcriptF L F c = .ok (((tl', L'), G), c')) : Core tl tl' := by
  unfold HTailF2.transcriptF at h
  rw [lbind_ok] at h
  obtain ⟨_, _, _, _, -, h⟩ := h
  rw [lbind_ok] at h
  obtain ⟨_, _, _, _, -, h⟩ := h
  rw [lbind_ok] at h
  obtain ⟨_, _, _, _, -, h⟩ := h
  rw [lbind_ok] at h
  obtain ⟨_, _, _, _, -, h⟩ := h
  rw [lbind_ok] at h
  obtain ⟨tl1, _, _, _, h1, h⟩ := h
  have c1 := drawMatrixF_core (sub_ok _ _ _ _ _ _ _ _ h1)
  rw [lbind_ok] at h
  obtain ⟨_, _, _, _, -, h⟩ := h
  rw [lbind_ok] at h
  obtain ⟨_, _, _, _, -, h⟩ := h
  rw [lbind_ok] at h
  obtain ⟨_, _, _, _, -, h⟩ := h
  have e : tl' = _ := (congrArg (fun x : ((HTailF2 × LinkCtx) × Fork) × Ctx => x.1.1.1)
    (Except.ok.inj h)).symm
  rw [e]
  exact c1.trans ⟨rfl, rfl, rfl⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)
include ρ W

theorem objectsF_core {tl tl' : HTailF2} {funs : Array HFun} {F G : Fork} {c c' : Ctx}
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) : Core tl tl' := by
  obtain ⟨g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, tl1, F1, c1, -, -, hJ, hB, hWt, -, etl, -, -, -⟩ :=
    objectsF_total ρ W tl tl' funs F G c c' h
  obtain ⟨-, -, -, e1⟩ := weightsF_spec tlb tl1 Fc F1 cc c1 hWt
  have eJ := linJoin9_spec tl tla Fa Fb ca cb hJ
  have eB := linBits9_spec tla tlb Fb Fc cb cc hB
  have k1 : Core tl tla := by rw [eJ]; exact ⟨rfl, rfl, rfl⟩
  have k2 : Core tla tlb := by rw [eB]; exact ⟨rfl, rfl, rfl⟩
  have k3 : Core tlb tl1 := by rw [e1]; exact ⟨rfl, rfl, rfl⟩
  have k4 : Core tl1 tl' := by rw [etl]; exact ⟨rfl, rfl, rfl⟩
  exact ((k1.trans k2).trans k3).trans k4

end
end Fo
