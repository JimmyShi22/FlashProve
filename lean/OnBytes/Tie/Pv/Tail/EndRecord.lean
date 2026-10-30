-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndRecord.lean: the routines of the smallness test that return its state
(OnBytes/Model/Tail.lean) leave the arrays' numbers, the blocks and the three lengths of the tables'
vectors as they were.

Definitions, and theorems with their proofs.

Main names:
  `RecordKept a b`: b has a's numbers of the arrays (`ix`), blocks and lengths (`nUF`).
  `RecordKept.refl`, `RecordKept.trans`.
  `borderMeans_record`, `ownerIs_record`, `closeFuns_record`, `drawMatrixF_record`,
    `transcriptF_record`, `objectsF_record`: the routines between addTreesF and the test of the
    weights.
  `bindL_ok`, `subL_ok`, `pureL_ok`: a run of a routine that also calls the chain (`LinkM`,
    OnBytes/Model/Trees.lean): one after the other; a lifted routine; a value.
  `rawRows_kept`: `rawRows_runs` (OnBytes/Tie/Pv/Tail/EndRuns.lean) with `RecordKept` from the
    record that addTreesF returns to the record that goes into objectsF.

Limits: nothing on the other fields. Nothing is said where a routine fails.


-/
import OnBytes.Tie.Pv.Tail.EndRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port Finset

/-- b has a's numbers of the arrays, blocks and lengths of the tables' vectors. -/
structure RecordKept (a b : HTailF2) : Prop where
  ix : b.ix = a.ix
  blocks : b.blocks = a.blocks
  nUF : b.nUF = a.nUF

/-- Every record keeps its own. -/
theorem RecordKept.refl (a : HTailF2) : RecordKept a a := ⟨rfl, rfl, rfl⟩

/-- `RecordKept` goes through a record between. -/
theorem RecordKept.trans {a b c : HTailF2} (h : RecordKept a b) (h' : RecordKept b c) :
    RecordKept a c := ⟨h'.ix.trans h.ix, h'.blocks.trans h.blocks, h'.nUF.trans h.nUF⟩

/-- Recording which array of an earlier sub-proof is meant. -/
theorem borderMeans_record {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (h : tl.borderMeans iF ownerNo index = .ok tl') : RecordKept tl tl' := by
  unfold HTailF2.borderMeans at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      exact ⟨rfl, rfl, rfl⟩

/-- Recording the sub-proof's own number. -/
theorem ownerIs_record (tl : HTailF2) (no : Nat) : RecordKept tl (tl.ownerIs no) := ⟨rfl, rfl, rfl⟩

/-- Closing the list of tables. -/
theorem closeFuns_record {tl tl' : HTailF2} {funs : Array HFun}
    (h : tl.closeFuns funs = some tl') : RecordKept tl tl' := by
  unfold HTailF2.closeFuns at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl⟩

/-- Drawing the matrix. -/
theorem drawMatrixF_record {tl tl' : HTailF2} {F G : Fork} {c c' : Ctx}
    (h : tl.drawMatrixF F c = .ok ((tl', G), c')) : RecordKept tl tl' := by
  unfold HTailF2.drawMatrixF at h
  simp only [bind_ok, pure_ok] at h
  obtain ⟨_, _, _, _, _, _, _, _, rfl, _, _⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-! ## Routines that also call the chain -/

/-- A run of «x, then f». -/
theorem bindL_ok {α β : Type} (x : LinkM α) (f : α → LinkM β) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((β × LinkCtx) × Fork) × Ctx) :
    (x >>= f) L F c = .ok r ↔
      ∃ a L1 F1 c1, x L F c = .ok (((a, L1), F1), c1) ∧ f a L1 F1 c1 = .ok r := by
  show (StateT.bind x f) L F c = .ok r ↔ _
  simp only [StateT.bind]
  rw [bind_ok]
  constructor
  · rintro ⟨⟨a, L1⟩, F1, c1, h1, h2⟩
    exact ⟨a, L1, F1, c1, h1, h2⟩
  · rintro ⟨a, L1, F1, c1, h1, h2⟩
    exact ⟨(a, L1), F1, c1, h1, h2⟩

/-- A lifted routine of the sub-proof leaves the link's own state. -/
theorem subL_ok {α : Type} (x : SubM α) (L L' : LinkCtx) (F G : Fork) (c c' : Ctx) (a : α) :
    LinkM.sub x L F c = .ok (((a, L'), G), c') ↔ x F c = .ok ((a, G), c') ∧ L' = L := by
  unfold LinkM.sub
  rw [bind_ok]
  constructor
  · rintro ⟨a1, F1, c1, h1, h2⟩
    obtain ⟨e1, rfl, rfl⟩ := (pure_ok _ _ _ _ _ _).1 h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
    exact ⟨h1, rfl⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨a, G, c', h1, (pure_ok _ _ _ _ _ _).2 ⟨rfl, rfl, rfl⟩⟩

/-- A routine that only returns a value. -/
theorem pureL_ok {α : Type} (a x : α) (L L' : LinkCtx) (F G : Fork) (c c' : Ctx) :
    (pure a : LinkM α) L F c = .ok (((x, L'), G), c') ↔ x = a ∧ L' = L ∧ G = F ∧ c' = c := by
  show (pure (a, L) : SubM (α × LinkCtx)) F c = _ ↔ _
  rw [pure_ok]
  constructor
  · rintro ⟨e, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩

/-- The messages of the smallness test. -/
theorem transcriptF_record {tl tl' : HTailF2} {L L' : LinkCtx} {F G : Fork} {c c' : Ctx}
    (h : tl.transcriptF L F c = .ok (((tl', L'), G), c')) : RecordKept tl tl' := by
  unfold HTailF2.transcriptF at h
  simp only [bindL_ok] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, tl1, L1, F1, c1, hd, h⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  obtain ⟨rfl, _, _, _⟩ := (pureL_ok _ _ _ _ _ _ _ _).1 h
  exact (drawMatrixF_record ((subL_ok _ _ _ _ _ _ _ _).1 hd).1).trans ⟨rfl, rfl, rfl⟩

/-- Adding the claims of the smallness test. -/
theorem objectsF_record {K : Type} [CommRing K] (ρ : Reading K) (W : World K) {tl tl' : HTailF2}
    {funs : Array HFun} {F G : Fork} {c c' : Ctx}
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) : RecordKept tl tl' := by
  obtain ⟨_, Fa0, ca0, tla0, Fb0, cb0, tlb0, Fc0, cc0, tl1, F10, c10, _, _, hJ0, hB0, hWt0, _,
    etl, _, _, _⟩ := objectsF_total ρ W tl tl' funs F G c c' h
  have ea := linJoin9_spec tl tla0 Fa0 Fb0 ca0 cb0 hJ0
  have eb := linBits9_spec tla0 tlb0 Fb0 Fc0 cb0 cc0 hB0
  obtain ⟨_, _, _, e1⟩ := weightsF_spec tlb0 tl1 Fc0 F10 cc0 c10 hWt0
  exact ⟨carry4 (fun t => t.ix) ea rfl eb rfl e1 rfl etl rfl,
    carry4 (fun t => t.blocks) ea rfl eb rfl e1 rfl etl rfl,
    carry4 (fun t => t.nUF) ea rfl eb rfl e1 rfl etl rfl⟩

/-- `RawRows` as the theorems on objectsF ask it, with the record's carry up to objectsF. -/
theorem rawRows_kept {K : Type} [CommRing K] (ρ : Reading K) (tl0 tla tl tl' : HTailF2)
    (funs : Array HFun) (F0 Fa F G F1 F2 F2' : Fork) (T0 Ta : Tail2) (nU aTX : Array Nat)
    (hb hbLine : Nat) (c c' c1 c1' c2 c2' : Ctx) (W : World K) (A : Nat → Nat → Nat → K)
    (hadd : tl0.addTreesF F0 T0 nU aTX hb hbLine = .ok (tla, Fa, Ta)) (hrec : RecordKept tla tl)
    (hobj : tl.objectsF funs F c = .ok ((tl', G), c'))
    (hk1 : ShapesKept Fa G) (hk2 : FrameKept G F1)
    (hco : tl'.coefficientsF F1 c1 = .ok (((), F2), c1')) (hd : c2.ch.dry = false)
    (hst : tl'.tileSelfTestF F2 c2 = .ok (((), F2'), c2'))
    (hW : ReadsRaw ρ tl' funs F2 W A) : RawRows W tl G funs (ρ.val G.theta) A := by
  have r := hrec.trans (objectsF_record ρ W hobj)
  exact rawRows_runs ρ tl0 tla tl tl' funs F0 Fa F G F1 F2 F2' T0 Ta nU aTX hb hbLine
    c c' c1 c1' c2 c2' W A hadd r.ix r.blocks r.nUF hobj hk1 hk2 hco hd hst hW

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.transcriptF_record
#print axioms OnBytes.Tie.Pv.Tail.objectsF_record
#print axioms OnBytes.Tie.Pv.Tail.rawRows_kept
