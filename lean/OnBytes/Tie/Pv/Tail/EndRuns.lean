-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndRuns.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), from four runs of the verifier's own routines,
with no premise on the reads.

Theorems with their proofs. OnBytes/Tie/Pv/Tail/EndWhole.lean asks of each read that its vector is
there and that its places lie below the vector's length. objectsF tests both itself
(OnBytes/Tie/Pv/Tail/EndReads.lean), so here they are no premises.

Main names:
  `addTreesF_record`: of the record that addTreesF returns: the three lengths are the caller's, and
    the arrays' numbers and the blocks are those of the record that went in.
  `rawRows_runs`: `RawRows` as the theorems on objectsF ask it.

Limits: premises that stay, all on public numbers: the steps between the runs keep the arrays'
shapes and, from objectsF on, the batching element (`ShapesKept`, `FrameKept`,
OnBytes/Tie/Pv/Tail/EndKeep.lean); the record that objectsF returns has the arrays' numbers, the
blocks and the three lengths of the record that addTreesF returned; the world reads the four kinds
of virtual row as sums of the arrays' entries (`ReadsRaw`, OnBytes/Tie/Pv/Tail/EndRaw.lean).


-/
import OnBytes.Tie.Pv.Tail.EndReads
import OnBytes.Tie.Pv.Tail.EndWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port Finset

/-- Of the record that addTreesF returns: the lengths, the arrays' numbers, the blocks. -/
theorem addTreesF_record (tl tl' : HTailF2) (F F' : Fork) (T T' : Tail2) (nU aTX : Array Nat)
    (hb hbLine : Nat) (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    tl'.nUF = #[nU.getD 0 0, nU.getD 1 0, nU.getD 2 0] ∧ tl'.ix = tl.ix ∧
      tl'.blocks = tl.blocks := by
  unfold HTailF2.addTreesF at h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨r1, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨r2, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨r3, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨⟨gz, Fz, Tz⟩, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨⟨gb, Fb, Tb⟩, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨r4, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  have e := Except.ok.inj h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, _, _⟩ := e
  exact ⟨rfl, rfl, rfl⟩

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- `RawRows` as the theorems on objectsF ask it, from the verifier's own runs. -/
theorem rawRows_runs (tl0 tla tl tl' : HTailF2) (funs : Array HFun)
    (F0 Fa F G F1 F2 F2' : Fork) (T0 Ta : Tail2) (nU aTX : Array Nat) (hb hbLine : Nat)
    (c c' c1 c1' c2 c2' : Ctx) (W : World K) (A : Nat → Nat → Nat → K)
    (hadd : tl0.addTreesF F0 T0 nU aTX hb hbLine = .ok (tla, Fa, Ta))
    (hix : tl'.ix = tla.ix) (hbl : tl'.blocks = tla.blocks) (hnU : tl'.nUF = tla.nUF)
    (hobj : tl.objectsF funs F c = .ok ((tl', G), c'))
    (hk1 : ShapesKept Fa G) (hk2 : FrameKept G F1)
    (hco : tl'.coefficientsF F1 c1 = .ok (((), F2), c1')) (hd : c2.ch.dry = false)
    (hst : tl'.tileSelfTestF F2 c2 = .ok (((), F2'), c2'))
    (hW : ReadsRaw ρ tl' funs F2 W A) : RawRows W tl G funs (ρ.val G.theta) A := by
  obtain ⟨r1, r2, r3⟩ := addTreesF_record tl0 tla F0 Fa T0 Ta nU aTX hb hbLine hadd
  refine rawRows_whole ρ tl0 tla tl tl' funs F0 Fa F G F1 F2 F2' T0 Ta nU aTX hb hbLine
    c c' c1 c1' c2 c2' W A hadd (hix.trans r2) ?_ hobj hk1 hk2 hco hd hst hW ?_
  · unfold HTailF2.zzBlocks
    rw [hbl, r3]
  · intro x hx
    obtain ⟨hs, hp⟩ := objectsF_reads tl tl' funs F G c c' hobj x hx
    rw [hix, r2] at hs
    refine ⟨hs, fun d hd' => ?_⟩
    have := hp d hd'
    rw [hnU, r1] at this
    rcases reads_tree tl' funs x hx with e | e
    · rw [e] at this ⊢
      simpa using this
    · rw [e] at this ⊢
      simpa using this

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.rawRows_runs
