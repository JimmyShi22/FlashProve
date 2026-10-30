-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndWhole.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), from four runs of the verifier's own routines and
what the steps between them keep.

Theorems with their proofs. The four runs, in the order of a sub-proof's check: the arrays are added
(addTreesF); the smallness test's claims are added (objectsF); the row weights are set
(coefficientsF); the weights are tested (tileSelfTestF, on a view). The steps between them differ by
the kind of sub-proof; of them it is asked only that they keep the arrays' shapes and, from objectsF
on, the batching element (`ShapesKept`, `FrameKept`, OnBytes/Tie/Pv/Tail/EndKeep.lean, which has a
law for each basic step).

Main names:
  `reads_tree`: a read's table lies on the first or on the third vector.
  `colsU_shape`: the number of columns of an array, read off its shape.
  `rawRows_whole`: `RawRows` as the theorems on objectsF ask it.

Limits: premises that stay, all on public numbers: the steps between the runs keep what is named
above; the record at objectsF has the numbers of the arrays and the blocks of the record at
addTreesF; each read's vector is there, and each place that a read names lies below the length that
addTreesF was given for that vector; the world reads the four kinds of virtual row as sums of the
arrays' entries (`ReadsRaw`, OnBytes/Tie/Pv/Tail/EndRaw.lean).


-/
import OnBytes.Tie.Pv.Tail.EndAdd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port Finset

/-- A read's table lies on the first or on the third vector. -/
theorem reads_tree (tl : HTailF2) (funs : Array HFun) (x : HFun × Nat)
    (h : x ∈ readsList tl funs) : x.1.tree = 0 ∨ x.1.tree = 2 := by
  unfold readsList at h
  obtain ⟨mu, -, h⟩ := List.mem_flatMap.1 h
  obtain ⟨un, hun, h⟩ := List.mem_flatMap.1 h
  obtain ⟨Fn, -, h⟩ := List.mem_flatMap.1 h
  unfold segsOf at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨sg, -, rfl⟩ := List.mem_map.1 h
    show Fn.tree = 0 ∨ Fn.tree = 2
    rw [hc.2]
    simpa using hun
  · simp at h

/-- The number of columns of an array, read off its shape. -/
theorem colsU_shape (F : Fork) (t : Nat) : colsU F t = (shapeAt F t).2.2.1 := by
  unfold colsU shapeAt
  by_cases ht : t < F.trees.size
  · simp [Array.getD, ht]
  · simp [Array.getD, ht]

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- `RawRows` as the theorems on objectsF ask it, from the verifier's own runs. -/
theorem rawRows_whole (tl0 tla tl tl' : HTailF2) (funs : Array HFun)
    (F0 Fa F G F1 F2 F2' : Fork) (T0 Ta : Tail2) (nU aTX : Array Nat) (hb hbLine : Nat)
    (c c' c1 c1' c2 c2' : Ctx) (W : World K) (A : Nat → Nat → Nat → K)
    (hadd : tl0.addTreesF F0 T0 nU aTX hb hbLine = .ok (tla, Fa, Ta))
    (hix : tl'.ix = tl0.ix) (hbl : tl'.zzBlocks = tl0.zzBlocks)
    (hobj : tl.objectsF funs F c = .ok ((tl', G), c'))
    (hk1 : ShapesKept Fa G) (hk2 : FrameKept G F1)
    (hco : tl'.coefficientsF F1 c1 = .ok (((), F2), c1')) (hd : c2.ch.dry = false)
    (hst : tl'.tileSelfTestF F2 c2 = .ok (((), F2'), c2')) (hW : ReadsRaw ρ tl' funs F2 W A)
    (hx : ∀ x ∈ readsList tl' funs, (tl0.ix.U.getD x.1.tree none).isSome = true ∧
      ∀ d, d < (tl'.mats.getD x.1.mat {}).k → posOf tl' x.1 x.2 d < nU.getD x.1.tree 0) :
    RawRows W tl G funs (ρ.val G.theta) A := by
  obtain ⟨hUs, hZ, -, -⟩ := addTreesF_frame tl0 tla F0 Fa T0 Ta nU aTX hb hbLine hadd
  have k12 := coefficientsF_frame tl' F1 F2 c1 c1' hco
  have kG2 : FrameKept G F2 := hk2.trans k12
  have ka2 : ShapesKept Fa F2 := hk1.trans kG2.shapes
  refine rawRows_before ρ tl tl' funs F G F2 F2' c c' c2 c2' W A hobj hd hst kG2.theta hW ?_ ?_
  · have e : shapeAt F2 tl0.ix.ZZ = _ := (ka2.shape _).trans hZ.2
    rw [hix, hbl]
    exact congrArg (·.2.2.2) e
  · intro x hxm
    obtain ⟨hs, hp⟩ := hx x hxm
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hs
    have h3 : x.1.tree < 3 := by
      rcases reads_tree tl' funs x hxm with e | e <;> omega
    have hu : uOf tl' x.1 = t := by
      unfold uOf
      rw [hix, ht]
      rfl
    have sa := hUs x.1.tree h3 t ht
    rw [hu]
    refine ⟨unitRow_tested tl' x.1.tree t _ F1 F2 F2' c1 c1' c2 c2' (by omega)
      (by rw [hix]; exact ht) (sa.kept ka2) hco hd hst, ?_⟩
    intro d hdk
    rw [colsU_shape, (sa.kept hk1).shape]
    exact hp d hdk

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.rawRows_whole
