-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndKeep.lean: the steps of a sub-proof's check that leave the batching element
and the shapes of the arrays as they were (OnBytes/Model/Hide.lean, OnBytes/Model/Tail.lean).

Definitions, and theorems with their proofs. The theorems on the smallness test's claims speak of
two states of one check: the state that objectsF returns, and the later state at which the verifier
tests the weights. Between them, and before them, stand steps that differ by the kind of sub-proof.
This file has one law for each basic step, so that a fact on an array's shape, or the batching
element, can be carried from one state to another.

Main names:
  `ShapesKept F G`: G has as many arrays as F, and each has the same kind and the same numbers of
    rows, of columns and of virtual rows (`shapeAt`, OnBytes/Tie/Pv/Tail/EndCoef.lean).
  `FrameKept F G`: the shapes are kept, and the batching element.
  `ShapesKept.refl`, `ShapesKept.trans`, `FrameKept.refl`, `FrameKept.trans`.
  `shapes_of_frame`: the shapes are kept where the library's `treesFrame` is
    (OnBytes/Model/HideLaws.lean).
  `FrameKept.of_same`: a step that leaves the arrays and the batching element.
  `took_frame`, `owe_frame`, `paid_frame`, `hide_frame`, `hideRun_frame`, `kap_frame`, `push_frame`,
    `lin_frame`, `lins_frame`, `rootTaken_frame`, `onRow_frame`, `coefficientsF_frame`: the steps.
  `batchBy_shapes`, `slots_shapes`: drawing the batching element and setting up the slots keep the
    shapes.
  `UShape.kept`, `UShape.kept_back`: the shape of a table's vector
    (OnBytes/Tie/Pv/Tail/EndFrame.lean) goes along, forwards and backwards.

Limits: single steps alone. No check of a sub-proof is followed from its beginning to its end here.


-/
import OnBytes.Tie.Pv.Tail.EndFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port

/-- G has as many arrays as F, each of the same kind and sizes. -/
structure ShapesKept (F G : Fork) : Prop where
  size : G.trees.size = F.trees.size
  shape : ∀ t, shapeAt G t = shapeAt F t

/-- Every state keeps its own shapes. -/
theorem ShapesKept.refl (F : Fork) : ShapesKept F F := ⟨rfl, fun _ => rfl⟩

/-- `ShapesKept` goes through a state between. -/
theorem ShapesKept.trans {F G H : Fork} (h : ShapesKept F G) (h' : ShapesKept G H) :
    ShapesKept F H :=
  ⟨h'.size.trans h.size, fun t => (h'.shape t).trans (h.shape t)⟩

/-- It goes both ways. -/
theorem ShapesKept.symm {F G : Fork} (h : ShapesKept F G) : ShapesKept G F :=
  ⟨h.size.symm, fun t => (h.shape t).symm⟩

/-- The shapes are kept, and the batching element. -/
structure FrameKept (F G : Fork) : Prop where
  theta : G.theta = F.theta
  shapes : ShapesKept F G

/-- Every state keeps its own. -/
theorem FrameKept.refl (F : Fork) : FrameKept F F := ⟨rfl, ShapesKept.refl F⟩

/-- `FrameKept` goes through a state between. -/
theorem FrameKept.trans {F G H : Fork} (h : FrameKept F G) (h' : FrameKept G H) : FrameKept F H :=
  ⟨h'.theta.trans h.theta, h.shapes.trans h'.shapes⟩

/-- A step that leaves the arrays keeps the shapes. -/
theorem ShapesKept.of_trees {F G : Fork} (h : G.trees = F.trees) : ShapesKept F G :=
  ⟨by rw [h], fun t => by unfold shapeAt; rw [h]⟩

/-- A step that leaves the arrays and the batching element. -/
theorem FrameKept.of_same {F G : Fork} (h : G.trees = F.trees) (ht : G.theta = F.theta) :
    FrameKept F G := ⟨ht, ShapesKept.of_trees h⟩

/-- The kind and sizes of an array, read off its frame. -/
def shapeOfFrame (x : HTree × Array (HRow × Nat)) : HKind × Nat × Nat × Nat :=
  (x.1.kind, x.1.R, x.1.K, x.2.size)

/-- The shapes are kept where the library's frame of the arrays is. -/
theorem shapes_of_frame {F G : Fork} (h : treesFrame G.trees = treesFrame F.trees) :
    ShapesKept F G := by
  have key : ∀ (a : Array HTree) (t : Nat),
      ((a.getD t {}).kind, (a.getD t {}).R, (a.getD t {}).K, (a.getD t {}).rows.size) =
        shapeOfFrame ((treesFrame a).getD t (HTree.frame {})) := by
    intro a t
    unfold treesFrame shapeOfFrame
    by_cases ht : t < a.size
    · simp [Array.getD, ht, HTree.frame]
    · simp [Array.getD, ht, HTree.frame]
  refine ⟨?_, fun t => ?_⟩
  · have := congrArg Array.size h
    simpa [treesFrame] using this
  · unfold shapeAt
    rw [key, key, h]

/-! ## Steps that leave the arrays -/

/-- Taking slots. -/
theorem took_frame (F : Fork) (n : Nat) : FrameKept F { F with next := F.next + n } :=
  FrameKept.of_same rfl rfl

/-- Entering an owed claim. -/
theorem owe_frame (F : Fork) (what : String) : FrameKept F (F.owe what).2 :=
  FrameKept.of_same rfl rfl

/-- Marking an owed claim as added. -/
theorem paid_frame (F : Fork) (i : Nat) : FrameKept F (F.paid i) := FrameKept.of_same rfl rfl

/-- Putting a value under a slot. -/
theorem hide_frame {F G : Fork} {j : Nat} {y factor : E} (h : F.hide j y factor = some G) :
    FrameKept F G := by
  unfold Fork.hide at h
  split at h
  · obtain rfl := Option.some.inj h
    exact FrameKept.of_same rfl rfl
  · simp at h

/-- The steps of a run of values. -/
theorem hideSteps_frame (factor : E) : ∀ (l : List E) (first : Nat) (F : Fork) (x : Nat × Fork),
    l.foldlM (Fork.hideStep factor) (first, F) = some x → FrameKept F x.2
  | [], first, F, x, h => by
    have hx : (first, F) = x := by simpa using h
    subst hx
    exact FrameKept.refl F
  | y :: l, first, F, x, h => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.hideStep factor (first, F) y with
    | none => simp [hq] at h
    | some s =>
      rw [hq] at h
      have h2 : l.foldlM (Fork.hideStep factor) s = some x := by simpa using h
      simp only [Fork.hideStep] at hq
      cases hh : F.hide first y factor with
      | none => simp [hh] at hq
      | some H =>
        rw [hh] at hq
        obtain rfl : (first + 1, H) = s := by simpa using hq
        exact (hide_frame hh).trans (hideSteps_frame factor l _ _ _ h2)

/-- Putting a run of values under slots. -/
theorem hideRun_frame {F G : Fork} {first : Nat} {v : Array E} {factor : E}
    (h : F.hideRun first v factor = some G) : FrameKept F G := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    exact hideSteps_frame factor _ _ _ _ hx
  · simp at h

/-- Handing out the weight of the next claim. -/
theorem kap_frame {F G : Fork} {k : E} (h : F.kap = some (k, G)) : FrameKept F G := by
  obtain ⟨-, hG, -, -⟩ := Fork.kap_spec F G k h
  rw [hG]
  exact FrameKept.of_same rfl rfl

/-- Drawing the batching element keeps the shapes. -/
theorem batchBy_shapes {F G : Fork} {x : E} (h : F.batchBy x = some G) : ShapesKept F G := by
  unfold Fork.batchBy at h
  split at h
  · simp at h
  · obtain rfl := Option.some.inj h
    exact ShapesKept.of_trees rfl

/-- Setting up the slots keeps the shapes. -/
theorem slots_shapes (F : Fork) (n : Nat) : ShapesKept F (F.slots n) := ShapesKept.of_trees rfl

/-! ## Steps that change the arrays -/

/-- The entries of a form, added to the weights one after the other, keep the frame. -/
theorem pushEnts_frame (w : E) : ∀ (l : List Ent) (a b : Array HTree),
    l.foldlM (Fork.pushEnt w) a = some b → treesFrame b = treesFrame a
  | [], a, b, h => by
    obtain rfl : a = b := by simpa using h
    rfl
  | x :: l, a, b, h => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.pushEnt w a x with
    | none => simp [hq] at h
    | some a1 =>
      rw [hq] at h
      exact (pushEnts_frame w l a1 b (by simpa using h)).trans (pushEnt_frame w a a1 x hq)

/-- Adding a multiple of a form to the one equation. -/
theorem push_frame {F G : Fork} {w : E} {a : Aff} (h : F.push w a = some G) : FrameKept F G := by
  unfold Fork.push at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rename_i trees' LS' h1 h2
      obtain rfl := Option.some.inj h
      rw [← Array.foldlM_toList] at h1
      exact ⟨rfl, shapes_of_frame (pushEnts_frame w _ _ _ h1)⟩
    · simp at h

/-- Adding a claim. -/
theorem lin_frame {F G : Fork} {f : Aff} (h : F.lin f = some G) : FrameKept F G := by
  unfold Fork.lin at h
  cases hk : F.kap with
  | none => simp [hk] at h
  | some x =>
    obtain ⟨k, H⟩ := x
    simp only [hk, Option.bind_some] at h
    exact (kap_frame hk).trans (push_frame h)

/-- Adding a list of claims. -/
theorem lins_frame : ∀ (l : List Aff) (F G : Fork), F.lins l = some G → FrameKept F G
  | [], F, G, h => by
    obtain rfl : F = G := by simpa [Fork.lins] using h
    exact FrameKept.refl F
  | a :: l, F, G, h => by
    simp only [Fork.lins, List.foldlM_cons] at h
    cases hq : F.lin a with
    | none => simp [hq] at h
    | some H =>
      rw [hq] at h
      exact (lin_frame hq).trans (lins_frame l H G (by simpa [Fork.lins] using h))

/-- Changing one virtual row. -/
theorem onRow_frame (F : Fork) (t r : Nat) (f : HRow → HRow) :
    FrameKept F (HTailF2.onRow F t r f) :=
  ⟨rfl, ⟨by
    show (F.trees.modify t _).size = _
    rw [Array.size_modify], fun t' => shapeAt_onRow F t' t r f⟩⟩

/-- Noting a commitment. -/
theorem rootTaken_frame (F : Fork) (t w : Nat) : FrameKept F (F.rootTaken t w) := by
  refine ⟨rfl, ⟨?_, fun t' => ?_⟩⟩
  · show (F.trees.modify t _).size = _
    rw [Array.size_modify]
  · unfold shapeAt
    show (((F.trees.modify t fun X => { X with root := some w }).getD t' {}).kind,
      ((F.trees.modify t fun X => { X with root := some w }).getD t' {}).R,
      ((F.trees.modify t fun X => { X with root := some w }).getD t' {}).K,
      ((F.trees.modify t fun X => { X with root := some w }).getD t' {}).rows.size) = _
    rw [getD_modify]
    by_cases hc : t = t' ∧ t' < F.trees.size
    · rw [if_pos hc]
    · rw [if_neg hc]

/-- Setting the row weights of every virtual row. -/
theorem coefficientsF_frame (tl : HTailF2) (F G : Fork) (c c' : Ctx)
    (h : tl.coefficientsF F c = .ok (((), G), c')) : FrameKept F G := by
  obtain ⟨hs, hz⟩ := coefficientsF_shape tl F G c c' h
  refine ⟨?_, ⟨hz, hs⟩⟩
  rw [(coefficientsF_rest tl F G c c' h).1]

/-! ## The shape of a table's vector goes along -/

/-- Forwards. -/
theorem UShape.kept {F G : Fork} {tU cols : Nat} (h : UShape F tU cols) (k : ShapesKept F G) :
    UShape G tU cols := ⟨by rw [k.size]; exact h.inside, (k.shape tU).trans h.shape⟩

/-- Backwards. -/
theorem UShape.kept_back {F G : Fork} {tU cols : Nat} (h : UShape G tU cols)
    (k : ShapesKept F G) : UShape F tU cols := h.kept k.symm

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.shapes_of_frame
#print axioms OnBytes.Tie.Pv.Tail.lins_frame
#print axioms OnBytes.Tie.Pv.Tail.hideRun_frame
#print axioms OnBytes.Tie.Pv.Tail.coefficientsF_frame
