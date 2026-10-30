-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PanVB.lean: CONDITIONAL.

What is here. Each panel of the verifier's two lists of panels of the batched sumcheck, placed or
not, has a first weight claim or a B side (`panelsA_vb`, `panelsT_vb`, `placePanels_vb`): read off
the verifier's own text (OnBytes/Model/LayerPanels.lean): `plain` gives a panel a first weight claim
just where it is handed no B side, and `tri` always. It is the hypothesis hH of
Johnson/Road/K4/C/PanelTabsOf.lean's there_of_end. The walk is that of
Johnson/Road/K4/C/EntsAt.lean.

  `keyVB b`   a panel's first weight claim, and whether it has a B side.
  `PanVB bl`   each panel of the list has the one or the other.
  `panVB_mem`   so for each member.
  `plain_vb`, `tri_vb`, `panelA_vb`, `panelsA_vb`   the panels of the lookup's join.
  `panelT_vb`, `panelsT_vb`, `placePanels_vb`   those of the second token sumcheck; placing.

Not shown here. That the second list returns: the statement speaks of what is returned, if anything.
Nothing on soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Road.K4.Reads.PanelsEnts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Slots (Gives Side gives_foldlM_inv)

/-- A panel's first weight claim, and whether it has a B side. -/
def keyVB (b : SBlk) : Option ℕ × Bool := (b.v0, b.B.isSome)

/-- Each panel of the list has a first weight claim or a B side. -/
def PanVB (bl : Array SBlk) : Prop :=
  ∀ c ∈ (bl.map keyVB).toList, c.1.isSome = true ∨ c.2 = true

/-- So for each member. -/
theorem panVB_mem {bl : Array SBlk} (h : PanVB bl) {b : SBlk} (hb : b ∈ bl.toList) :
    b.v0.isSome = true ∨ b.B.isSome = true :=
  h (keyVB b) (by rw [Array.toList_map]; exact List.mem_map_of_mem hb)

theorem panVB_empty : PanVB #[] := fun c hc => by simp at hc

theorem panVB_push {bl : Array SBlk} {b : SBlk} (h : PanVB bl)
    (hb : b.v0.isSome = true ∨ b.B.isSome = true) : PanVB (bl.push b) := fun c hc => by
  simp only [Array.map_push, Array.toList_push, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact h c hc
  · exact hb

theorem plain_vb (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ) (A B : Side) (wt : ℕ → E)
    (virt : Option ℕ) {s : Panels} (hs : PanVB s.bl) :
    PanVB (plain y ec claim moeSet ny A B wt virt s).bl := by
  unfold plain
  refine panVB_push hs ?_
  cases B with
  | none => exact Or.inl rfl
  | some g => exact Or.inr rfl

theorem tri_vb (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) (xx : Array Aff)
    (virt : Option ℕ) (wt : E) {s : Panels} (hs : PanVB s.bl) :
    PanVB (tri y ec claim nk sl xx virt wt s).bl := by
  unfold tri
  exact panVB_push hs (Or.inl rfl)

theorem panelA_vb (p : PanelEnv) (ec : E) (el : Array E) (sn : String) {s : Panels}
    (hs : PanVB s.bl) : PanVB (panelA p ec el sn s).bl := by
  unfold panelA
  dsimp only
  split
  · exact plain_vb _ _ _ _ _ _ _ _ _ hs
  split
  · exact plain_vb _ _ _ _ _ _ _ _ _ hs
  split
  · exact plain_vb _ _ _ _ _ _ _ _ _ hs
  split
  · exact plain_vb _ _ _ _ _ _ _ _ _ hs
  split
  · exact plain_vb _ _ _ _ _ _ _ _ _ hs
  · exact hs

theorem panelsA_vb (p : PanelEnv) {s : Panels} (hs : PanVB s.bl) : PanVB (panelsA p s).bl := by
  unfold panelsA
  refine OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Panels => PanVB s.bl)
    (fun s q hs => ?_) _ _ hs
  exact OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Panels => PanVB s.bl)
    (fun s g hs => panelA_vb p _ _ _ hs) _ _ hs

theorem panelT_vb (p : PanelEnv) (ec : E) (el : Array E) (sn : String) {s : Panels}
    (hs : PanVB s.bl) : Gives (panelT p ec el sn s) fun s' => PanVB s'.bl := by
  unfold panelT
  dsimp only
  refine Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ ?_)))))
  · exact Gives.skip fun wh => Gives.pure (plain_vb _ _ _ _ _ _ _ _ _ hs)
  · exact Gives.pure (plain_vb _ _ _ _ _ _ _ _ _ hs)
  · exact Gives.pure hs
  · exact Gives.skip fun ew => Gives.pure (plain_vb _ _ _ _ _ _ _ _ _ hs)
  · exact Gives.skip fun ew => Gives.pure (plain_vb _ _ _ _ _ _ _ _ _ hs)
  · refine gives_foldlM_inv (P := fun s : Panels => PanVB s.bl) (fun s lm hs => ?_) _ _ hs
    refine Gives.ite (Gives.pure (tri_vb _ _ _ _ _ _ _ _ hs)) ?_
    exact Gives.skip fun xx => Gives.pure (tri_vb _ _ _ _ _ _ _ _ hs)
  · exact Gives.pure hs

theorem panelsT_vb (p : PanelEnv) (TS : List ℕ) {s : Panels} (hs : PanVB s.bl) :
    Gives (panelsT p TS s) fun s' => PanVB s'.bl := by
  unfold panelsT
  refine gives_foldlM_inv (P := fun s : Panels => PanVB s.bl) (fun s q hs => ?_) _ _ hs
  exact gives_foldlM_inv (P := fun s : Panels => PanVB s.bl)
    (fun s g hs => panelT_vb p _ _ _ hs) _ _ hs

/-- Placing turns a panel's first place alone. -/
theorem placePanels_vb {bl : Array SBlk} (h : PanVB bl) : PanVB (placePanels bl).1 := by
  unfold placePanels
  refine OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Array SBlk × ℕ => PanVB s.1)
    (fun s i hs => ?_) _ _ h
  show PanVB (s.1.modify i fun b => { b with off := s.2 })
  unfold PanVB
  rw [map_modify_same keyVB (fun b : SBlk => { b with off := s.2 }) (fun _ => rfl)]
  exact hs

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.panVB_mem
#print axioms OnBytes.Road.K4.C.panVB_empty
#print axioms OnBytes.Road.K4.C.panVB_push
#print axioms OnBytes.Road.K4.C.plain_vb
#print axioms OnBytes.Road.K4.C.tri_vb
#print axioms OnBytes.Road.K4.C.panelA_vb
#print axioms OnBytes.Road.K4.C.panelsA_vb
#print axioms OnBytes.Road.K4.C.panelT_vb
#print axioms OnBytes.Road.K4.C.panelsT_vb
#print axioms OnBytes.Road.K4.C.placePanels_vb
