-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/SecondPass.lean: CONDITIONAL. Statements with their proofs.

What is here. The layers' own rounds (sub-protocol K4): THE PANELS OF THE SECOND PASS ALONE (those
of the second token sumcheck's terms: `SBlk.claim` = 1), in the verifier's list of panels
(OnBytes/Model/LayerPanels.lean): a walk over `panelsA`, `panelsT` and `placePanels` that asks
nothing of a panel of the first pass. Of each panel of the second pass it says: every entry that its
two sides and its column factors name lies in the array of the reads at a place with the test T
(`CoreTest`, EntsAt.lean); with the selector it has a first weight claim; without, it holds no
never-sent vector and has an A side.
Why. EntsAt.lean's walk speaks of all panels and so asks the test at the tables of three points, zt,
rt and Y. The honest side's reads at a token hold the tables at rt and Y alone; of the list it takes
the panels of the second pass alone (`Sides.trips`, Johnson/Desc/K4/Honest/Sides.lean).

Not shown here. `PtAt` is a hypothesis (PtsHave.lean pays it at the honest reads). That a list of
panels returns: not here: each statement speaks of what is returned, if anything. That a side
returns at a row and a column: PanelTabsOf.lean. Nothing on soundness, on completeness or on any
other property. No property is claimed.

  `key2`, `Second`, `Pan2`, `pan2_mem`   what is said of a panel; of a list; of a member
  `plain_first`, `plain_second`, `tri_second`   one panel more
  `panelA_2`, `panelsA_2`, `panelT_2`, `panelsT_2`, `placePanels_2`   **the walk**
-/
import Johnson.Road.K4.C.EntsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Reads (entsIn_ofConst)
open OnBytes.Desc.First.K4.Slots (Gives Side core gives_foldlM_inv)

/-- What is read of a panel: its pass; whether its rows carry the selector; whether it has a first
weight claim; its never-sent vector's number; its two sides and column factors. -/
def key2 (b : SBlk) : ℕ × Bool × Bool × Option ℕ × (Side × Side × Array Aff) :=
  (b.claim, b.tri, b.v0.isSome, b.virt, core b)

/-- **What is said of a panel of the second pass**; of another, nothing. It is what the walk below
concludes of each panel; the definition claims nothing. -/
def Second (v : Env) (T : ℕ → Prop) (c : ℕ × Bool × Bool × Option ℕ × (Side × Side × Array Aff)) :
    Prop :=
  c.1 = 1 → CoreTest v T c.2.2.2.2 ∧ (c.2.1 = true → c.2.2.1 = true) ∧
    (c.2.1 = false → c.2.2.2.1 = none ∧ c.2.2.2.2.1.isSome = true)

/-- So for each panel of the list. -/
def Pan2 (v : Env) (T : ℕ → Prop) (bl : Array SBlk) : Prop :=
  ∀ c ∈ (bl.map key2).toList, Second v T c

variable {v : Env} {T : ℕ → Prop} {S : String → Prop}

/-- So for each member. -/
theorem pan2_mem {bl : Array SBlk} (h : Pan2 v T bl) {b : SBlk} (hb : b ∈ bl.toList) :
    Second v T (key2 b) :=
  h (key2 b) (by rw [Array.toList_map]; exact List.mem_map_of_mem hb)

theorem pan2_empty : Pan2 v T #[] := fun c hc => by simp at hc

theorem pan2_push {bl : Array SBlk} {b : SBlk} (h : Pan2 v T bl) (hb : Second v T (key2 b)) :
    Pan2 v T (bl.push b) := fun c hc => by
  simp only [Array.map_push, Array.toList_push, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact h c hc
  · exact hb

/-- A panel of the first pass more: nothing is asked of it. -/
theorem plain_first (y : Lay) (ec : E) (moeSet : Bool) (ny : ℕ) (A B : Side) (wt : ℕ → E)
    (virt : Option ℕ) {s : Panels} (hs : Pan2 v T s.bl) :
    Pan2 v T (plain y ec 0 moeSet ny A B wt virt s).bl := by
  unfold plain
  exact pan2_push hs fun (h : (0 : ℕ) = 1) => absurd h (by decide)

/-- A panel of the second pass more, without the selector and without a never-sent vector. -/
theorem plain_second (y : Lay) (ec : E) (moeSet : Bool) (ny : ℕ) {A B : Side} (wt : ℕ → E)
    {s : Panels} (hs : Pan2 v T s.bl) (hA : SideAt v T A) (hB : SideAt v T B)
    (hs1 : A.isSome = true) : Pan2 v T (plain y ec 1 moeSet ny A B wt none s).bl := by
  unfold plain
  refine pan2_push hs fun _ => ⟨⟨fun f hf i yv => ?_, fun f hf i yv => ?_, inTest_getD_empty⟩,
    fun (h : false = true) => absurd h (by decide), fun _ => ⟨rfl, ?_⟩⟩
  · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact hA g hg _ _
  · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact hB g hg _ _
  · show (A.map _).isSome = true
    rw [Option.isSome_map]
    exact hs1

/-- A panel of the second pass more, with the selector. -/
theorem tri_second (y : Lay) (ec : E) (nk : ℕ) (sl : Array E) {xx : Array Aff} (virt : Option ℕ)
    (wt : E) {s : Panels} (hs : Pan2 v T s.bl) (hx : ∀ k, InTest v T (xx.getD k {})) :
    Pan2 v T (tri y ec 1 nk sl xx virt wt s).bl := by
  unfold tri
  exact pan2_push hs fun _ => ⟨⟨sideAt_none, sideAt_none, hx⟩, fun _ => rfl,
    fun (h : true = false) => absurd h (by decide)⟩

theorem panelA_2 (p : PanelEnv) (ec : E) (el : Array E) (sn : String) {s : Panels}
    (hs : Pan2 p.v T s.bl) : Pan2 p.v T (panelA p ec el sn s).bl := by
  unfold panelA
  dsimp only
  split
  · exact plain_first _ _ _ _ _ _ _ _ hs
  split
  · exact plain_first _ _ _ _ _ _ _ _ hs
  split
  · exact plain_first _ _ _ _ _ _ _ _ hs
  split
  · exact plain_first _ _ _ _ _ _ _ _ hs
  split
  · exact plain_first _ _ _ _ _ _ _ _ hs
  · exact hs

theorem panelsA_2 (p : PanelEnv) {s : Panels} (hs : Pan2 p.v T s.bl) :
    Pan2 p.v T (panelsA p s).bl := by
  unfold panelsA
  refine OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Panels => Pan2 p.v T s.bl)
    (fun s q hs => ?_) _ _ hs
  exact OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Panels => Pan2 p.v T s.bl)
    (fun s g hs => panelA_2 p _ _ _ hs) _ _ hs

/-- **The panels of one segment of a call with terms in the second token sumcheck.** -/
theorem panelT_2 (p : PanelEnv) (H : PtAt p.v T S) (hrt : S "rt") (hY : S "Y") (ec : E)
    (el : Array E) (sn : String) {s : Panels} (hs : Pan2 p.v T s.bl) :
    Gives (panelT p ec el sn s) fun s' => Pan2 p.v T s'.bl := by
  unfold panelT
  dsimp only
  refine Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ (Gives.ite ?_ ?_)))))
  · exact Gives.skip fun wh => Gives.pure (plain_second _ _ _ _ _ hs
      (sideAt_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideAt_some fun _ _ => at_SxsA H _ hY _) rfl)
  · exact Gives.pure (plain_second _ _ _ _ _ hs
      (sideAt_some fun _ _ => at_shIn (at_tensorAt H _ hrt) _ _) sideAt_none rfl)
  · exact Gives.pure hs
  · exact Gives.skip fun ew => Gives.pure (plain_second _ _ _ _ _ hs
      (sideAt_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideAt_some fun _ _ => at_shSum H _ _ _ hrt _) rfl)
  · exact Gives.skip fun ew => Gives.pure (plain_second _ _ _ _ _ hs
      (sideAt_some fun _ _ => Gives.some (entsIn_ofConst _))
      (sideAt_some fun _ _ => at_shA H _ hrt _ _) rfl)
  · refine gives_foldlM_inv (P := fun s : Panels => Pan2 p.v T s.bl) (fun s lm hs => ?_) _ _ hs
    refine Gives.ite (Gives.pure (tri_second _ _ _ _ _ _ hs inTest_getD_empty)) ?_
    exact Gives.bind (mapM_getD_at fun _ => at_shIn (at_tensorAt H _ hrt) _ _) fun xx hx =>
      Gives.pure (tri_second _ _ _ _ _ _ hs hx)
  · exact Gives.pure hs

theorem panelsT_2 (p : PanelEnv) (H : PtAt p.v T S) (hrt : S "rt") (hY : S "Y") (TS : List ℕ)
    {s : Panels} (hs : Pan2 p.v T s.bl) :
    Gives (panelsT p TS s) fun s' => Pan2 p.v T s'.bl := by
  unfold panelsT
  refine gives_foldlM_inv (P := fun s : Panels => Pan2 p.v T s.bl) (fun s q hs => ?_) _ _ hs
  exact gives_foldlM_inv (P := fun s : Panels => Pan2 p.v T s.bl)
    (fun s g hs => panelT_2 p H hrt hY _ _ _ hs) _ _ hs

/-- Placing turns a panel's first place alone. -/
theorem placePanels_2 {bl : Array SBlk} (h : Pan2 v T bl) : Pan2 v T (placePanels bl).1 := by
  unfold placePanels
  refine OnBytes.Desc.First.K4.Slots.foldl_inv (P := fun s : Array SBlk × ℕ => Pan2 v T s.1)
    (fun s i hs => ?_) _ _ h
  show Pan2 v T (s.1.modify i fun b => { b with off := s.2 })
  unfold Pan2
  rw [map_modify_same key2 (fun b : SBlk => { b with off := s.2 }) (fun _ => rfl)]
  exact hs

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.pan2_mem
#print axioms OnBytes.Road.K4.C.pan2_empty
#print axioms OnBytes.Road.K4.C.pan2_push
#print axioms OnBytes.Road.K4.C.plain_first
#print axioms OnBytes.Road.K4.C.plain_second
#print axioms OnBytes.Road.K4.C.tri_second
#print axioms OnBytes.Road.K4.C.panelA_2
#print axioms OnBytes.Road.K4.C.panelsA_2
#print axioms OnBytes.Road.K4.C.panelT_2
#print axioms OnBytes.Road.K4.C.panelsT_2
#print axioms OnBytes.Road.K4.C.placePanels_2
