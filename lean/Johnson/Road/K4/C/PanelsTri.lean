-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PanelsTri.lean: on the verifier's panels with the selector.

What is here. The layers' own rounds (sub-protocol K4), the batched sumcheck: a panel with the
selector has as many rows as there are experts, and where its column factor is a never-sent vector
it has as many columns as an expert has hidden units: by the way in which the verifier's functions
make a panel (OnBytes/Model/LayerPanels.lean). The proofs follow the library's virt_plain to
virt_placed (Johnson/Road/K4/GatedSays.lean) with another predicate. A definition; statements and
proofs.

  `TriOK`   the rows and the columns of a panel with the selector.
  `triOK_plain`, `triOK_tri`, `triOK_panelA`, `triOK_panelT`   each function keeps it.
  `triOK_panels`   the verifier's own list of panels has it.
  `triOK_placed`   the placing changes nothing of it.

Not shown here. That the verifier's list of panels returns anywhere: the last two statements start
from a return. Public numbers alone.
No property is claimed.
-/
import Johnson.Road.K4.C.DownPanel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk Lay placePanels Panels PanelEnv panelA panelT panelsA panelsT)

/-- The rows and the columns of a panel with the selector. -/
def TriOK (y : Lay) (b : SBlk) : Prop :=
  b.tri = true → b.ni = y.h.NE ∧ ∀ k, b.virt = some k → b.ny = y.h.fe

/-- The function plain appends a panel without the selector. -/
theorem triOK_plain (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A B : Option (ℕ → ℕ → Option Aff)) (wt : ℕ → E) (virt : Option ℕ) (s : Panels)
    (hs : ∀ b ∈ s.bl.toList, TriOK y b) :
    ∀ b ∈ (Layer.plain y ec claim moeSet ny A B wt virt s).bl.toList, TriOK y b := by
  intro b hb
  unfold Layer.plain at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · intro h
    cases h

/-- The function tri appends a panel with as many rows as experts. -/
theorem triOK_tri (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) (xx : Array Aff)
    (virt : Option ℕ) (wt : E) (s : Panels) (hv : ∀ k, virt = some k → nk = y.h.fe)
    (hs : ∀ b ∈ s.bl.toList, TriOK y b) :
    ∀ b ∈ (Layer.tri y ec claim nk sl xx virt wt s).bl.toList, TriOK y b := by
  intro b hb
  unfold Layer.tri at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · exact fun _ => ⟨rfl, hv⟩

/-- The panels of one segment of the lookup's join. -/
theorem triOK_panelA (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels)
    (hs : ∀ b ∈ s.bl.toList, TriOK p.v.y b) :
    ∀ b ∈ (panelA p ec el sn s).bl.toList, TriOK p.v.y b := by
  simp only [panelA]
  split_ifs <;> first
    | exact hs
    | exact triOK_plain _ _ _ _ _ _ _ _ _ _ hs

/-- The panels of one segment of the second token sumcheck's terms. -/
theorem triOK_panelT (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    (hs : ∀ b ∈ s.bl.toList, TriOK p.v.y b) (h : panelT p ec el sn s = some s') :
    ∀ b ∈ s'.bl.toList, TriOK p.v.y b := by
  simp only [panelT] at h
  split_ifs at h <;> first
    | (cases h; exact hs)
    | (cases h; exact triOK_plain _ _ _ _ _ _ _ _ _ _ hs)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h
       exact triOK_plain _ _ _ _ _ _ _ _ _ _ hs)
    | exact foldlM_inv_mem (fun s : Panels => ∀ b ∈ s.bl.toList, TriOK p.v.y b) _ _
        (fun s lm s' hm hs h => by
          first
            | (cases h
               exact triOK_tri _ _ _ _ _ _ _ _ _ (fun _ _ => rfl) hs)
            | (obtain ⟨_, _, h⟩ := bind_some h; cases h
               exact triOK_tri _ _ _ _ _ _ _ _ _ (fun _ e => nomatch e) hs))
        _ _ hs h

/-- The verifier's own list of panels. -/
theorem triOK_panels (p : PanelEnv) (TS : List ℕ) {pans : Panels}
    (h : panelsT p TS (panelsA p {}) = some pans) : ∀ b ∈ pans.bl.toList, TriOK p.v.y b := by
  have h0 : ∀ b ∈ ({} : Panels).bl.toList, TriOK p.v.y b :=
    fun b hb => absurd hb List.not_mem_nil
  have hA : ∀ b ∈ (panelsA p {}).bl.toList, TriOK p.v.y b := by
    unfold panelsA
    refine foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, TriOK p.v.y b) _ (fun s q hs => ?_)
      _ _ h0
    exact foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, TriOK p.v.y b) _
      (fun s g hs => triOK_panelA p _ _ _ s hs) _ _ hs
  unfold panelsT at h
  refine foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, TriOK p.v.y b) _
    (fun s q s' hs e => ?_) _ _ _ hA h
  exact foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, TriOK p.v.y b) _
    (fun s g s' hs e => triOK_panelT p _ _ _ s s' hs e) _ _ _ hs e

/-- The placing changes nothing of it. -/
theorem triOK_placed {y : Lay} {bl : Array SBlk} (R : ∀ b ∈ bl.toList, TriOK y b) :
    ∀ b ∈ (placePanels bl).1.toList, TriOK y b := by
  intro b hb
  obtain ⟨b0, h0, o, rfl⟩ := placed_from bl b hb
  exact R b0 h0

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.triOK_plain
#print axioms OnBytes.Road.K4.C.triOK_tri
#print axioms OnBytes.Road.K4.C.triOK_panelA
#print axioms OnBytes.Road.K4.C.triOK_panelT
#print axioms OnBytes.Road.K4.C.triOK_panels
#print axioms OnBytes.Road.K4.C.triOK_placed
