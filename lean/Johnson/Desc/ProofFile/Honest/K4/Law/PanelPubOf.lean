-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PanelPubOf.lean: CONDITIONAL.

What is here. The public hypothesis `PanelPub` of PanelTiesOf.lean, and `TripPub` of
TripTiesOf.lean, at every panel of the verifier's list as the honest side lays it: shown from the
verifier's own text for the panels. A panel with the selector has a row for each routed expert (a
walk over the list, here). Its never-sent vector is not number 0, and a never-sent vector that is a
whole A side is number 0 with the bits of the width f (the library's `virt_panels`,
Johnson/Road/K4/GatedSays.lean). The columns fit the bits (a walk, here). So `pass0_pub`
(PassOf.lean) need not ask `PanelPub`.

  `RowsCols`   the two numbers
  `rc_plain`, `rc_tri`, `rc_panelA`, `rc_panelT`, `rc_panels`, `rc_placed`   the walk
  `tripPub_of`   `TripPub` at the panels that the honest side lays at any shown values
  `panelPub_of`   **`PanelPub` at every panel of the job's data**

Limits. On the verifier's public functions alone. The one premise: the function that lays the
panels, or that makes the job's data, returns. Nothing on a value, a matrix or a world.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PanelTiesOf
import Johnson.Desc.ProofFile.Honest.K4.Law.TripTiesOf
import Johnson.Desc.ProofFile.Honest.K4.Law.TokSig
import Johnson.Road.K4.GatedSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E ceilLog2)
open OnBytes.Model (Aff)
open OnBytes.Model.Layer (SBlk Lay placePanels Panels PanelEnv panelA panelT panelsA panelsT)
open OnBytes.Road (foldl_inv foldlM_inv foldlM_inv_mem placed_from bind_some)
open OnBytes.Road.K4 (virt_panels virt_placed)
open OnBytes.Road.K4.C (sidesEnv stack_panels_at)
open OnBytes.Desc.First.K4.Honest

/-- A panel with the selector has a row for each routed expert; the columns fit the bits. -/
def RowsCols (y : Lay) (b : SBlk) : Prop := (b.tri = true → b.ni = y.h.NE) ∧ b.ny ≤ 2 ^ b.wy

/-- A number is at most two to its bits. -/
theorem le_two_ceil (n : ℕ) : n ≤ 2 ^ ceilLog2 n := by
  rw [OnBytes.Road.ceilLog2_eq_clog]
  exact Nat.le_pow_clog (by decide) n

/-- One plain panel more: the rows and the columns stay as `RowsCols` says. -/
theorem rc_plain (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A B : Option (ℕ → ℕ → Option Aff)) (wt : ℕ → E) (virt : Option ℕ) (s : Panels)
    (hs : ∀ b ∈ s.bl.toList, RowsCols y b) :
    ∀ b ∈ (OnBytes.Model.Layer.plain y ec claim moeSet ny A B wt virt s).bl.toList,
      RowsCols y b := by
  intro b hb
  unfold OnBytes.Model.Layer.plain at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · exact ⟨fun h => Bool.noConfusion h, le_two_ceil _⟩

/-- One panel of three factors more. -/
theorem rc_tri (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) (xx : Array Aff)
    (virt : Option ℕ) (wt : E) (s : Panels) (hs : ∀ b ∈ s.bl.toList, RowsCols y b) :
    ∀ b ∈ (OnBytes.Model.Layer.tri y ec claim nk sl xx virt wt s).bl.toList, RowsCols y b := by
  intro b hb
  unfold OnBytes.Model.Layer.tri at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · exact ⟨fun _ => rfl, le_two_ceil _⟩

/-- The panels that one segment of the lookup's join adds. -/
theorem rc_panelA (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels)
    (hs : ∀ b ∈ s.bl.toList, RowsCols p.v.y b) :
    ∀ b ∈ (panelA p ec el sn s).bl.toList, RowsCols p.v.y b := by
  simp only [panelA]
  split_ifs <;> first
    | exact hs
    | exact rc_plain _ _ _ _ _ _ _ _ _ _ hs

/-- The panels that one segment of the second token sumcheck adds, where the function returns. -/
theorem rc_panelT (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    (hs : ∀ b ∈ s.bl.toList, RowsCols p.v.y b) (h : panelT p ec el sn s = some s') :
    ∀ b ∈ s'.bl.toList, RowsCols p.v.y b := by
  simp only [panelT] at h
  split_ifs at h <;> first
    | (cases h; exact hs)
    | (cases h; exact rc_plain _ _ _ _ _ _ _ _ _ _ hs)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h
       exact rc_plain _ _ _ _ _ _ _ _ _ _ hs)
    | exact foldlM_inv_mem (fun s : Panels => ∀ b ∈ s.bl.toList, RowsCols p.v.y b) _ _
        (fun s lm s' hm hs h => by
          first
            | (cases h
               exact rc_tri _ _ _ _ _ _ _ _ _ hs)
            | (obtain ⟨_, _, h⟩ := bind_some h; cases h
               exact rc_tri _ _ _ _ _ _ _ _ _ hs))
        _ _ hs h

/-- The verifier's own list of panels. -/
theorem rc_panels (p : PanelEnv) (TS : List ℕ) {pans : Panels}
    (h : panelsT p TS (panelsA p {}) = some pans) : ∀ b ∈ pans.bl.toList, RowsCols p.v.y b := by
  have h0 : ∀ b ∈ ({} : Panels).bl.toList, RowsCols p.v.y b :=
    fun b hb => absurd hb List.not_mem_nil
  have hA : ∀ b ∈ (panelsA p {}).bl.toList, RowsCols p.v.y b := by
    unfold panelsA
    refine foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, RowsCols p.v.y b) _ (fun s q hs => ?_)
      _ _ h0
    exact foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, RowsCols p.v.y b) _
      (fun s g hs => rc_panelA p _ _ _ s hs) _ _ hs
  unfold panelsT at h
  refine foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, RowsCols p.v.y b) _
    (fun s q s' hs e => ?_) _ _ _ hA h
  exact foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, RowsCols p.v.y b) _
    (fun s g s' hs e => rc_panelT p _ _ _ s s' hs e) _ _ _ hs e

/-- The placing changes nothing of it. -/
theorem rc_placed {y : Lay} {bl : Array SBlk} (R : ∀ b ∈ bl.toList, RowsCols y b) :
    ∀ b ∈ (placePanels bl).1.toList, RowsCols y b := by
  intro b hb
  obtain ⟨b0, h0, o, rfl⟩ := placed_from bl b hb
  exact R b0 h0

/-- **`TripPub` at the panels that the honest side lays**, at any values sh in the place of the
shown ones. -/
theorem tripPub_of {S : OnBytes.Desc.First.K4.Honest.Sides} {sh : Array E} {bl : Array SBlk}
    {places : ℕ} (h : S.panels sh = some (bl, places)) : ∀ b ∈ bl.toList, TripPub S b := by
  obtain ⟨pans, hp, rfl⟩ := panels_open h
  intro b hb
  obtain ⟨r, c⟩ := rc_placed (rc_panels (sidesEnv S sh) S.TS hp) b hb
  exact ⟨r, c⟩

/-- **`PanelPub` AT EVERY PANEL OF THE JOB's DATA.** CONDITIONAL: on the maker's return. -/
theorem panelPub_of {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) :
    ∀ b ∈ SD.bl.toList, PanelPub SD (ceilLog2 SD.S.v.y.h.f) b := by
  obtain ⟨pans, hp, hbl, _⟩ := stack_panels_at h
  intro b hb
  rw [hbl] at hb
  obtain ⟨r, c⟩ := rc_placed (rc_panels (sidesEnv SD.S shownT) SD.S.TS hp) b hb
  have V := virt_placed (virt_panels (sidesEnv SD.S shownT) SD.S.TS hp) b hb
  refine ⟨r, c, fun ht k hk => ?_, fun ht k hk => ?_⟩
  · obtain ⟨⟨lm, _, e⟩, _⟩ := V.tri ht k hk
    omega
  · obtain ⟨e0, e1, _⟩ := V.plain ht k hk
    exact ⟨e0, e1⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.le_two_ceil
#print axioms ProofFile.Honest.K4.rc_plain
#print axioms ProofFile.Honest.K4.rc_tri
#print axioms ProofFile.Honest.K4.rc_panelA
#print axioms ProofFile.Honest.K4.rc_panelT
#print axioms ProofFile.Honest.K4.rc_panels
#print axioms ProofFile.Honest.K4.rc_placed
#print axioms ProofFile.Honest.K4.tripPub_of
#print axioms ProofFile.Honest.K4.panelPub_of
