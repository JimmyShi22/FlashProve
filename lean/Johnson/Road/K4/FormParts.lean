-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FormParts.lean: the two forms that the end of the batched sumcheck of a layers'
sub-proof leaves, Alin and Blin, are worth the extensions, at the end point, of the parts of the two
long vectors that are given as forms.

Johnson/Road/FormsKeysEnd.lean (ends_mean) says what a form's value PLUS the panels' shares at true
end values is: the extension of the whole long vector. Here the never-sent vectors and the vectors
of the weight claims are set to 0, of which the end values 0 are true. What is left of the long
vectors is what the panels give as forms; what is left of the sums is the forms' values.

Main names:
  `dEnd_zero`: at end values 0 a panel adds nothing to the two elements of the field.
  `endsTrue_zero`: the end values 0 are true of the vectors 0.
  `forms_ext`: the two values, for any list of panels whose numbers are in order (PanelOK).
  `forms_ext_own`: the same on the verifier's own list, under the caller's own test of the number
    of places.
Limits. In one world, whatever its entries of the reads are: nothing here says that they are true
of cells. The A side's part holds the values that the second token sumcheck sent, as they were sent
(the head of Johnson/Road/FormsKeysEnd.lean). Every statement begins "if stackEnd returns". Nothing
on the library's typed sumcheck, on a run, on soundness or on hiding.


-/
import Johnson.Road.FormsKeysEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (SBlk StackEnd stackEnd Lay placePanels Panels PanelEnv panelsA panelsT)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- At end values 0 a panel adds nothing to the two elements of the field. -/
theorem dEnd_zero (y : Lay) (rs : Array E) (lam : ℕ) (om : Array E) (b : SBlk) :
    (dEnd ρ W y rs lam om (fun _ => 0) (fun _ => 0) b).2.2.1 = 0 ∧
      (dEnd ρ W y rs lam om (fun _ => 0) (fun _ => 0) b).2.2.2.1 = 0 := by
  unfold dEnd
  split <;> simp

/-- The end values 0 are true of the vectors 0. -/
theorem endsTrue_zero (rs : Array E) (b : SBlk) :
    EndsTrue ρ rs (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) b :=
  ⟨fun _ _ _ => by simp, fun _ _ _ => by simp [gsum], fun _ _ _ => by simp [gsum],
    fun _ _ _ _ _ => by simp⟩

/-- **The two forms are worth the extensions of the long vectors' form parts.** -/
theorem forms_ext {y : Lay} {rs : Array E} {lam : ℕ} {om H1 V : Array E} {bl : Array SBlk}
    {shownA shownB : E} {s' : StackEnd} (ok : ∀ b ∈ bl.toList, PanelOK y rs lam b)
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s') :
    s'.Alin.value ρ W =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y * vecOf (aG ρ W y om fun _ _ => 0) bl.toList Y ∧
      s'.Blin.value ρ W =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y * vecOf (bG ρ W fun _ _ => 0) bl.toList Y := by
  obtain ⟨a, b⟩ := ends_mean (ρ := ρ) (W := W) (om := om) (h1 := fun _ => 0) (vv := fun _ => 0)
    (hv := fun _ _ => 0) (wv := fun _ _ => 0) ok (fun b _ => endsTrue_zero rs b) h
  unfold AsAt at a
  unfold BsAt at b
  have zA : (bl.toList.map fun b =>
      (dEnd ρ W y rs lam om (fun _ => 0) (fun _ => 0) b).2.2.1) = bl.toList.map fun _ => 0 :=
    List.map_congr_left fun b _ => (dEnd_zero y rs lam om b).1
  have zB : (bl.toList.map fun b =>
      (dEnd ρ W y rs lam om (fun _ => 0) (fun _ => 0) b).2.2.2.1) = bl.toList.map fun _ => 0 :=
    List.map_congr_left fun b _ => (dEnd_zero y rs lam om b).2
  rw [zA] at a
  rw [zB] at b
  refine ⟨?_, ?_⟩
  · rw [← a]
    simp
  · rw [← b]
    simp

/-- The same on the verifier's own list of panels. -/
theorem forms_ext_own {p : PanelEnv} {TS : List ℕ} {pans : Panels} {rs : Array E} {lam : ℕ}
    {om H1 V : Array E} {shownA shownB : E} {s' : StackEnd}
    (hp : panelsT p TS (panelsA p {}) = some pans)
    (hl : (ceilLog2 (placePanels pans.bl).2 == lam) = true) (hrs : lam ≤ rs.size)
    (h : stackEnd p.v.y (placePanels pans.bl).1 rs lam om H1 V shownA shownB = some s') :
    s'.Alin.value ρ W =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          vecOf (aG ρ W p.v.y om fun _ _ => 0) (placePanels pans.bl).1.toList Y ∧
      s'.Blin.value ρ W =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          vecOf (bG ρ W fun _ _ => 0) (placePanels pans.bl).1.toList Y :=
  forms_ext (placed_ok pans.bl (shape_panels p TS hp) (places_le hl) hrs) h

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.forms_ext
#print axioms OnBytes.Road.K4.forms_ext_own
