-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PansSum.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the batched sumcheck's panels: what the
lighter test on the panels (pansL, Johnson/Desc/First/K4/Returns/Pub/Light.lean) reads of a list of
panels, as ONE SUMMARY of three numbers, and how the summary moves when the verifier's two
functions plain and tri (OnBytes/Model/LayerPanels.lean) append a panel. One definition of a
hypothesis; statements and proofs. General in the sizes.

  `Sm y s pl nv wD`  the panels' places add up to pl; the next weight claim has the number nv; the
                     walk endStepL over the panels returns wD.
  `places_push`, `sm_empty`, `sm_push`   the empty list; one more panel.
  `sm_weight`        plain with a form on the A side and a weight matrix on the B side.
  `sm_forms`         plain with forms on both sides.
  `sm_virt`          plain with a never-sent vector on the A side: the down product's panel.
  `sm_tri`           tri: a panel with the selector.

Not shown here. That a list of panels with a summary exists beyond the empty one. Public data
alone: numbers, and whether a form IS THERE; nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Desc.First.K4.Returns.Pub.Light
import Johnson.Road.FormsKeysLate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay SBlk Panels plain tri)
open OnBytes.Desc.First.K4.RtPub (placesL endStepL sidesThere)

/-- The places of a list with one more panel. -/
theorem places_push (bl : Array SBlk) (b : SBlk) : placesL (bl.push b) = placesL bl + 2 ^ b.w := by
  unfold placesL
  rw [Array.size_push, List.range_succ, List.map_append, List.sum_append]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    have hi' := List.mem_range.mp hi
    unfold wOf
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hi']
    simp [hi']
  · unfold wOf
    simp

/-- **The summary of a list of panels.** This defines a hypothesis; the definition claims
nothing. -/
structure Sm (y : Lay) (s : Panels) (pl nv wD : ℕ) : Prop where
  pl : placesL s.bl = pl
  nv : s.nextV = nv
  st : s.bl.toList.foldlM (endStepL y) 0 = some wD

/-- The empty list. -/
theorem sm_empty (y : Lay) : Sm y {} 0 0 0 := ⟨rfl, rfl, rfl⟩

/-- One more panel. -/
theorem sm_push {y : Lay} {s : Panels} {pl nv wD wD' nv' : ℕ} (H : Sm y s pl nv wD) (b : SBlk)
    (hb : endStepL y wD b = some wD') :
    Sm y { bl := s.bl.push b, nextV := nv' } (pl + 2 ^ b.w) nv' wD' := by
  refine ⟨by rw [places_push, H.pl], rfl, ?_⟩
  show (s.bl.push b).toList.foldlM (endStepL y) 0 = some wD'
  rw [Array.toList_push, List.foldlM_append, H.st]
  show ([b].foldlM (endStepL y) wD) = some wD'
  rw [List.foldlM_cons, hb]
  rfl

/-- **plain with a form on the A side and a weight matrix on the B side.** -/
theorem sm_weight {y : Lay} {s : Panels} {pl nv wD : ℕ} (H : Sm y s pl nv wD) (ec : E)
    (claim : ℕ) (moeSet : Bool) (ny : ℕ) (f : ℕ → ℕ → Option Aff) (wt : ℕ → E)
    (hf : ∀ i, i < (if moeSet then y.LamM else y.Lam) → ∀ yv, yv < ny →
      (f (if moeSet then 2 * i + 1 else i) yv).isSome = true) :
    Sm y (plain y ec claim moeSet ny (some f) none wt none s)
      (pl + 2 ^ (ceilLog2 (if moeSet then y.LamM else y.Lam) + ceilLog2 ny))
      (nv + (if moeSet then y.LamM else y.Lam)) wD := by
  rw [plain_push]
  have e : (if (none : Option (ℕ → ℕ → Option Aff)).isNone = true then
      s.nextV + (if moeSet then y.LamM else y.Lam) else s.nextV) =
      nv + (if moeSet then y.LamM else y.Lam) := by
    rw [H.nv]
    rfl
  rw [e]
  refine sm_push H _ ?_
  show (if sidesThere (blkPlain y ec claim moeSet ny (some f) none wt none s.nextV)
    (fun i yv => f (if moeSet then 2 * i + 1 else i) yv) = true then some wD else none) = some wD
  rw [if_pos]
  unfold sidesThere
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro yv hyv
  rw [Bool.and_eq_true]
  exact ⟨hf i (List.mem_range.mp hi) yv (List.mem_range.mp hyv), rfl⟩

/-- **plain with forms on both sides.** -/
theorem sm_forms {y : Lay} {s : Panels} {pl nv wD : ℕ} (H : Sm y s pl nv wD) (ec : E)
    (claim : ℕ) (moeSet : Bool) (ny : ℕ) (f g : ℕ → ℕ → Option Aff) (wt : ℕ → E)
    (hf : ∀ i, i < (if moeSet then y.LamM else y.Lam) → ∀ yv, yv < ny →
      (f (if moeSet then 2 * i + 1 else i) yv).isSome = true)
    (hg : ∀ i, i < (if moeSet then y.LamM else y.Lam) → ∀ yv, yv < ny →
      (g (if moeSet then 2 * i + 1 else i) yv).isSome = true) :
    Sm y (plain y ec claim moeSet ny (some f) (some g) wt none s)
      (pl + 2 ^ (ceilLog2 (if moeSet then y.LamM else y.Lam) + ceilLog2 ny)) nv wD := by
  rw [plain_push]
  have e : (if (some g : Option (ℕ → ℕ → Option Aff)).isNone = true then
      s.nextV + (if moeSet then y.LamM else y.Lam) else s.nextV) = nv := H.nv
  rw [e]
  refine sm_push H _ ?_
  show (if sidesThere (blkPlain y ec claim moeSet ny (some f) (some g) wt none s.nextV)
    (fun i yv => f (if moeSet then 2 * i + 1 else i) yv) = true then some wD else none) = some wD
  rw [if_pos]
  unfold sidesThere
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro yv hyv
  rw [Bool.and_eq_true]
  refine ⟨hf i (List.mem_range.mp hi) yv (List.mem_range.mp hyv), ?_⟩
  show (false || (g (if moeSet then 2 * i + 1 else i) yv).isSome) = true
  rw [Bool.false_or]
  exact hg i (List.mem_range.mp hi) yv (List.mem_range.mp hyv)

/-- **plain with a never-sent vector on the A side**: the walk takes the panel's bits, if it has
taken none before. -/
theorem sm_virt {y : Lay} {s : Panels} {pl nv : ℕ} (H : Sm y s pl nv 0) (ec : E) (claim : ℕ)
    (moeSet : Bool) (ny : ℕ) (wt : ℕ → E) (k : ℕ) :
    Sm y (plain y ec claim moeSet ny none none wt (some k) s)
      (pl + 2 ^ (ceilLog2 (if moeSet then y.LamM else y.Lam) + ceilLog2 ny))
      (nv + (if moeSet then y.LamM else y.Lam))
      (ceilLog2 (if moeSet then y.LamM else y.Lam) + ceilLog2 ny) := by
  rw [plain_push]
  have e : (if (none : Option (ℕ → ℕ → Option Aff)).isNone = true then
      s.nextV + (if moeSet then y.LamM else y.Lam) else s.nextV) =
      nv + (if moeSet then y.LamM else y.Lam) := by
    rw [H.nv]
    rfl
  rw [e]
  exact sm_push H _ rfl

/-- **tri: a panel with the selector.** hk: if its column factor is a never-sent vector, its columns
have lfe bits. -/
theorem sm_tri {y : Lay} {s : Panels} {pl nv wD : ℕ} (H : Sm y s pl nv wD) (ec : E)
    (claim nk : ℕ) (sl : Array E) (xx : Array Aff) (virt : Option ℕ) (wt : E)
    (hk : virt.isSome = true → ceilLog2 nk = y.lfe) :
    Sm y (tri y ec claim nk sl xx virt wt s)
      (pl + 2 ^ (ceilLog2 (max y.h.NE 1) + ceilLog2 nk)) (nv + 1) wD := by
  have e : tri y ec claim nk sl xx virt wt s =
      { bl := s.bl.push { tri := true, claim := claim, ec := ec, ni := y.h.NE, ny := nk,
                          wy := ceilLog2 nk, w := ceilLog2 (max y.h.NE 1) + ceilLog2 nk, sl := sl,
                          xx := xx, virt := virt, wt := #[wt], v0 := some s.nextV },
        nextV := s.nextV + 1 } := rfl
  rw [e, H.nv]
  refine sm_push H _ ?_
  cases virt with
  | none => rfl
  | some k =>
    show (if (ceilLog2 nk != y.lfe) = true then none else some wD) = some wD
    rw [hk rfl]
    simp

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.places_push
#print axioms OnBytes.Road.K4.C.sm_empty
#print axioms OnBytes.Road.K4.C.sm_push
#print axioms OnBytes.Road.K4.C.sm_weight
#print axioms OnBytes.Road.K4.C.sm_forms
#print axioms OnBytes.Road.K4.C.sm_virt
#print axioms OnBytes.Road.K4.C.sm_tri
