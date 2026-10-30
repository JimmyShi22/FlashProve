-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ColsOfLayout.lean: CONDITIONAL: at a call of a layout that the verifier returns,
whose line is one of the library's eight, under its eleven switches.

What is here. The layers' own rounds (sub-protocol K4), the lookup's join: the hypothesis ColsOK
(MarksReturn.lean) at a call of a layout that the verifier returns, whose line names the families
of one of the library's calls: the verifier's columns are the library's (pos_eq_segs,
Johnson/Road/FormsKeysPos.lean), and the library's are all different and lie in the call (posInj,
pos_lt, Inst/Model/FF/IndexFacts.lean). The first half of the proof is that of the library's
padding_isPad (Johnson/Road/FormsKeysPub.lean). Statements and proofs.

  `posList_at`           a member of an array's list.
  **`colsOK_of_layout`**   ColsOK.

Not shown here. That a layout with the library's lines of calls exists: no example is shown here.
AT CALLS WHOSE LINE IS ONE OF THE LIBRARY's EIGHT, UNDER THE LIBRARY's ELEVEN SWITCHES ALONE.
Public data alone.
No property is claimed.
-/
import Johnson.Road.K4.C.MarksReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model (Seg CallD place markUsed topBit)
open OnBytes.Model.Layer (Lay layout)
open Inst.Model.FFSeg (Dim Fam len pos call fams isExp lJ)

/-- A member of an array's list. -/
theorem posList_at (a : Array ℕ) {x : ℕ} (hx : x < a.toList.length) :
    a.toList[x] = a.getD x 0 := by
  have hx' : x < a.size := by simpa using hx
  rw [Array.getD, dif_pos hx']
  simp

/-- **THE COLUMNS OF A CALL WITH ONE OF THE LIBRARY's LINES LIE IN THE CALL AND ARE ALL DIFFERENT.**
CONDITIONAL: on the layout's return, the switches, the sizes and the call's line. -/
theorem colsOK_of_layout {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) {D : Dim} (Z : Sized h D) {cd : CallD}
    (hcd : cd ∈ y.calls) {cc : Fin 8} (hn : cd.segs.map (·.name) = (fams cc).map segName) :
    ColsOK cd := by
  have A := admitted_of_layout hy S.p3
  have hseg : ∀ s ∈ cd.segs, s.n = len D (famS s) ∧ s.moe = isExp (famS s) ∧ s.pos.size = s.n := by
    intro s hs
    obtain ⟨fam, a1, a2, a3, a4, -⟩ := segs_of_layout hy S cd hcd s hs
    have e : famS s = fam := by
      unfold famS
      rw [a1, famOf_segName]
      rfl
    rw [e]
    exact ⟨a2.trans (Z.len_eq fam).symm, a3, a4⟩
  have hfam : cd.segs.map famS = fams cc := by
    have e1 : cd.segs.map famS = (cd.segs.map (·.name)).map fun n => (famOf n).getD .G := by
      rw [List.map_map]
      rfl
    rw [e1, hn, List.map_map]
    conv_rhs => rw [← List.map_id (fams cc)]
    refine List.map_congr_left fun s _ => ?_
    show (famOf (segName s)).getD .G = s
    rw [famOf_segName]
    rfl
  have hlt : ∀ s ∈ fams cc, len D s < 2 ^ (topBit + 1) := fun s _ => by
    rw [Z.len_eq s]
    exact len_lt A s
  obtain ⟨cl, taken, -, -, h3⟩ := A.calls
  rw [h3] at hcd
  obtain ⟨c0, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hcd)
  have hpos := pos_eq_segs D cc c0.1 c0.2.1 c0.2.2 _ famS hfam (fun g hg => (hseg g hg).1) hlt
  have hl := lengths_of_segs D cc c0.1 c0.2.1 c0.2.2 _ famS hfam fun g hg => (hseg g hg).1
  have hcall : ∀ s ∈ (place c0.1 c0.2.1 c0.2.2 (h.nmin - h.ll - h.lt)).segs,
      call (famS s) = cc := fun s hs =>
    Inst.Model.FFSeg.IndexFacts.mem_fams_iff.mp (hfam ▸ List.mem_map_of_mem hs)
  have hat : ∀ s ∈ (place c0.1 c0.2.1 c0.2.2 (h.nmin - h.ll - h.lt)).segs,
      ∀ x (hx : x < s.pos.toList.length), x < len D (famS s) ∧
        s.pos.toList[x] = pos D (famS s) x := by
    intro s hs x hx
    have hxl : x < len D (famS s) := by
      rw [← (hseg s hs).1, ← (hseg s hs).2.2]
      simpa using hx
    exact ⟨hxl, by rw [posList_at s.pos hx, hpos s hs x hxl]⟩
  refine ⟨rfl, fun s hs j hj => ?_, fun s hs => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hj
    obtain ⟨hxl, e⟩ := hat s hs x hx
    rw [e, place_J, lJ_max D cc c0.1 c0.2.1 c0.2.2 _ hl hlt]
    have h1 := Inst.Model.FFSeg.IndexFacts.pos_lt D hxl
    rw [hcall s hs] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  · show s.pos.toList.Pairwise (· ≠ ·)
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab e
    obtain ⟨la, ea⟩ := hat s hs a ha
    obtain ⟨lb, eb⟩ := hat s hs b hb
    rw [ea, eb] at e
    have := (Inst.Model.FFSeg.IndexFacts.posInj D _ _ a b rfl la lb e).2
    omega
  · have hnd : ((place c0.1 c0.2.1 c0.2.2 (h.nmin - h.ll - h.lt)).segs.map famS).Pairwise
        (· ≠ ·) := by
      rw [hfam]
      exact Inst.Model.FFSeg.IndexFacts.fams_nodup cc
    refine (List.pairwise_map.mp hnd).imp_of_mem fun {s s'} hs hs' hne => ?_
    intro j hj hj'
    obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hj
    obtain ⟨x', hx', e⟩ := List.getElem_of_mem hj'
    obtain ⟨la, ea⟩ := hat s hs x hx
    obtain ⟨lb, eb⟩ := hat s' hs' x' hx'
    rw [ea, eb] at e
    exact hne (Inst.Model.FFSeg.IndexFacts.posInj D _ _ x' x
      ((hcall s' hs').trans (hcall s hs).symm) lb la e).1.symm

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.posList_at
#print axioms OnBytes.Road.K4.C.colsOK_of_layout
