-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/ReadsSame.lean: kind K5: the test under which tablesP returns
(placeOk, Johnson/Desc/First/Att/Claims/ReadsReturn.lean) reads of the points, beside its two
comparisons of coordinates, seven lengths alone. So a yes at one record gives a yes at every record
of these lengths at which the two comparisons and the lookup's planesOk say yes.

Main names:
  `LongLens p p0`: two records have equally many units; at each unit the sumcheck's challenges are
    equally many; and ziW, zcW and the challenges of the division's sumcheck, of the score at the
    index and of the key at the index are equally many.
  `tabs_all`: whether a read's tables fit the list of matrices hangs on no point and no weight.
  `lngB_congr`, `longOk_same`: the long tables' tests hang on these lengths.
  `placeOk_of_lens`: LongLens p p0 → placeOk g mats nW lk0 p0 = true → lk.planesOk = true →
    mergedPlanes g.lmS lk.zx p.planes = true → mergedTokens g lk.zx p.d = true →
    placeOk g mats nW lk p = true.
  `tablesP_of_lens`: the same from and to the return of tablesP.
Not shown: LongLens or the two comparisons at any record.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.ReadsReturn

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo LookIn Pts Read TablesP)

/-- The lengths that the long tables' tests read, and the number of units, are one. -/
structure LongLens (p p0 : Pts) : Prop where
  n : p.scores.size = p0.scores.size
  units : ∀ u, (p.unit u).sc.r.size = (p0.unit u).sc.r.size
  ziW : p.d.ziW.size = p0.d.ziW.size
  zcW : p.d.zcW.size = p0.d.zcW.size
  scE : p.d.scE.r.size = p0.d.scE.r.size
  scF : p.x.scF.r.size = p0.x.scF.r.size
  scd : p.x.scd.r.size = p0.x.scd.r.size

variable {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk lk0 : LookIn} {p p0 : Pts}

/-- Whether a read's tables fit hangs on no point and no weight. -/
theorem tabs_all (r : Read) : (tabs g lk p r).all (fitsT mats) = (tabs g lk0 p0 r).all (fitsT mats) := by
  cases r <;> simp only [tabs, List.all_map, P.Read.of, P.Matrix.parts, P.Matrix.number, P.Weights.len, fitsT,
    Function.comp_def]

theorem lngB_congr {zc zc' w w' : Array E} (h1 : zc.size = zc'.size) (h2 : w.size = w'.size) :
    lngB g zc w = lngB g zc' w' := by
  unfold lngB
  rw [h1, h2]

theorem eqTab_congr {z z' : Array E} (h : z.size = z'.size) : (P.eqTab z).size = (P.eqTab z').size := by
  rw [eqTab_size, eqTab_size, h]

theorem extract_congr {z z' : Array E} (h : z.size = z'.size) (a b : ℕ) :
    (z.extract a b).size = (z'.extract a b).size := by
  rw [Array.size_extract, Array.size_extract, h]

theorem longOk_same (H : LongLens p p0) (r : Read) : longOk g lk p r = longOk g lk0 p0 r := by
  have tk : ∀ hi lo hi' lo' : Array E, (P.tok g hi lo).size = (P.tok g hi' lo').size := fun _ _ _ _ => by
    rw [tok_size, tok_size]
  have lc : ∀ u, (P.lastCoords (p.unit u).sc.r g.ldh).size = (P.lastCoords (p0.unit u).sc.r g.ldh).size := fun u => by
    unfold P.lastCoords
    rw [Array.size_extract, Array.size_extract, H.units u]
  have rc : (p.x.rc g).size = (p0.x.rc g).size := by
    unfold P.MaxP.rc
    rw [Array.size_extract, Array.size_extract, H.scF]
  cases r with
  | outAtDivide => exact lngB_congr H.zcW (eqTab_congr H.ziW)
  | queriesAtUnit u => exact lngB_congr (lc u) (tk _ _ _ _)
  | keysAtUnit u => exact lngB_congr (lc u) (tk _ _ _ _)
  | outputsAtProduct => exact lngB_congr H.zcW (eqTab_congr (extract_congr H.scE _ _))
  | valuesAtBelow => exact lngB_congr H.zcW (tk _ _ _ _)
  | valuesAtOn => exact lngB_congr H.zcW (tk _ _ _ _)
  | queriesAtIndex => exact lngB_congr rc (eqTab_congr (extract_congr H.scF _ _))
  | keysAtIndex => exact lngB_congr rc (eqTab_congr (extract_congr H.scd _ _))
  | _ => rfl

/-- **A yes at one record gives a yes at every record of these lengths**, where the two comparisons of coordinates and the lookup's planesOk say yes. -/
theorem placeOk_of_lens (H : LongLens p p0) (h0 : placeOk g mats nW lk0 p0 = true) (hp : lk.planesOk = true)
    (m1 : P.mergedPlanes g.lmS lk.zx p.planes = true) (m2 : P.mergedTokens g lk.zx p.d = true) :
    placeOk g mats nW lk p = true := by
  unfold placeOk at h0 ⊢
  simp only [Bool.and_eq_true] at h0 ⊢
  obtain ⟨⟨⟨_, a⟩, b⟩, c⟩ := h0
  refine ⟨⟨⟨⟨⟨m1, m2⟩, hp⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [H.n]
    rw [List.all_eq_true] at a ⊢
    exact fun r hr => (tabs_all r).trans (a r hr)
  · rw [H.n]
    rw [List.all_eq_true] at b ⊢
    exact fun r hr => (longOk_same H r).trans (b r hr)
  · rw [H.n]
    exact c

/-- The same from and to the return of tablesP. -/
theorem tablesP_of_lens {t0 : TablesP} (H : LongLens p p0) (h0 : P.tablesP g mats nW lk0 p0 = some t0)
    (hp : lk.planesOk = true) (m1 : P.mergedPlanes g.lmS lk.zx p.planes = true)
    (m2 : P.mergedTokens g lk.zx p.d = true) : ∃ t, P.tablesP g mats nW lk p = some t :=
  tablesP_some (placeOk_of_lens H (by rw [← tablesP_isSome, h0]; rfl) hp m1 m2)

end K5Law
